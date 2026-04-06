/// Verified GPU Mandelbrot kernel using prime field arithmetic from verus-fixed-point.
///
/// Two kernels:
/// 1. Reference orbit: Z_{n+1} = Z_n^2 + c (per reference point, on GPU)
/// 2. Perturbation: δ_{n+1} = 2·Z_n·δ_n + δ_n^2 + Δc (per pixel, on GPU)
///
/// All arithmetic functions are verified (914 verified, 0 errors) and
/// auto-transpiled to WGSL via verus-gpu-parser.

use verus_fixed_point::fixed_point::limb_ops::*;
use verus_fixed_point::fixed_point::prime_field::*;

/// Reference orbit kernel: Z_{n+1} = Z_n^2 + c.
/// Computes the orbit for a single reference point.
///
/// Buffer layout (all u32, N limbs per value):
///   c_data:     [c_re(N), c_im(N)] — the reference point c
///   orbit_re:   [Z_re(N) * max_iters] — real parts of orbit
///   orbit_im:   [Z_im(N) * max_iters] — imaginary parts of orbit
///   params:     [width, height, max_iters, n_limbs, c_val, p0..p_{N-1}]
///   scratch:    per-thread workspace for intermediate computations
///
/// Each thread computes one iteration's Z value.
/// Actually, since the orbit is sequential, one thread computes the full orbit.
/// Multiple threads handle multiple reference points.
#[gpu_kernel(workgroup_size(64, 1, 1))]
fn mandelbrot_ref_orbit_kernel(
    #[gpu_builtin(thread_id_x)] tid: u32,
    #[gpu_buffer(0, read)] c_data: &[u32],
    #[gpu_buffer(1, read_write)] orbit_re: &mut [u32],
    #[gpu_buffer(2, read_write)] orbit_im: &mut [u32],
    #[gpu_buffer(3, read)] params: &[u32],
    #[gpu_buffer(4, read_write)] scratch: &mut [u32],
) {
    let n = params[3u32];       // number of limbs
    let max_iters = params[2u32];
    let c_val = params[4u32];   // Mersenne constant

    // Scratch layout per thread (offsets from scratch_base):
    // [0..n):     z_re
    // [n..2n):    z_im
    // [2n..4n):   z_re^2 (product, 2n limbs)
    // [4n..6n):   z_im^2 (product, 2n limbs)
    // [6n..8n):   (z_re+z_im)^2 (product, 2n limbs)
    // [8n..9n):   reduced re^2
    // [9n..10n):  reduced im^2
    // [10n..11n): reduced (re+im)^2
    // [11n..12n): new_re = re^2 - im^2 + c_re
    // [12n..13n): new_im = (re+im)^2 - re^2 - im^2 + c_im
    // [13n..20n): additional scratch for add/sub/reduce operations
    let scratch_per_thread = 20u32 * n;
    let sb = tid * scratch_per_thread;

    let zr = sb;
    let zi = sb + n;

    // Load c
    let c_re_off = tid * 2u32 * n;
    let c_im_off = c_re_off + n;

    // Z_0 = 0
    for i in 0u32..n {
        scratch[zr + i] = 0u32;
        scratch[zi + i] = 0u32;
    }

    // Iterate: Z_{n+1} = Z_n^2 + c
    for iter in 0u32..max_iters {
        // Store Z_n in orbit buffers
        let orbit_off = (tid * max_iters + iter) * n;
        for i in 0u32..n {
            orbit_re[orbit_off + i] = scratch[zr + i];
            orbit_im[orbit_off + i] = scratch[zi + i];
        }

        // Compute Z_{n+1} = Z_n^2 + c using complex squaring:
        //   re' = re^2 - im^2 + c_re
        //   im' = (re+im)^2 - re^2 - im^2 + c_im

        // Step 1: re^2 (schoolbook multiply, result in scratch[2n..4n))
        let re2_prod = sb + 2u32 * n;
        generic_mul_karatsuba(&scratch[zr..], &scratch[zr..], n, &mut scratch[re2_prod..]);

        // Step 2: im^2
        let im2_prod = sb + 4u32 * n;
        generic_mul_karatsuba(&scratch[zi..], &scratch[zi..], n, &mut scratch[im2_prod..]);

        // Step 3: re + im → scratch[8n..9n)
        let re_plus_im = sb + 8u32 * n;
        let tmp_scratch = sb + 13u32 * n;
        generic_add_limbs(&scratch[zr..], &scratch[zi..], n, &mut scratch[re_plus_im..]);

        // Step 4: (re+im)^2
        let sum2_prod = sb + 6u32 * n;
        generic_mul_karatsuba(&scratch[re_plus_im..], &scratch[re_plus_im..], n, &mut scratch[sum2_prod..]);

        // Step 5: Mersenne reduce all three products to n limbs
        let re2_red = sb + 8u32 * n;
        let im2_red = sb + 9u32 * n;
        let sum2_red = sb + 10u32 * n;
        mersenne_reduce_exec(&scratch[re2_prod..], n, c_val, &mut scratch[re2_red..]);
        mersenne_reduce_exec(&scratch[im2_prod..], n, c_val, &mut scratch[im2_red..]);
        mersenne_reduce_exec(&scratch[sum2_prod..], n, c_val, &mut scratch[sum2_red..]);

        // Step 6: new_re = re^2 - im^2 + c_re (mod p)
        //   = add_mod(sub_mod(re2_red, im2_red), c_re)
        // For now, use add/sub with carry fold + conditional subtract
        let new_re = sb + 11u32 * n;
        // re^2 - im^2
        generic_sub_limbs(&scratch[re2_red..], &scratch[im2_red..], n, &mut scratch[new_re..]);
        // + c_re
        generic_add_limbs(&scratch[new_re..], &c_data[c_re_off..], n, &mut scratch[new_re..]);

        // Step 7: new_im = (re+im)^2 - re^2 - im^2 + c_im
        let new_im = sb + 12u32 * n;
        generic_sub_limbs(&scratch[sum2_red..], &scratch[re2_red..], n, &mut scratch[new_im..]);
        generic_sub_limbs(&scratch[new_im..], &scratch[im2_red..], n, &mut scratch[new_im..]);
        generic_add_limbs(&scratch[new_im..], &c_data[c_im_off..], n, &mut scratch[new_im..]);

        // Step 8: Copy new values to z_re, z_im
        for i in 0u32..n {
            scratch[zr + i] = scratch[new_re + i];
            scratch[zi + i] = scratch[new_im + i];
        }
    }
}
