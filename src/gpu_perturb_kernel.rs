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



/// Perturbation kernel: δ_{n+1} = 2·Z_n·δ_n + δ_n^2 + Δc.
/// Each thread handles one pixel. Reads reference orbit from orbit buffers.
///
/// Buffer layout:
///   orbit_re/im: precomputed reference orbit [Z_re/im(N) * max_iters]
///   delta_c:     per-pixel Δc [Δc_re(N), Δc_im(N)] per pixel
///   params:      [width, height, max_iters, n_limbs, c_val, p0..p_{N-1},
///                 escape_threshold(N)]
///   scratch:     per-thread workspace
///   iter_counts: output iteration count per pixel
#[gpu_kernel(workgroup_size(16, 16, 1))]
fn mandelbrot_perturb_kernel(
    #[gpu_builtin(thread_id_x)] gid_x: u32,
    #[gpu_builtin(thread_id_y)] gid_y: u32,
    #[gpu_buffer(0, read)] orbit_re: &[u32],
    #[gpu_buffer(1, read)] orbit_im: &[u32],
    #[gpu_buffer(2, read)] delta_c: &[u32],
    #[gpu_buffer(3, read)] params: &[u32],
    #[gpu_buffer(4, read_write)] scratch: &mut [u32],
    #[gpu_buffer(5, read_write)] iter_counts: &mut [u32],
) {
    let width = params[0u32];
    let max_iters = params[2u32];
    let n = params[3u32];
    let c_val = params[4u32];
    let p_off = 5u32;  // p limbs at params[5..5+N]

    let tid = gid_y * width + gid_x;

    // Scratch layout per thread:
    // [0..n):      δ_re (current perturbation real)
    // [n..2n):     δ_im (current perturbation imaginary)
    // [2n..4n):    product workspace 1 (2n limbs)
    // [4n..6n):    product workspace 2 (2n limbs)
    // [6n..8n):    product workspace 3 (2n limbs)
    // [8n..9n):    temp1 (reduced)
    // [9n..10n):   temp2 (reduced)
    // [10n..11n):  temp3 (reduced)
    // [11n..12n):  temp4
    // [12n..13n):  temp5
    // [13n..20n):  additional scratch
    let scratch_per_thread = 20u32 * n;
    let sb = tid * scratch_per_thread;

    let dr = sb;            // δ_re
    let di = sb + n;        // δ_im

    // Load Δc for this pixel
    let dc_re_off = tid * 2u32 * n;
    let dc_im_off = dc_re_off + n;

    // δ_0 = Δc (initial perturbation = offset from reference)
    for i in 0u32..n {
        scratch[dr + i] = delta_c[dc_re_off + i];
        scratch[di + i] = delta_c[dc_im_off + i];
    }

    let mut escaped_iter = max_iters;

    for iter in 0u32..max_iters {
        // Load Z_n from reference orbit
        let orbit_off = iter * n;  // single reference point, no tid offset
        // Z_re and Z_im are in orbit buffers

        // ─── Perturbation step: δ' = 2·Z·δ + δ² + Δc ───

        // Part 1: 2·Z·δ (complex multiply)
        //   (2·Z_re·δ_re - 2·Z_im·δ_im, 2·Z_re·δ_im + 2·Z_im·δ_re)
        // First compute Z·δ, then double.

        // k1 = Z_re * δ_re
        let prod1 = sb + 2u32 * n;
        generic_mul_karatsuba(&orbit_re[orbit_off..], &scratch[dr..], n, &mut scratch[prod1..]);
        let k1 = sb + 8u32 * n;
        mersenne_reduce_exec(&scratch[prod1..], n, c_val, &mut scratch[k1..]);

        // k2 = Z_im * δ_im
        let prod2 = sb + 4u32 * n;
        generic_mul_karatsuba(&orbit_im[orbit_off..], &scratch[di..], n, &mut scratch[prod2..]);
        let k2 = sb + 9u32 * n;
        mersenne_reduce_exec(&scratch[prod2..], n, c_val, &mut scratch[k2..]);

        // k3 = Z_re * δ_im
        generic_mul_karatsuba(&orbit_re[orbit_off..], &scratch[di..], n, &mut scratch[prod1..]);
        let k3 = sb + 10u32 * n;
        mersenne_reduce_exec(&scratch[prod1..], n, c_val, &mut scratch[k3..]);

        // k4 = Z_im * δ_re
        generic_mul_karatsuba(&orbit_im[orbit_off..], &scratch[dr..], n, &mut scratch[prod2..]);
        let k4 = sb + 11u32 * n;
        mersenne_reduce_exec(&scratch[prod2..], n, c_val, &mut scratch[k4..]);

        // Zδ_re = k1 - k2, Zδ_im = k3 + k4
        let zd_re = sb + 12u32 * n;
        let zd_im = sb + 13u32 * n;
        generic_sub_limbs(&scratch[k1..], &scratch[k2..], n, &mut scratch[zd_re..]);
        generic_add_limbs(&scratch[k3..], &scratch[k4..], n, &mut scratch[zd_im..]);

        // 2·Z·δ = double Zδ
        let tzd_re = sb + 8u32 * n;   // reuse temp slots
        let tzd_im = sb + 9u32 * n;
        generic_add_limbs(&scratch[zd_re..], &scratch[zd_re..], n, &mut scratch[tzd_re..]);
        generic_add_limbs(&scratch[zd_im..], &scratch[zd_im..], n, &mut scratch[tzd_im..]);

        // Part 2: δ² (complex squaring using 3 muls)
        //   re^2, im^2, (re+im)^2
        let dsq_prod = sb + 2u32 * n;
        generic_mul_karatsuba(&scratch[dr..], &scratch[dr..], n, &mut scratch[dsq_prod..]);
        let dr2 = sb + 10u32 * n;
        mersenne_reduce_exec(&scratch[dsq_prod..], n, c_val, &mut scratch[dr2..]);

        let dsq_prod2 = sb + 4u32 * n;
        generic_mul_karatsuba(&scratch[di..], &scratch[di..], n, &mut scratch[dsq_prod2..]);
        let di2 = sb + 11u32 * n;
        mersenne_reduce_exec(&scratch[dsq_prod2..], n, c_val, &mut scratch[di2..]);

        // δ_re + δ_im
        let dsum = sb + 12u32 * n;
        generic_add_limbs(&scratch[dr..], &scratch[di..], n, &mut scratch[dsum..]);
        // (δ_re + δ_im)^2
        generic_mul_karatsuba(&scratch[dsum..], &scratch[dsum..], n, &mut scratch[dsq_prod..]);
        let dsum2 = sb + 13u32 * n;
        mersenne_reduce_exec(&scratch[dsq_prod..], n, c_val, &mut scratch[dsum2..]);

        // δ²_re = dr2 - di2
        let dsq_re = sb + 12u32 * n;
        generic_sub_limbs(&scratch[dr2..], &scratch[di2..], n, &mut scratch[dsq_re..]);

        // δ²_im = dsum2 - dr2 - di2
        let dsq_im = sb + 13u32 * n;
        generic_sub_limbs(&scratch[dsum2..], &scratch[dr2..], n, &mut scratch[dsq_im..]);
        generic_sub_limbs(&scratch[dsq_im..], &scratch[di2..], n, &mut scratch[dsq_im..]);

        // Part 3: δ' = 2·Z·δ + δ² + Δc
        // new_dr = tzd_re + dsq_re + Δc_re
        let new_dr = sb + 10u32 * n;
        generic_add_limbs(&scratch[tzd_re..], &scratch[dsq_re..], n, &mut scratch[new_dr..]);
        generic_add_limbs(&scratch[new_dr..], &delta_c[dc_re_off..], n, &mut scratch[new_dr..]);

        // new_di = tzd_im + dsq_im + Δc_im
        let new_di = sb + 11u32 * n;
        generic_add_limbs(&scratch[tzd_im..], &scratch[dsq_im..], n, &mut scratch[new_di..]);
        generic_add_limbs(&scratch[new_di..], &delta_c[dc_im_off..], n, &mut scratch[new_di..]);

        // Update δ
        for i in 0u32..n {
            scratch[dr + i] = scratch[new_dr + i];
            scratch[di + i] = scratch[new_di + i];
        }

        // ─── Escape detection: |Z + δ|² > threshold ───
        // Compute Z_re + δ_re and Z_im + δ_im
        let full_re = sb + 8u32 * n;
        let full_im = sb + 9u32 * n;
        generic_add_limbs(&orbit_re[orbit_off..], &scratch[dr..], n, &mut scratch[full_re..]);
        generic_add_limbs(&orbit_im[orbit_off..], &scratch[di..], n, &mut scratch[full_im..]);

        // |Z+δ|² = full_re² + full_im²
        generic_mul_karatsuba(&scratch[full_re..], &scratch[full_re..], n, &mut scratch[dsq_prod..]);
        let mag_re2 = sb + 10u32 * n;
        mersenne_reduce_exec(&scratch[dsq_prod..], n, c_val, &mut scratch[mag_re2..]);

        generic_mul_karatsuba(&scratch[full_im..], &scratch[full_im..], n, &mut scratch[dsq_prod2..]);
        let mag_im2 = sb + 11u32 * n;
        mersenne_reduce_exec(&scratch[dsq_prod2..], n, c_val, &mut scratch[mag_im2..]);

        let mag2 = sb + 12u32 * n;
        generic_add_limbs(&scratch[mag_re2..], &scratch[mag_im2..], n, &mut scratch[mag2..]);

        // Escape check: compare magnitude against threshold.
        // In prime field representation, values > p/2 are "negative" (centered view).
        // |Z+δ|² is always non-negative, so it's in [0, p/2].
        // Escape when |Z+δ|² > escape_threshold (e.g., field encoding of 4).
        // Simple check: subtract threshold, if no borrow then magnitude >= threshold.
        let escape_off = p_off + n;  // escape threshold limbs after p limbs in params
        let diff_off = sb + 13u32 * n;
        let borrow = generic_sub_limbs(&scratch[mag2..], &params[escape_off..], n, &mut scratch[diff_off..]);
        // borrow == 0 means mag2 >= threshold → escaped
        if borrow == 0u32 {
            if escaped_iter == max_iters {
                escaped_iter = iter;
            }
        }
    }

    iter_counts[tid] = escaped_iter;
}
