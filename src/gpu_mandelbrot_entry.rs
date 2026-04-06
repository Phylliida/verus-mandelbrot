/// GPU Mandelbrot kernel using output-parameter functions (no Vec::new).
/// All operations write to caller-provided buffers.
/// Uses add_limbs_to, sub_limbs_to, mul_schoolbook_to, slice_vec_to
/// from verus-fixed-point (940 verified, 0 errors).

use verus_fixed_point::fixed_point::limb_ops::*;

#[gpu_kernel(workgroup_size(16, 16, 1))]
fn mandelbrot_fixedpoint(
    #[gpu_builtin(thread_id_x)] gid_x: u32,
    #[gpu_builtin(thread_id_y)] gid_y: u32,
    #[gpu_buffer(0, read)] c_data: &[u32],
    #[gpu_buffer(1, read_write)] scratch: &mut [u32],
    #[gpu_buffer(2, read_write)] iter_counts: &mut [u32],
    #[gpu_buffer(3, read)] params: &[u32],
) {
    let width = params[0u32];
    let height = params[1u32];
    let max_iters = params[2u32];
    let n = params[3u32];
    let frac_limbs = params[4u32];

    if gid_x >= width { return; }
    if gid_y >= height { return; }
    let tid = gid_y * width + gid_x;

    // Scratch layout per thread (all regions are n limbs unless noted):
    //   [0]:   z_re        (n)
    //   [1]:   z_im        (n)
    //   [2]:   prod        (2n)  — multiply product
    //   [4]:   re2         (n)   — re^2 reduced
    //   [5]:   im2         (n)   — im^2 reduced
    //   [6]:   sum2        (n)   — (re+im)^2 reduced
    //   [7]:   re_plus_im  (n)   — re + im
    //   [8]:   tmp         (n)   — temp for sub/add results
    //   [9]:   new_re      (n)
    //   [10]:  new_im      (n)
    // Total: 12n words per thread (slot 2 is 2n, rest are n)
    let words_per_thread = 12u32 * n;
    let sb = tid * words_per_thread;
    let s0 = sb;                    // z_re
    let s1 = sb + n;                // z_im
    let s2 = sb + 2u32 * n;         // prod (2n)
    let s4 = sb + 4u32 * n;         // re2
    let s5 = sb + 5u32 * n;         // im2
    let s6 = sb + 6u32 * n;         // sum2
    let s7 = sb + 7u32 * n;         // re_plus_im
    let s8 = sb + 8u32 * n;         // tmp
    let s9 = sb + 9u32 * n;         // new_re
    let s10 = sb + 10u32 * n;       // new_im

    // c layout: [c_re(n), c_im(n)] per pixel
    let c_re = tid * 2u32 * n;
    let c_im = c_re + n;

    // Z_0 = 0
    for i in 0u32..n {
        scratch[s0 + i] = 0u32;
        scratch[s1 + i] = 0u32;
    }

    let mut escaped_iter = max_iters;

    for iter in 0u32..max_iters {
        // ── Complex squaring: Z^2 = (re^2 - im^2, (re+im)^2 - re^2 - im^2) ──

        // re^2: mul_schoolbook_to(z_re, z_re) → prod[0..2n], then slice → re2
        mul_schoolbook_to(&scratch[s0..], &scratch[s0..], &mut scratch[s2..], n);
        slice_vec_to(&scratch[s2..], frac_limbs, frac_limbs + n, &mut scratch[s4..], 0);

        // im^2: mul_schoolbook_to(z_im, z_im) → prod, then slice → im2
        mul_schoolbook_to(&scratch[s1..], &scratch[s1..], &mut scratch[s2..], n);
        slice_vec_to(&scratch[s2..], frac_limbs, frac_limbs + n, &mut scratch[s5..], 0);

        // re + im → re_plus_im
        add_limbs_to(&scratch[s0..], &scratch[s1..], &mut scratch[s7..], n);

        // (re+im)^2: mul → prod, slice → sum2
        mul_schoolbook_to(&scratch[s7..], &scratch[s7..], &mut scratch[s2..], n);
        slice_vec_to(&scratch[s2..], frac_limbs, frac_limbs + n, &mut scratch[s6..], 0);

        // new_re = re^2 - im^2 + c_re
        sub_limbs_to(&scratch[s4..], &scratch[s5..], &mut scratch[s9..], n);
        add_limbs_to(&scratch[s9..], &c_data[c_re..], &mut scratch[s9..], n);

        // new_im = (re+im)^2 - re^2 - im^2 + c_im
        sub_limbs_to(&scratch[s6..], &scratch[s4..], &mut scratch[s10..], n);
        sub_limbs_to(&scratch[s10..], &scratch[s5..], &mut scratch[s10..], n);
        add_limbs_to(&scratch[s10..], &c_data[c_im..], &mut scratch[s10..], n);

        // Copy new values to z_re, z_im
        for i in 0u32..n {
            scratch[s0 + i] = scratch[s9 + i];
            scratch[s1 + i] = scratch[s10 + i];
        }

        // ── Escape check: |Z|^2 > 4 ──
        // Re-use re2, im2 slots for magnitude
        mul_schoolbook_to(&scratch[s0..], &scratch[s0..], &mut scratch[s2..], n);
        slice_vec_to(&scratch[s2..], frac_limbs, frac_limbs + n, &mut scratch[s4..], 0);
        mul_schoolbook_to(&scratch[s1..], &scratch[s1..], &mut scratch[s2..], n);
        slice_vec_to(&scratch[s2..], frac_limbs, frac_limbs + n, &mut scratch[s5..], 0);
        add_limbs_to(&scratch[s4..], &scratch[s5..], &mut scratch[s8..], n);

        // Compare magnitude against threshold (params[5..5+n])
        let thresh_off = 5u32;
        let borrow = sub_limbs_to(&scratch[s8..], &params[thresh_off..], &mut scratch[s9..], n);
        // borrow == 0 → |Z|^2 >= threshold → escaped
        if borrow == 0u32 {
            if escaped_iter == max_iters {
                escaped_iter = iter;
            }
        }
    }

    iter_counts[tid] = escaped_iter;
}
