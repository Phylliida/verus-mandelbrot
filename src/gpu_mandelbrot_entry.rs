/// GPU Mandelbrot kernel with proper signed fixed-point arithmetic.
/// Uses verified signed_add_to, signed_sub_to, signed_mul_to from verus-fixed-point.
/// 944 verified, 0 errors.

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

    // Scratch layout per thread (each slot is n limbs unless noted):
    //   [0]:  z_re         (n)
    //   [1]:  z_re_sign    (1)   — at offset n
    //   [2]:  z_im         (n)   — at offset n+1
    //   [3]:  z_im_sign    (1)   — at offset 2n+1
    //   [4]:  prod         (2n)  — at offset 2n+2
    //   [6]:  re2          (n)   — at offset 4n+2
    //   [7]:  re2_sign     (1)
    //   [8]:  im2          (n)
    //   [9]:  im2_sign     (1)
    //   [10]: sum2         (n)
    //   [11]: sum2_sign    (1)
    //   [12]: rpi          (n)   — re+im
    //   [13]: rpi_sign     (1)
    //   [14]: tmp          (n)
    //   [15]: tmp_sign     (1)
    //   [16]: tmp2         (n)
    //   [17]: tmp2_sign    (1)
    //   [18]: stmp1        (n)   — scratch for signed_add_to
    //   [19]: stmp2        (n)   — scratch for signed_add_to
    // Total: ~16n + 8 per thread
    let spt = 16u32 * n + 8u32;
    let sb = tid * spt;

    let zr       = sb;
    let zr_sign  = sb + n;
    let zi       = sb + n + 1u32;
    let zi_sign  = sb + 2u32 * n + 1u32;
    let prod     = sb + 2u32 * n + 2u32;
    let re2      = sb + 4u32 * n + 2u32;
    let re2_sign = re2 + n;
    let im2      = re2_sign + 1u32;
    let im2_sign = im2 + n;
    let sum2     = im2_sign + 1u32;
    let sum2_sign = sum2 + n;
    let rpi      = sum2_sign + 1u32;
    let rpi_sign = rpi + n;
    let tmp      = rpi_sign + 1u32;
    let tmp_sign = tmp + n;
    let tmp2     = tmp_sign + 1u32;
    let tmp2_sign = tmp2 + n;
    let stmp1    = tmp2_sign + 1u32;
    let stmp2    = stmp1 + n;

    // c layout per pixel: [c_re(n), c_re_sign(1), c_im(n), c_im_sign(1)]
    let c_stride = 2u32 * n + 2u32;
    let c_re      = tid * c_stride;
    let c_re_sign = c_re + n;
    let c_im      = c_re_sign + 1u32;
    let c_im_sign = c_im + n;

    // Z_0 = 0 (positive zero)
    for i in 0u32..n {
        scratch[zr + i] = 0u32;
        scratch[zi + i] = 0u32;
    }
    scratch[zr_sign] = 0u32;
    scratch[zi_sign] = 0u32;

    let mut escaped_iter = max_iters;

    for iter in 0u32..max_iters {
        // ── Complex squaring Z^2 using 3 signed multiplies ──
        // re^2 = signed_mul(z_re, z_re)
        let re2_s = signed_mul_to(
            &scratch[zr..], &scratch[zr_sign],
            &scratch[zr..], &scratch[zr_sign],
            &mut scratch[re2..], &mut scratch[prod..], n, frac_limbs);
        scratch[re2_sign] = re2_s;

        // im^2 = signed_mul(z_im, z_im)
        let im2_s = signed_mul_to(
            &scratch[zi..], &scratch[zi_sign],
            &scratch[zi..], &scratch[zi_sign],
            &mut scratch[im2..], &mut scratch[prod..], n, frac_limbs);
        scratch[im2_sign] = im2_s;

        // re + im (signed add)
        let rpi_s = signed_add_to(
            &scratch[zr..], &scratch[zr_sign],
            &scratch[zi..], &scratch[zi_sign],
            &mut scratch[rpi..], n);
        scratch[rpi_sign] = rpi_s;

        // (re+im)^2
        let sum2_s = signed_mul_to(
            &scratch[rpi..], &scratch[rpi_sign],
            &scratch[rpi..], &scratch[rpi_sign],
            &mut scratch[sum2..], &mut scratch[prod..], n, frac_limbs);
        scratch[sum2_sign] = sum2_s;

        // new_re = re^2 - im^2 + c_re
        let tmp_s = signed_sub_to(
            &scratch[re2..], &scratch[re2_sign],
            &scratch[im2..], &scratch[im2_sign],
            &mut scratch[tmp..], n);
        scratch[tmp_sign] = tmp_s;
        let new_re_s = signed_add_to(
            &scratch[tmp..], &scratch[tmp_sign],
            &c_data[c_re..], &c_data[c_re_sign],
            &mut scratch[zr..], n);
        scratch[zr_sign] = new_re_s;

        // new_im = (re+im)^2 - re^2 - im^2 + c_im
        let t1_s = signed_sub_to(
            &scratch[sum2..], &scratch[sum2_sign],
            &scratch[re2..], &scratch[re2_sign],
            &mut scratch[tmp..], n);
        scratch[tmp_sign] = t1_s;
        let t2_s = signed_sub_to(
            &scratch[tmp..], &scratch[tmp_sign],
            &scratch[im2..], &scratch[im2_sign],
            &mut scratch[tmp2..], n);
        scratch[tmp2_sign] = t2_s;
        let new_im_s = signed_add_to(
            &scratch[tmp2..], &scratch[tmp2_sign],
            &c_data[c_im..], &c_data[c_im_sign],
            &mut scratch[zi..], n);
        scratch[zi_sign] = new_im_s;

        // ── Escape check: |Z|^2 > 4 ──
        // |Z|^2 = re^2 + im^2 (both non-negative after squaring)
        // Re-compute re^2 + im^2 using unsigned add (both magnitudes)
        let mag_re2_s = signed_mul_to(
            &scratch[zr..], &scratch[zr_sign],
            &scratch[zr..], &scratch[zr_sign],
            &mut scratch[re2..], &mut scratch[prod..], n, frac_limbs);
        let mag_im2_s = signed_mul_to(
            &scratch[zi..], &scratch[zi_sign],
            &scratch[zi..], &scratch[zi_sign],
            &mut scratch[im2..], &mut scratch[prod..], n, frac_limbs);
        // re^2 and im^2 are always positive (square of real), so unsigned add is fine
        add_limbs_to(&scratch[re2..], &scratch[im2..], &mut scratch[tmp..], n);

        // Compare against threshold at params[5..5+n]
        let thresh_off = 5u32;
        let borrow = sub_limbs_to(&scratch[tmp..], &params[thresh_off..], &mut scratch[tmp2..], n);
        // borrow == 0 → |Z|^2 >= threshold → escaped
        if borrow == 0u32 {
            if escaped_iter == max_iters {
                escaped_iter = iter;
            }
        }
    }

    iter_counts[tid] = escaped_iter;
}
