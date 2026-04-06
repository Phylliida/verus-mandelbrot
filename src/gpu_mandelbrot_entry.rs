/// GPU kernel entry point for transpilation to WGSL.
/// Calls verified fixed-point operations from verus-fixed-point.
/// This file is parsed by verus-gpu-parser, NOT compiled by Verus.

use verus_fixed_point::runtime_fixed_point::*;
use verus_fixed_point::fixed_point::limb_ops::*;

/// Fixed-point multiply: Karatsuba n×n → 2n limbs, take middle n (shift right by frac_limbs).
/// Uses generic_mul_karatsuba (recursive, transpiler unrolls to depth variants).
/// At depth 0, self-calls are replaced with generic_mul_schoolbook (base case).
fn fp_mul(a_limbs: &Vec<u32>, a_sign: u32,
          b_limbs: &Vec<u32>, b_sign: u32,
          n: usize, frac_limbs: usize) -> (Vec<u32>, u32)
{
    // Karatsuba multiply (transpiler unrolls recursion, uses schoolbook at depth 0
    // via #[gpu_base_case(generic_mul_schoolbook)] annotation)
    let (product, _gc) = generic_mul_karatsuba(a_limbs, b_limbs, n);
    let truncated = generic_slice_vec(&product, frac_limbs, frac_limbs + n);
    // Sign XOR
    let sign_b_flip = select_limb(&b_sign, 1u32, 0u32);
    let result_sign = select_limb(&a_sign, b_sign, sign_b_flip);
    (truncated, result_sign)
}

/// Signed add of two sign-magnitude values.
fn fp_signed_add(a_limbs: &Vec<u32>, a_sign: u32,
                 b_limbs: &Vec<u32>, b_sign: u32,
                 n: usize) -> (Vec<u32>, u32)
{
    let (sum, _carry) = generic_add_limbs(a_limbs, b_limbs, n);
    let (a_minus_b, borrow_ab) = generic_sub_limbs(a_limbs, b_limbs, n);
    let (b_minus_a, _borrow_ba) = generic_sub_limbs(b_limbs, a_limbs, n);

    // same_sign indicator
    let (sign_diff, sign_borrow) = a_sign.sub_borrow(&b_sign, &0u32);
    let diff_zero = sign_diff.is_zero_limb();
    let borrow_zero = sign_borrow.is_zero_limb();
    let (same_sign, _) = diff_zero.mul2(&borrow_zero);

    // diff_sign result
    let diff_result = generic_select_vec(&borrow_ab, &a_minus_b, &b_minus_a, n);
    let diff_sign = select_limb(&borrow_ab, a_sign, b_sign);

    // final select
    let result_limbs = generic_select_vec(&same_sign, &sum, &diff_result, n);
    let result_sign = select_limb(&same_sign, a_sign, diff_sign);

    (result_limbs, result_sign)
}

/// Signed sub = add with negated sign.
fn fp_signed_sub(a_limbs: &Vec<u32>, a_sign: u32,
                 b_limbs: &Vec<u32>, b_sign: u32,
                 n: usize) -> (Vec<u32>, u32)
{
    let neg_b_sign = select_limb(&b_sign, 1u32, 0u32);
    fp_signed_add(a_limbs, a_sign, b_limbs, neg_b_sign, n)
}

/// Magnitude squared: re^2 + im^2 (always positive).
fn fp_mag_squared(re_limbs: &Vec<u32>, re_sign: u32,
                  im_limbs: &Vec<u32>, im_sign: u32,
                  n: usize, frac_limbs: usize) -> (Vec<u32>, u32)
{
    let (re2, _re2_sign) = fp_mul(re_limbs, re_sign, re_limbs, re_sign, n, frac_limbs);
    let (im2, _im2_sign) = fp_mul(im_limbs, im_sign, im_limbs, im_sign, n, frac_limbs);
    // re^2 and im^2 are both positive (sign XOR of same values = 0)
    let (mag, _carry) = generic_add_limbs(&re2, &im2, n);
    (mag, 0u32)
}

#[gpu_kernel(workgroup_size(16, 16, 1))]
fn mandelbrot_fixedpoint(
    #[gpu_builtin(thread_id_x)] gid_x: u32,
    #[gpu_builtin(thread_id_y)] gid_y: u32,
    #[gpu_buffer(0, read)] c_data: &[u32],       // per-pixel c: [re_limbs(n), re_sign, im_limbs(n), im_sign] per pixel
    #[gpu_buffer(1, read_write)] scratch: &mut [u32],
    #[gpu_buffer(2, read_write)] iter_counts: &mut [u32],
    #[gpu_buffer(3, read)] params: &[u32],        // [width, height, max_iters, n_limbs, frac_limbs, thresh_limbs...]
) {
    let width = params[0u32];
    let height = params[1u32];
    let max_iters = params[2u32];
    let n = params[3u32];
    let frac_limbs = params[4u32];

    if gid_x >= width { return; }
    if gid_y >= height { return; }
    let tid = gid_y * width + gid_x;

    // Per-pixel c value from c_data buffer
    // Layout: [re_limbs(n), re_sign(1), im_limbs(n), im_sign(1)] per pixel
    let stride = 2u32 * n + 2u32;
    let c_base = tid * stride;

    // Scratch layout per thread:
    // [0..n): z_re limbs, [n): z_re_sign
    // [n+1..2n+1): z_im limbs, [2n+1): z_im_sign
    // [2n+2..4n+2): product tmp (2n limbs)
    // [4n+2..5n+2): temp1
    // [5n+2..6n+2): temp2
    // [6n+2..7n+2): temp3
    let words_per_thread = 7u32 * n + 3u32;
    let sb = tid * words_per_thread;

    let zr_off = sb;
    let zr_sign_off = sb + n;
    let zi_off = sb + n + 1u32;
    let zi_sign_off = sb + 2u32 * n + 1u32;

    // Z_0 = 0 (positive zero)
    for i in 0u32..n {
        scratch[zr_off + i] = 0u32;
        scratch[zi_off + i] = 0u32;
    }
    scratch[zr_sign_off] = 0u32;
    scratch[zi_sign_off] = 0u32;

    let mut escaped_iter = max_iters;

    for iter in 0u32..max_iters {
        // Z_{n+1} = Z_n^2 + c
        // Complex squaring: (re^2 - im^2, (re+im)^2 - re^2 - im^2)

        // re^2
        let (re2, re2_sign) = fp_mul(
            &scratch[zr_off..], scratch[zr_sign_off],
            &scratch[zr_off..], scratch[zr_sign_off],
            n, frac_limbs);

        // im^2
        let (im2, im2_sign) = fp_mul(
            &scratch[zi_off..], scratch[zi_sign_off],
            &scratch[zi_off..], scratch[zi_sign_off],
            n, frac_limbs);

        // re + im
        let (re_plus_im, rpi_sign) = fp_signed_add(
            &scratch[zr_off..], scratch[zr_sign_off],
            &scratch[zi_off..], scratch[zi_sign_off],
            n);

        // (re+im)^2
        let (sum2, sum2_sign) = fp_mul(&re_plus_im, rpi_sign, &re_plus_im, rpi_sign, n, frac_limbs);

        // new_re = re^2 - im^2 + c_re
        let (re_diff, re_diff_sign) = fp_signed_sub(&re2, re2_sign, &im2, im2_sign, n);
        let (new_re, new_re_sign) = fp_signed_add(
            &re_diff, re_diff_sign,
            &c_data[c_base..], c_data[c_base + n],
            n);

        // new_im = (re+im)^2 - re^2 - im^2 + c_im
        let (t1, t1_sign) = fp_signed_sub(&sum2, sum2_sign, &re2, re2_sign, n);
        let (t2, t2_sign) = fp_signed_sub(&t1, t1_sign, &im2, im2_sign, n);
        let c_im_base = c_base + n + 1u32;
        let (new_im, new_im_sign) = fp_signed_add(
            &t2, t2_sign,
            &c_data[c_im_base..], c_data[c_im_base + n],
            n);

        // Store new Z
        for i in 0u32..n {
            scratch[zr_off + i] = new_re[i];
            scratch[zi_off + i] = new_im[i];
        }
        scratch[zr_sign_off] = new_re_sign;
        scratch[zi_sign_off] = new_im_sign;

        // Escape check: |Z|^2 > 4
        let (mag, _mag_sign) = fp_mag_squared(
            &new_re, new_re_sign, &new_im, new_im_sign, n, frac_limbs);
        // Compare: mag > threshold (threshold at params[5..5+n])
        let thresh_off = 5u32;
        let (_diff, borrow) = generic_sub_limbs(&mag, &params[thresh_off..], n);
        // Wait, params is not &Vec but we need sub_limbs on it...
        // Actually the transpiler handles buffer slice args.
        // borrow == 0 → mag >= threshold → escaped
        if borrow == 0u32 {
            if escaped_iter == max_iters {
                escaped_iter = iter;
            }
        }
    }

    iter_counts[tid] = escaped_iter;
}
