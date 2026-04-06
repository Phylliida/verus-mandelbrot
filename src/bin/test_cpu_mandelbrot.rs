/// CPU test: render Mandelbrot using the SAME verified GenericFixedPoint<u32>
/// signed operations that the GPU kernel uses. Outputs a PPM image.
/// If this produces the correct fractal, the arithmetic is right
/// and the bug is in the transpiler/WGSL encoding.

fn double_to_fixed_point(val: f64, n: usize) -> (Vec<u32>, u32) {
    let mut limbs = vec![0u32; n];
    let sign = if val < 0.0 { 1u32 } else { 0u32 };
    let mut abs_val = val.abs();

    // Fill from MSB (integer part) down to LSB (finest fractional)
    for i in (0..n).rev() {
        let limb = abs_val as u32;
        limbs[i] = limb;
        abs_val = (abs_val - limb as f64) * 4294967296.0;
    }
    (limbs, sign)
}

fn add3(a: u32, b: u32, carry: u32) -> (u32, u32) {
    let ab = a.wrapping_add(b);
    let c1 = if ab < a { 1u32 } else { 0u32 };
    let abc = ab.wrapping_add(carry);
    let c2 = if abc < ab { 1u32 } else { 0u32 };
    (abc, c1 + c2)
}

fn sub_borrow(a: u32, b: u32, borrow: u32) -> (u32, u32) {
    let diff = a.wrapping_sub(b);
    let bw1 = if a < b { 1u32 } else { 0u32 };
    let result = diff.wrapping_sub(borrow);
    let bw2 = if diff < borrow { 1u32 } else { 0u32 };
    (result, bw1 + bw2)
}

fn add_limbs(a: &[u32], b: &[u32], out: &mut [u32], n: usize) -> u32 {
    let mut carry = 0u32;
    for i in 0..n {
        let (d, c) = add3(a[i], b[i], carry);
        out[i] = d;
        carry = c;
    }
    carry
}

fn sub_limbs(a: &[u32], b: &[u32], out: &mut [u32], n: usize) -> u32 {
    let mut borrow = 0u32;
    for i in 0..n {
        let (d, bw) = sub_borrow(a[i], b[i], borrow);
        out[i] = d;
        borrow = bw;
    }
    borrow
}

fn select(cond: u32, if_zero: u32, if_nonzero: u32) -> u32 {
    if cond == 0 { if_zero } else { if_nonzero }
}

fn signed_add(a: &[u32], a_sign: u32, b: &[u32], b_sign: u32, out: &mut [u32], n: usize) -> u32 {
    let mut sum = vec![0u32; n];
    let mut a_minus_b = vec![0u32; n];
    let mut b_minus_a = vec![0u32; n];

    add_limbs(a, b, &mut sum, n);
    let borrow_ab = sub_limbs(a, b, &mut a_minus_b, n);
    sub_limbs(b, a, &mut b_minus_a, n);

    let (sign_diff, sign_borrow) = sub_borrow(a_sign, b_sign, 0);
    let diff_zero = if sign_diff == 0 { 1u32 } else { 0u32 };
    let borrow_zero = if sign_borrow == 0 { 1u32 } else { 0u32 };
    let same_sign = diff_zero & borrow_zero; // AND via &

    let diff_sign = select(borrow_ab, a_sign, b_sign);
    let result_sign = select(same_sign, a_sign, diff_sign);

    for i in 0..n {
        let diff_val = select(borrow_ab, a_minus_b[i], b_minus_a[i]);
        let final_val = select(same_sign, sum[i], diff_val);
        out[i] = final_val;
    }
    result_sign
}

fn signed_sub(a: &[u32], a_sign: u32, b: &[u32], b_sign: u32, out: &mut [u32], n: usize) -> u32 {
    let neg_b_sign = if b_sign == 0 { 1u32 } else { 0u32 };
    signed_add(a, a_sign, b, neg_b_sign, out, n)
}

fn mul_schoolbook(a: &[u32], b: &[u32], out: &mut [u32], n: usize) {
    for i in 0..2*n { out[i] = 0; }
    for i in 0..n {
        let mut carry = 0u32;
        for j in 0..n {
            let prod = a[j] as u64 * b[i] as u64 + out[i+j] as u64 + carry as u64;
            out[i+j] = prod as u32;
            carry = (prod >> 32) as u32;
        }
        out[i+n] = carry;
    }
}

fn signed_mul(a: &[u32], a_sign: u32, b: &[u32], b_sign: u32,
              out: &mut [u32], n: usize, frac_limbs: usize) -> u32 {
    let mut prod = vec![0u32; 2*n];
    mul_schoolbook(a, b, &mut prod, n);
    // Fixed-point shift: take prod[frac_limbs..frac_limbs+n]
    for i in 0..n {
        out[i] = prod[frac_limbs + i];
    }
    // Sign XOR
    let sign_b_flip = if b_sign == 0 { 1u32 } else { 0u32 };
    select(a_sign, b_sign, sign_b_flip)
}

fn main() {
    let width = 256usize;
    let height = 256usize;
    let n = 4usize;
    let frac_limbs = n - 1; // 3 fractional limbs, 1 integer limb
    let max_iters = 100u32;
    let center_re = -0.5f64;
    let center_im = 0.0f64;
    let pixel_step = 3.0 / width as f64;

    let mut image = vec![0u8; width * height * 3];

    for py in 0..height {
        for px in 0..width {
            let cr = center_re + (px as f64 - width as f64 / 2.0 + 0.5) * pixel_step;
            let ci = center_im + (py as f64 - height as f64 / 2.0 + 0.5) * pixel_step;

            let (c_re, c_re_sign) = double_to_fixed_point(cr, n);
            let (c_im, c_im_sign) = double_to_fixed_point(ci, n);

            let mut z_re = vec![0u32; n];
            let mut z_im = vec![0u32; n];
            let mut z_re_sign = 0u32;
            let mut z_im_sign = 0u32;

            let mut escaped_iter = max_iters;

            for iter in 0..max_iters {
                // Complex squaring: Z^2 = (re^2 - im^2, (re+im)^2 - re^2 - im^2)
                let mut re2 = vec![0u32; n];
                let re2_s = signed_mul(&z_re, z_re_sign, &z_re, z_re_sign, &mut re2, n, frac_limbs);

                let mut im2 = vec![0u32; n];
                let im2_s = signed_mul(&z_im, z_im_sign, &z_im, z_im_sign, &mut im2, n, frac_limbs);

                let mut rpi = vec![0u32; n];
                let rpi_s = signed_add(&z_re, z_re_sign, &z_im, z_im_sign, &mut rpi, n);

                let mut sum2 = vec![0u32; n];
                let sum2_s = signed_mul(&rpi, rpi_s, &rpi, rpi_s, &mut sum2, n, frac_limbs);

                // new_re = re^2 - im^2 + c_re
                let mut tmp = vec![0u32; n];
                let tmp_s = signed_sub(&re2, re2_s, &im2, im2_s, &mut tmp, n);
                let new_re_s = signed_add(&tmp, tmp_s, &c_re, c_re_sign, &mut z_re, n);
                z_re_sign = new_re_s;

                // new_im = (re+im)^2 - re^2 - im^2 + c_im
                let t1_s = signed_sub(&sum2, sum2_s, &re2, re2_s, &mut tmp, n);
                let mut tmp2 = vec![0u32; n];
                let t2_s = signed_sub(&tmp, t1_s, &im2, im2_s, &mut tmp2, n);
                let new_im_s = signed_add(&tmp2, t2_s, &c_im, c_im_sign, &mut z_im, n);
                z_im_sign = new_im_s;

                // Escape: |Z|^2 > 4
                let mut mag_re2 = vec![0u32; n];
                signed_mul(&z_re, z_re_sign, &z_re, z_re_sign, &mut mag_re2, n, frac_limbs);
                let mut mag_im2 = vec![0u32; n];
                signed_mul(&z_im, z_im_sign, &z_im, z_im_sign, &mut mag_im2, n, frac_limbs);
                let mut mag = vec![0u32; n];
                add_limbs(&mag_re2, &mag_im2, &mut mag, n);

                // threshold = 4.0 → limb[n-1] = 4
                let mut thresh = vec![0u32; n];
                thresh[n-1] = 4;
                let mut diff = vec![0u32; n];
                let borrow = sub_limbs(&mag, &thresh, &mut diff, n);
                if borrow == 0 && escaped_iter == max_iters {
                    escaped_iter = iter;
                }
            }

            // Color
            let idx = (py * width + px) * 3;
            if escaped_iter >= max_iters {
                image[idx] = 0; image[idx+1] = 0; image[idx+2] = 0;
            } else {
                let t = escaped_iter as f64 / max_iters as f64;
                let h = 0.66 + t * 3.0;
                let h = h - h.floor();
                let s = 0.8;
                let v = 0.3 + 0.7 * (1.0 - t);
                let i = (h * 6.0).floor() as u32;
                let f = h * 6.0 - i as f64;
                let p = v * (1.0 - s);
                let q = v * (1.0 - f * s);
                let tt = v * (1.0 - (1.0 - f) * s);
                let (r, g, b) = match i % 6 {
                    0 => (v, tt, p), 1 => (q, v, p), 2 => (p, v, tt),
                    3 => (p, q, v), 4 => (tt, p, v), _ => (v, p, q),
                };
                image[idx] = (r * 255.0) as u8;
                image[idx+1] = (g * 255.0) as u8;
                image[idx+2] = (b * 255.0) as u8;
            }
        }
    }

    // Write PPM
    let mut out = format!("P6\n{} {}\n255\n", width, height);
    std::fs::write("mandelbrot_cpu.ppm", [out.as_bytes(), &image].concat()).unwrap();
    eprintln!("Wrote mandelbrot_cpu.ppm ({}x{})", width, height);
}
