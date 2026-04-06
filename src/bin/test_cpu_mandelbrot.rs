// Direct import — avoid verus-mandelbrot's verus-rational dependency
use verus_fixed_point::runtime_fixed_point::GenericFixedPoint;
use verus_fixed_point::fixed_point::limb_ops::{generic_add_limbs, generic_sub_limbs};

fn double_to_fp(val: f64, n: usize, frac: usize) -> GenericFixedPoint<u32> {
    let mut limbs = vec![0u32; n];
    let sign = if val < 0.0 { 1u32 } else { 0u32 };
    let mut abs_val = val.abs();
    for i in (0..n).rev() {
        let limb = abs_val as u32;
        limbs[i] = limb;
        abs_val = (abs_val - limb as f64) * 4294967296.0;
    }
    GenericFixedPoint { limbs, sign, n_exec: n, frac_exec: frac }
}

fn main() {
    let width = 32usize;
    let height = 32usize;
    let n = 4usize;
    let frac = (n - 1) * 32;
    let max_iters = 100u32;

    let mut image = vec![0u8; width * height * 3];

    for py in 0..height {
        for px in 0..width {
            let cr = -0.5 + (px as f64 - width as f64 / 2.0 + 0.5) * 3.0 / width as f64;
            let ci = 0.0 + (py as f64 - height as f64 / 2.0 + 0.5) * 3.0 / width as f64;

            let c_re = double_to_fp(cr, n, frac);
            let c_im = double_to_fp(ci, n, frac);

            let mut z_re = GenericFixedPoint::zero(n, frac);
            let mut z_im = GenericFixedPoint::zero(n, frac);

            let mut escaped_iter = max_iters;

            for iter in 0..max_iters {
                // Z^2 + c using signed ops
                let re2 = z_re.signed_mul(&z_re);
                let im2 = z_im.signed_mul(&z_im);
                let rpi = z_re.signed_add(&z_im);
                let sum2 = rpi.signed_mul(&rpi);

                let new_re = re2.signed_sub(&im2).signed_add(&c_re);
                let t = sum2.signed_sub(&re2);
                let new_im = t.signed_sub(&im2).signed_add(&c_im);

                z_re = new_re;
                z_im = new_im;

                // Escape: |z|^2 > 4
                let mag_re2 = z_re.signed_mul(&z_re);
                let mag_im2 = z_im.signed_mul(&z_im);
                // Both squares are positive, use unsigned add
                let (mag_limbs, _carry) = generic_add_limbs(&mag_re2.limbs, &mag_im2.limbs, n);

                let mut thresh = vec![0u32; n];
                thresh[n - 1] = 4;
                let (_, borrow) = generic_sub_limbs(&mag_limbs, &thresh, n);
                if borrow == 0u32 && escaped_iter == max_iters {
                    escaped_iter = iter;
                }
            }

            let idx = (py * width + px) * 3;
            if escaped_iter >= max_iters {
                image[idx] = 0; image[idx+1] = 0; image[idx+2] = 0;
            } else {
                let t = (escaped_iter as f64 / max_iters as f64 * 255.0) as u8;
                image[idx] = t;
                image[idx+1] = t / 3;
                image[idx+2] = 255 - t / 2;
            }
        }
        if py % 32 == 0 { eprintln!("Row {}/{}", py, height); }
    }

    std::fs::write("mandelbrot_cpu.ppm",
        [format!("P6\n{} {}\n255\n", width, height).as_bytes(), &image].concat()
    ).unwrap();
    eprintln!("Wrote mandelbrot_cpu.ppm");
    eprintln!("");
    test_point();
}

// Debug: check c = (-0.5, 0) which should be in the set
fn test_point() {
    let n = 4;
    let frac = (n-1) * 32;
    let c_re = double_to_fp(-0.5, n, frac);
    let c_im = double_to_fp(0.0, n, frac);
    eprintln!("c_re: limbs={:08x?} sign={}", c_re.limbs, c_re.sign);
    let mut z_re = GenericFixedPoint::zero(n, frac);
    let mut z_im = GenericFixedPoint::zero(n, frac);

    for iter in 0..10 {
        let re2 = z_re.signed_mul(&z_re);
        let im2 = z_im.signed_mul(&z_im);
        let rpi = z_re.signed_add(&z_im);
        let sum2 = rpi.signed_mul(&rpi);
        let new_re = re2.signed_sub(&im2).signed_add(&c_re);
        let t = sum2.signed_sub(&re2);
        let new_im = t.signed_sub(&im2).signed_add(&c_im);
        z_re = new_re;
        z_im = new_im;
        eprintln!("iter {}: z_re limbs={:?} sign={}, z_im limbs={:?} sign={}",
            iter, z_re.limbs, z_re.sign, z_im.limbs, z_im.sign);
    }
}
