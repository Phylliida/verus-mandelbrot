#[cfg(verus_keep_ghost)]
use crate::complex_interval::ComplexInterval;
#[cfg(verus_keep_ghost)]
use crate::mandelbrot::*;
#[cfg(verus_keep_ghost)]
use verus_interval_arithmetic::Interval;
#[cfg(verus_keep_ghost)]
use verus_rational::Rational;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use crate::runtime_complex_interval::RuntimeComplexInterval;
use verus_interval_arithmetic::RuntimeInterval;
use verus_rational::RuntimeRational;

#[cfg(not(verus_keep_ghost))]
compile_error!(
    "verus-mandelbrot exposes a single verified implementation; \
     build with Verus (`cfg(verus_keep_ghost)`, e.g. `cargo verus verify`)"
);

#[cfg(verus_keep_ghost)]
verus! {

/// Result of iterating the Mandelbrot map on a pixel.
pub enum MandelbrotResult {
    /// Certainly escaped at iteration n (|z|² > 4 proved).
    Escaped(u32),
    /// Completed max_iters without escaping.
    Contained(u32),
}

/// Iterate z_{n+1} = z² + c with interval arithmetic and dyadic reduction.
/// Returns Escaped(n) if escape is proved, or Contained(max_iters) otherwise.
pub fn mandelbrot_iterate(
    c_re: &RuntimeRational,
    c_im: &RuntimeRational,
    max_iters: u32,
    precision: u32,
) -> (out: MandelbrotResult)
    requires
        c_re.wf_spec(),
        c_im.wf_spec(),
{
    let c = RuntimeComplexInterval::from_point(c_re, c_im);
    let zero = RuntimeRational::from_int(0);
    let mut z = RuntimeComplexInterval::from_point(&zero, &zero);

    let four_rat = RuntimeRational::from_int(4);
    let threshold = RuntimeInterval::from_point(&four_rat);

    let mut i: u32 = 0;
    while i < max_iters
        invariant
            z.wf_spec(),
            c.wf_spec(),
            threshold.wf_spec(),
            threshold@ == Interval::from_point_spec(Rational::from_int_spec(4)),
            0 <= i <= max_iters,
        decreases max_iters - i,
    {
        // z = z² + c
        let z_squared = z.square();
        let z_next = z_squared.add(&c);
        // Reduce to keep denominator bounded
        let z_reduced = z_next.reduce(precision);

        // Check escape
        let mag2 = z_reduced.magnitude_squared();
        let escaped = threshold.certainly_lt(&mag2);
        if escaped {
            return MandelbrotResult::Escaped(i);
        }

        z = z_reduced;
        i = i + 1;
    }

    MandelbrotResult::Contained(max_iters)
}

/// Compute Mandelbrot iteration for a grid of pixels.
/// Returns a Vec of Vecs (row-major), each element is a MandelbrotResult.
pub fn mandelbrot_grid(
    re_min: &RuntimeRational,
    re_max: &RuntimeRational,
    im_min: &RuntimeRational,
    im_max: &RuntimeRational,
    width: u32,
    height: u32,
    max_iters: u32,
    precision: u32,
) -> (out: Vec<Vec<MandelbrotResult>>)
    requires
        re_min.wf_spec(),
        re_max.wf_spec(),
        im_min.wf_spec(),
        im_max.wf_spec(),
        width > 0,
        height > 0,
    ensures
        out@.len() == height as int,
{
    let mut grid: Vec<Vec<MandelbrotResult>> = Vec::new();

    // Precompute step sizes: re_step = (re_max - re_min) / width
    //                        im_step = (im_max - im_min) / height
    let re_range = re_max.sub(re_min);
    let im_range = im_max.sub(im_min);
    let w_rat = RuntimeRational::from_int(width as i64);
    let h_rat = RuntimeRational::from_int(height as i64);
    proof {
        Rational::lemma_eqv_zero_iff_num_zero(w_rat@);
        Rational::lemma_eqv_zero_iff_num_zero(h_rat@);
    }
    let re_step = re_range.div(&w_rat);
    let im_step = im_range.div(&h_rat);

    // Half-pixel offset for pixel centers
    let two = RuntimeRational::from_int(2);
    proof { Rational::lemma_eqv_zero_iff_num_zero(two@); }
    let half_re = re_step.div(&two);
    let half_im = im_step.div(&two);

    let mut row: u32 = 0;
    while row < height
        invariant
            re_min.wf_spec(),
            im_min.wf_spec(),
            re_step.wf_spec(),
            im_step.wf_spec(),
            half_re.wf_spec(),
            half_im.wf_spec(),
            0 <= row <= height,
            grid@.len() == row as int,
            width > 0,
            height > 0,
        decreases height - row,
    {
        let mut row_results: Vec<MandelbrotResult> = Vec::new();
        // im_center = im_min + (row + 0.5) * im_step = im_min + row * im_step + half_im
        let row_rat = RuntimeRational::from_int(row as i64);
        let im_offset = row_rat.mul(&im_step);
        let im_base = im_min.add(&im_offset);
        let im_center = im_base.add(&half_im);

        let mut col: u32 = 0;
        while col < width
            invariant
                re_min.wf_spec(),
                re_step.wf_spec(),
                half_re.wf_spec(),
                im_center.wf_spec(),
                0 <= col <= width,
                row_results@.len() == col as int,
            decreases width - col,
        {
            // re_center = re_min + (col + 0.5) * re_step
            let col_rat = RuntimeRational::from_int(col as i64);
            let re_offset = col_rat.mul(&re_step);
            let re_base = re_min.add(&re_offset);
            let re_center = re_base.add(&half_re);

            let result = mandelbrot_iterate(&re_center, &im_center, max_iters, precision);
            row_results.push(result);
            col = col + 1;
        }
        grid.push(row_results);
        row = row + 1;
    }

    grid
}

} // verus!
