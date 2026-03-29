//! Conversion helpers between the viewer's sign-magnitude fixed-point format
//! and the verified `RuntimeRational` arithmetic used by SA/perturbation.

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::Ghost;

use verus_rational::RuntimeRational;
use verus_interval_arithmetic::RuntimeInterval;
use crate::runtime_perturbation::RefOrbitPoint;
use crate::runtime_series_approximation::SaCoeffPoint;

verus! {

///  Convert viewer sign-magnitude fixed-point (MSB-first limbs) to RuntimeRational.
///
///  The viewer format: value = ±(limb[0] + limb[1]/2^32 + limb[2]/2^64 + ...)
///
///  Built as: result = limb[0] + limb[1]*(1/B) + limb[2]*(1/B)^2 + ...
///  where B = 2^32 = 4294967296, using RuntimeRational::from_frac(1, B) as the base.
pub fn fp_to_rational(limbs: &[u32], sign: bool) -> (out: RuntimeRational)
    requires limbs.len() > 0,
    ensures out.wf_spec(),
{
    let inv_base = RuntimeRational::from_frac(1, 4294967296i64); //  1/2^32
    let mut result = RuntimeRational::from_int(limbs[0] as i64);
    let mut power = RuntimeRational::from_frac(1, 4294967296i64); //  starts at 1/B

    let n = limbs.len();
    let mut j: usize = 1;
    while j < n
        invariant
            1 <= j <= n,
            n == limbs@.len(),
            result.wf_spec(),
            power.wf_spec(),
            inv_base.wf_spec(),
        decreases n - j,
    {
        let term = RuntimeRational::from_int(limbs[j] as i64).mul(&power);
        result = result.add(&term);
        power = power.mul(&inv_base);
        if j % 4 == 0 {
            result = result.normalize();
            power = power.normalize();
        }
        j = j + 1;
    }

    //  Apply sign: negate if negative
    if sign {
        let zero = RuntimeRational::from_int(0);
        result = zero.sub(&result);
    }

    result
}

} //  verus!

//  ── f64/f32 conversion helpers (outside verus! — floats not supported by verifier) ──

///  Convert RuntimeRational to f64 by reading BigInt limbs directly.
///  Lossy (f64 has ~52 bits of mantissa) but sufficient for GPU upload.
pub fn rational_to_f64(r: &RuntimeRational) -> f64 {
    let num_f64 = bigint_to_f64(&r.numerator);
    let den_f64 = bignat_to_f64(&r.denominator);
    if den_f64 == 0.0 { 0.0 } else { num_f64 / den_f64 }
}

fn bigint_to_f64(b: &verus_bigint::RuntimeBigIntWitness) -> f64 {
    let mag = bignat_to_f64(&b.magnitude);
    if b.is_negative { -mag } else { mag }
}

fn bignat_to_f64(b: &verus_bigint::RuntimeBigNatWitness) -> f64 {
    let limbs = &b.limbs_le;
    let n = limbs.len();
    let mut val = 0.0f64;
    //  Process MSB to LSB for better floating-point precision
    for i in 0..n {
        let idx = n - 1 - i;
        val = val * 4294967296.0f64 + limbs[idx] as f64;
    }
    val
}

///  Convert a RuntimeInterval to f64 by taking the midpoint of [lo, hi].
pub fn interval_to_f64(iv: &RuntimeInterval) -> f64 {
    let lo = rational_to_f64(&iv.lo);
    let hi = rational_to_f64(&iv.hi);
    (lo + hi) / 2.0
}

///  Convert Vec<RefOrbitPoint> to interleaved f32 pairs [re0,im0,re1,im1,...] for GPU SSBO.
pub fn orbit_to_f32(orbit: &[RefOrbitPoint]) -> Vec<f32> {
    let mut result: Vec<f32> = Vec::with_capacity(orbit.len() * 2);
    for pt in orbit {
        result.push(interval_to_f64(&pt.re) as f32);
        result.push(interval_to_f64(&pt.im) as f32);
    }
    result
}

///  SA skip result.
pub struct SaSkipResult {
    pub skip_iters: u32,
    pub sa_re: f32,
    pub sa_im: f32,
}

///  Find SA skip: first iteration where |A * pixel_step| is a normal f32.
///  Returns skip_iters=0 if SA is not needed or no valid skip was found.
pub fn find_sa_skip(
    sa_coeffs: &[SaCoeffPoint],
    pixel_step_f64: f64,
    needs_sa: bool,
) -> SaSkipResult {
    if !needs_sa {
        return SaSkipResult { skip_iters: 0, sa_re: 0.0, sa_im: 0.0 };
    }

    let sa_normal_threshold = f32::MIN_POSITIVE as f64;
    let f32_max_half = (f32::MAX as f64) * 0.5;

    let mut skip_n = 0usize;
    let mut best_skip = 0usize;
    let mut best_sa_mag = 0.0f64;

    for (i, coeff) in sa_coeffs.iter().enumerate() {
        let a_re_f64 = interval_to_f64(&coeff.re);
        let a_im_f64 = interval_to_f64(&coeff.im);
        let sa_re_f64 = a_re_f64 * pixel_step_f64;
        let sa_im_f64 = a_im_f64 * pixel_step_f64;
        let sa_mag = sa_re_f64.abs().max(sa_im_f64.abs());

        if sa_mag >= sa_normal_threshold && skip_n == 0 {
            skip_n = i;
        }
        if sa_mag > best_sa_mag && sa_mag < f32_max_half {
            best_sa_mag = sa_mag;
            best_skip = i;
        }
    }

    if skip_n == 0 && best_skip > 0 {
        skip_n = best_skip;
    }

    if skip_n > 0 {
        let a_re_f64 = interval_to_f64(&sa_coeffs[skip_n].re);
        let a_im_f64 = interval_to_f64(&sa_coeffs[skip_n].im);
        SaSkipResult {
            skip_iters: skip_n as u32,
            sa_re: (a_re_f64 * pixel_step_f64) as f32,
            sa_im: (a_im_f64 * pixel_step_f64) as f32,
        }
    } else {
        SaSkipResult { skip_iters: 0, sa_re: 0.0, sa_im: 0.0 }
    }
}
