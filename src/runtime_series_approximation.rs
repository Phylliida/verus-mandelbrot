#[cfg(verus_keep_ghost)]
use crate::perturbation::*;
#[cfg(verus_keep_ghost)]
use crate::series_approximation::*;
use crate::runtime_perturbation::RefOrbitPoint;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::Ghost;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use verus_rational::RuntimeRational;
#[cfg(verus_keep_ghost)]
use verus_rational::Rational;
use verus_interval_arithmetic::RuntimeInterval;

verus! {

/// Copy a RuntimeRational by copying its internal witnesses.
fn copy_rational(r: &RuntimeRational) -> (out: RuntimeRational)
    requires r.wf_spec(),
    ensures out.wf_spec(), out@ == r@,
{
    let num_copy = r.numerator.copy_small_total();
    let den_copy = r.denominator.copy_small_total();
    RuntimeRational {
        numerator: num_copy,
        denominator: den_copy,
        model: Ghost(r@),
    }
}

/// Copy a RuntimeInterval by copying both endpoints.
fn copy_interval(iv: &RuntimeInterval) -> (out: RuntimeInterval)
    requires iv.wf_spec(),
    ensures out.wf_spec(), out@.lo == iv@.lo, out@.hi == iv@.hi,
{
    RuntimeInterval::from_endpoints(copy_rational(&iv.lo), copy_rational(&iv.hi))
}

/// A single SA coefficient point stored as intervals with bounded precision.
pub struct SaCoeffPoint {
    pub re: RuntimeInterval,
    pub im: RuntimeInterval,
}

impl SaCoeffPoint {
    pub open spec fn wf_spec(&self) -> bool {
        self.re.wf_spec() && self.im.wf_spec()
    }
}

/// Compute SA coefficients A_0, A_1, ..., A_{k-1} along the reference orbit.
/// A_0 = (0, 0), A_{n+1} = 2·Z_n·A_n + (1, 0).
///
/// Uses interval arithmetic with precision capped at `precision_bits` via `reduce(k)`.
pub fn compute_sa_coefficients(
    orbit: &Vec<RefOrbitPoint>,
    precision_bits: u32,
) -> (out: Vec<SaCoeffPoint>)
    requires
        orbit@.len() >= 1,
        forall|i: int| 0 <= i < orbit@.len() ==> (#[trigger] orbit@[i]).wf_spec(),
    ensures
        out@.len() == orbit@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
{
    let mut coeffs: Vec<SaCoeffPoint> = Vec::new();

    let zero = RuntimeRational::from_int(0);
    let two = RuntimeRational::from_int(2);
    let one = RuntimeRational::from_int(1);

    // A_0 = (0, 0) as point intervals
    let zero_iv = RuntimeInterval::from_point(&zero);
    let one_iv = RuntimeInterval::from_point(&one);
    coeffs.push(SaCoeffPoint {
        re: RuntimeInterval::from_point(&zero),
        im: RuntimeInterval::from_point(&zero),
    });

    let mut ar = RuntimeInterval::from_point(&zero);
    let mut ai = RuntimeInterval::from_point(&zero);

    let orbit_len = orbit.len();
    let mut i: usize = 1;
    while i < orbit_len
        invariant
            two.wf_spec(),
            one_iv.wf_spec(),
            ar.wf_spec(),
            ai.wf_spec(),
            1 <= i <= orbit_len,
            orbit_len == orbit@.len(),
            coeffs@.len() == i as int,
            forall|j: int| 0 <= j < orbit@.len() ==> (#[trigger] orbit@[j]).wf_spec(),
            forall|j: int| 0 <= j < coeffs@.len() ==> (#[trigger] coeffs@[j]).wf_spec(),
        decreases orbit_len - i,
    {
        // Z_n = orbit[i-1]  (interval components)
        let zr = &orbit[i - 1].re;
        let zi = &orbit[i - 1].im;

        // A_{n+1}_re = 2·Zr·Ar - 2·Zi·Ai + 1
        let two_zr_ar = RuntimeInterval::scale(&two, &zr.mul(&ar));
        let two_zi_ai = RuntimeInterval::scale(&two, &zi.mul(&ai));
        let new_re = two_zr_ar.sub(&two_zi_ai).add(&one_iv).reduce(precision_bits);

        // A_{n+1}_im = 2·Zr·Ai + 2·Zi·Ar
        let two_zr_ai = RuntimeInterval::scale(&two, &zr.mul(&ai));
        let two_zi_ar = RuntimeInterval::scale(&two, &zi.mul(&ar));
        let new_im = two_zr_ai.add(&two_zi_ar).reduce(precision_bits);

        coeffs.push(SaCoeffPoint {
            re: copy_interval(&new_re),
            im: copy_interval(&new_im),
        });

        ar = new_re;
        ai = new_im;
        i = i + 1;
    }

    coeffs
}

} // verus!
