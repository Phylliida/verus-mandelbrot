#[cfg(verus_keep_ghost)]
use crate::perturbation::*;
#[cfg(verus_keep_ghost)]
use crate::series_approximation::*;
#[cfg(verus_keep_ghost)]
use crate::runtime_perturbation::RefOrbitPoint;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use verus_rational::RuntimeRational;
#[cfg(verus_keep_ghost)]
use verus_rational::Rational;

#[cfg(verus_keep_ghost)]
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

/// A single SA coefficient point stored as full-precision rationals.
pub struct SaCoeffPoint {
    pub re: RuntimeRational,
    pub im: RuntimeRational,
}

impl SaCoeffPoint {
    pub open spec fn wf_spec(&self) -> bool {
        self.re.wf_spec() && self.im.wf_spec()
    }
}

/// Compute SA coefficients A_0, A_1, ..., A_{k-1} along the reference orbit.
/// A_0 = (0, 0), A_{n+1} = 2·Z_n·A_n + (1, 0).
///
/// Each coefficient is normalized periodically to control witness growth.
pub fn compute_sa_coefficients(
    orbit: &Vec<RefOrbitPoint>,
    center_re: &RuntimeRational,
    center_im: &RuntimeRational,
) -> (out: Vec<SaCoeffPoint>)
    requires
        orbit@.len() >= 1,
        center_re.wf_spec(),
        center_im.wf_spec(),
        forall|i: int| 0 <= i < orbit@.len() ==> (#[trigger] orbit@[i]).wf_spec(),
    ensures
        out@.len() == orbit@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
{
    let mut coeffs: Vec<SaCoeffPoint> = Vec::new();

    // A_0 = (0, 0)
    coeffs.push(SaCoeffPoint {
        re: RuntimeRational::from_int(0),
        im: RuntimeRational::from_int(0),
    });

    let two = RuntimeRational::from_int(2);
    let one = RuntimeRational::from_int(1);
    let mut ar = RuntimeRational::from_int(0);
    let mut ai = RuntimeRational::from_int(0);

    let orbit_len = orbit.len();
    let mut i: usize = 1;
    while i < orbit_len
        invariant
            center_re.wf_spec(),
            center_im.wf_spec(),
            two.wf_spec(),
            one.wf_spec(),
            ar.wf_spec(),
            ai.wf_spec(),
            1 <= i <= orbit_len,
            orbit_len == orbit@.len(),
            coeffs@.len() == i as int,
            forall|j: int| 0 <= j < orbit@.len() ==> (#[trigger] orbit@[j]).wf_spec(),
            forall|j: int| 0 <= j < coeffs@.len() ==> (#[trigger] coeffs@[j]).wf_spec(),
        decreases orbit_len - i,
    {
        // Z_n = orbit[i-1]
        let zr = &orbit[i - 1].re;
        let zi = &orbit[i - 1].im;

        // A_{n+1}_re = 2·Zr·Ar - 2·Zi·Ai + 1
        let two_zr_ar = two.mul(&zr.mul(&ar));
        let two_zi_ai = two.mul(&zi.mul(&ai));
        let new_re = two_zr_ar.sub(&two_zi_ai).add(&one);

        // A_{n+1}_im = 2·Zr·Ai + 2·Zi·Ar
        let two_zr_ai = two.mul(&zr.mul(&ai));
        let two_zi_ar = two.mul(&zi.mul(&ar));
        let new_im = two_zr_ai.add(&two_zi_ar);

        // Normalize periodically
        let norm_re = if i % 8 == 7 { new_re.normalize() } else { new_re };
        let norm_im = if i % 8 == 7 { new_im.normalize() } else { new_im };

        coeffs.push(SaCoeffPoint {
            re: copy_rational(&norm_re),
            im: copy_rational(&norm_im),
        });

        ar = norm_re;
        ai = norm_im;
        i = i + 1;
    }

    coeffs
}

} // verus!
