#[cfg(verus_keep_ghost)]
use crate::perturbation::*;
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

/// A single point on the reference orbit, stored as full-precision rationals.
pub struct RefOrbitPoint {
    pub re: RuntimeRational,
    pub im: RuntimeRational,
}

impl RefOrbitPoint {
    pub open spec fn wf_spec(&self) -> bool {
        self.re.wf_spec() && self.im.wf_spec()
    }
}

/// Compute the reference orbit at (center_re, center_im) using full-precision
/// rational arithmetic. Returns orbit points Z_0, Z_1, ..., Z_k where
/// Z_0 = (0, 0) and Z_{n+1} = Z_n² + C. Stops early if |Z|² > 4.
///
/// Each point is normalized periodically to control witness growth.
pub fn compute_ref_orbit(
    center_re: &RuntimeRational,
    center_im: &RuntimeRational,
    max_iters: u32,
) -> (out: Vec<RefOrbitPoint>)
    requires
        center_re.wf_spec(),
        center_im.wf_spec(),
        max_iters > 0,
    ensures
        out@.len() >= 1,
        out@.len() <= max_iters as int + 1,
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
{
    let mut orbit: Vec<RefOrbitPoint> = Vec::new();

    // Z_0 = (0, 0)
    orbit.push(RefOrbitPoint {
        re: RuntimeRational::from_int(0),
        im: RuntimeRational::from_int(0),
    });

    let mut zr = RuntimeRational::from_int(0);
    let mut zi = RuntimeRational::from_int(0);
    let two = RuntimeRational::from_int(2);
    let four = RuntimeRational::from_int(4);

    let mut i: u32 = 0;
    while i < max_iters
        invariant
            center_re.wf_spec(),
            center_im.wf_spec(),
            zr.wf_spec(),
            zi.wf_spec(),
            two.wf_spec(),
            four.wf_spec(),
            0 <= i <= max_iters,
            orbit@.len() == (i as int) + 1,
            forall|j: int| 0 <= j < orbit@.len() ==> (#[trigger] orbit@[j]).wf_spec(),
        decreases max_iters - i,
    {
        // z_{n+1} = z_n² + c
        // re' = zr² - zi² + cr
        // im' = 2·zr·zi + ci
        let zr2 = zr.mul(&zr);
        let zi2 = zi.mul(&zi);
        let zr_zi = zr.mul(&zi);
        let two_zr_zi = two.mul(&zr_zi);

        let new_re = zr2.sub(&zi2).add(center_re);
        let new_im = two_zr_zi.add(center_im);

        // Normalize periodically to control witness growth
        let norm_re = if i % 8 == 7 { new_re.normalize() } else { new_re };
        let norm_im = if i % 8 == 7 { new_im.normalize() } else { new_im };

        // Push a copy of the orbit point
        orbit.push(RefOrbitPoint {
            re: copy_rational(&norm_re),
            im: copy_rational(&norm_im),
        });

        // Check escape: |z|² > 4
        let mag_re2 = norm_re.mul(&norm_re);
        let mag_im2 = norm_im.mul(&norm_im);
        let mag_sq = mag_re2.add(&mag_im2);
        let escaped = four.lt(&mag_sq);

        if escaped {
            return orbit;
        }

        zr = norm_re;
        zi = norm_im;
        i = i + 1;
    }

    orbit
}

} // verus!
