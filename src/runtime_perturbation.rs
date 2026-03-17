#[cfg(verus_keep_ghost)]
use crate::perturbation::*;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::Ghost;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use verus_rational::RuntimeRational;
#[cfg(verus_keep_ghost)]
use verus_rational::Rational;
use verus_interval_arithmetic::{RuntimeInterval, build_pow2};

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

/// A single point on the reference orbit, stored as intervals with bounded precision.
pub struct RefOrbitPoint {
    pub re: RuntimeInterval,
    pub im: RuntimeInterval,
}

impl RefOrbitPoint {
    pub open spec fn wf_spec(&self) -> bool {
        self.re.wf_spec() && self.im.wf_spec()
    }
}

/// Compute the reference orbit at (center_re, center_im) using interval arithmetic
/// with precision capped at `precision_bits` via `reduce(k)`. Returns orbit points
/// Z_0, Z_1, ..., Z_k where Z_0 = (0, 0) and Z_{n+1} = Z_n² + C.
/// Stops early if |Z|² > 4 (conservative: checks lower bound of magnitude interval).
pub fn compute_ref_orbit(
    center_re: &RuntimeRational,
    center_im: &RuntimeRational,
    max_iters: u32,
    precision_bits: u32,
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

    let zero = RuntimeRational::from_int(0);

    // Z_0 = (0, 0) as point intervals
    orbit.push(RefOrbitPoint {
        re: RuntimeInterval::from_point(&zero),
        im: RuntimeInterval::from_point(&zero),
    });

    let c_re = RuntimeInterval::from_point(center_re);
    let c_im = RuntimeInterval::from_point(center_im);
    let mut zr = RuntimeInterval::from_point(&zero);
    let mut zi = RuntimeInterval::from_point(&zero);
    let two = RuntimeRational::from_int(2);
    let four = RuntimeRational::from_int(4);
    // Bailout threshold: if upper bound of |z|² exceeds this, the interval
    // has blown up and the orbit is no longer useful for perturbation.
    // Keep tight (16) so we stop before interval midpoints become unreliable.
    let bailout = RuntimeRational::from_int(16);
    // Precompute 2^precision_bits once for all reduce calls
    let pow2_wit = build_pow2(precision_bits);

    let mut i: u32 = 0;
    while i < max_iters
        invariant
            c_re.wf_spec(),
            c_im.wf_spec(),
            zr.wf_spec(),
            zi.wf_spec(),
            two.wf_spec(),
            four.wf_spec(),
            bailout.wf_spec(),
            pow2_wit.wf_spec(),
            pow2_wit.model@ == verus_interval_arithmetic::interval::pow2_spec(precision_bits as nat),
            0 <= i <= max_iters,
            orbit@.len() == (i as int) + 1,
            forall|j: int| 0 <= j < orbit@.len() ==> (#[trigger] orbit@[j]).wf_spec(),
        decreases max_iters - i,
    {
        // z_{n+1} = z_n² + c
        // re' = zr² - zi² + cr
        // im' = 2·zr·zi + ci
        let zr2 = zr.square();
        let zi2 = zi.square();
        let zr_zi = zr.mul(&zi);
        let two_zr_zi = RuntimeInterval::scale(&two, &zr_zi);

        let new_re = zr2.sub(&zi2).add(&c_re).reduce_with_pow2(&pow2_wit, Ghost(precision_bits as nat));
        let new_im = two_zr_zi.add(&c_im).reduce_with_pow2(&pow2_wit, Ghost(precision_bits as nat));

        // Push a copy of the orbit point
        orbit.push(RefOrbitPoint {
            re: copy_interval(&new_re),
            im: copy_interval(&new_im),
        });

        // Check escape: lower bound of |z|² > 4 means definitely escaped.
        // Also bail out if upper bound exceeds bailout threshold — interval
        // arithmetic error has grown too large for the orbit to be useful.
        let mag_re2 = new_re.square();
        let mag_im2 = new_im.square();
        let mag_sq = mag_re2.add(&mag_im2);
        let escaped = four.lt(&mag_sq.lo);
        let blown = bailout.lt(&mag_sq.hi);

        if escaped || blown {
            return orbit;
        }

        zr = new_re;
        zi = new_im;
        i = i + 1;
    }

    orbit
}

} // verus!
