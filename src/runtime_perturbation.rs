#[cfg(verus_keep_ghost)]
use crate::perturbation::*;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::Ghost;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use verus_rational::RuntimeRational;
#[cfg(verus_keep_ghost)]
use verus_rational::Rational;

verus! {

/// Debug helper: print orbit iteration progress.
#[verifier::external_body]
fn print_orbit_progress(iter: u32, re: &RuntimeRational, im: &RuntimeRational)
    requires re.wf_spec(), im.wf_spec(),
{
    let re_num = re.numerator.magnitude.limbs_le.len();
    let re_den = re.denominator.limbs_le.len();
    let im_num = im.numerator.magnitude.limbs_le.len();
    let im_den = im.denominator.limbs_le.len();
    eprintln!("    orbit iter {:4}: re limbs {}/{}, im limbs {}/{}",
        iter, re_num, re_den, im_num, im_den);
}

/// Debug helper: print input rational sizes.
#[verifier::external_body]
fn print_rational_info(label: &str, r: &RuntimeRational)
    requires r.wf_spec(),
{
    let num = r.numerator.magnitude.limbs_le.len();
    let den = r.denominator.limbs_le.len();
    eprintln!("    {}: num_limbs={}, den_limbs={}", label, num, den);
}

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

    print_rational_info("center_re", center_re);
    print_rational_info("center_im", center_im);

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

        // Debug: print iteration progress with limb sizes
        print_orbit_progress(i + 1, &new_re, &new_im);

        // Push a copy of the orbit point
        orbit.push(RefOrbitPoint {
            re: copy_rational(&new_re),
            im: copy_rational(&new_im),
        });

        // Check escape: |z|² > 4 (no normalize — div_rem is O(quotient))
        let mag_re2 = new_re.mul(&new_re);
        let mag_im2 = new_im.mul(&new_im);
        let mag_sq = mag_re2.add(&mag_im2);
        let escaped = four.lt(&mag_sq);

        if escaped {
            return orbit;
        }

        zr = new_re;
        zi = new_im;
        i = i + 1;
    }

    orbit
}

} // verus!
