///  Verified GPU Mandelbrot kernel — prime field arithmetic for deep zoom.
///
///  Both reference orbits (Z_{n+1} = Z_n^2 + c) and perturbation
///  (δ_{n+1} = 2·Z_n·δ_n + δ_n^2 + Δc) run on GPU using the same
///  verified RuntimePrimeField<u32> operations.
///
///  Arithmetic: pseudo-Mersenne prime p = 2^(32*N) - c.
///  Complex numbers: two RuntimePrimeField values (re, im).
///  Escape detection: |z|^2 > threshold via BoundedPrimeField centered comparison.

use vstd::prelude::*;
use verus_fixed_point::fixed_point::prime_field::*;
use verus_fixed_point::fixed_point::limb_ops::*;

verus! {

///  Complex number over a prime field.
pub struct PrimeComplex {
    pub re: RuntimePrimeField<u32>,
    pub im: RuntimePrimeField<u32>,
}

impl PrimeComplex {
    pub open spec fn wf(&self) -> bool {
        &&& self.re.wf() && self.im.wf()
        &&& self.re.same_field(&self.im)
        &&& self.re.n_exec >= 2
        &&& self.re.n_exec <= 0x1FFF_FFFF
    }

    pub open spec fn same_field(&self, other: &Self) -> bool {
        self.re.same_field(&other.re)
    }
}

///  Complex squaring: z^2 = (re^2 - im^2, 2*re*im).
///  Uses 3 multiplications: re^2, im^2, (re+im)^2.
///  Then: new_re = re^2 - im^2, new_im = (re+im)^2 - re^2 - im^2.
///  This avoids computing 2*re*im directly (which would need doubling).
pub fn complex_square(z: &PrimeComplex) -> (out: PrimeComplex)
    requires z.wf(),
    ensures out.wf(), out.same_field(z),
{
    let re2 = z.re.mul_mod(&z.re);
    let im2 = z.im.mul_mod(&z.im);
    //  new_re = re^2 - im^2
    let new_re = re2.sub_mod(&im2);
    //  For new_im = 2*re*im, use (re+im)^2 - re^2 - im^2
    let re_plus_im = z.re.add_mod(&z.im);
    let sum2 = re_plus_im.mul_mod(&re_plus_im);
    let sum2_minus_re2 = sum2.sub_mod(&re2);
    let new_im = sum2_minus_re2.sub_mod(&im2);
    PrimeComplex { re: new_re, im: new_im }
}

///  Complex addition: a + b = (a.re + b.re, a.im + b.im).
pub fn complex_add(a: &PrimeComplex, b: &PrimeComplex) -> (out: PrimeComplex)
    requires a.wf(), b.wf(), a.same_field(b),
    ensures out.wf(), out.same_field(a),
{
    PrimeComplex {
        re: a.re.add_mod(&b.re),
        im: a.im.add_mod(&b.im),
    }
}

///  Complex subtraction: a - b = (a.re - b.re, a.im - b.im).
pub fn complex_sub(a: &PrimeComplex, b: &PrimeComplex) -> (out: PrimeComplex)
    requires a.wf(), b.wf(), a.same_field(b),
    ensures out.wf(), out.same_field(a),
{
    PrimeComplex {
        re: a.re.sub_mod(&b.re),
        im: a.im.sub_mod(&b.im),
    }
}

///  Scalar multiply by 2: 2*z = z + z.
pub fn complex_double(z: &PrimeComplex) -> (out: PrimeComplex)
    requires z.wf(),
    ensures out.wf(), out.same_field(z),
{
    PrimeComplex {
        re: z.re.add_mod(&z.re),
        im: z.im.add_mod(&z.im),
    }
}

///  Complex multiplication: a * b = (a.re*b.re - a.im*b.im, a.re*b.im + a.im*b.re).
///  Uses Karatsuba-like: 3 multiplications instead of 4.
///  k1 = a.re * b.re, k2 = a.im * b.im, k3 = (a.re + a.im) * (b.re + b.im)
///  out.re = k1 - k2, out.im = k3 - k1 - k2
pub fn complex_mul(a: &PrimeComplex, b: &PrimeComplex) -> (out: PrimeComplex)
    requires a.wf(), b.wf(), a.same_field(b),
    ensures out.wf(), out.same_field(a),
{
    let k1 = a.re.mul_mod(&b.re);
    let k2 = a.im.mul_mod(&b.im);
    let a_sum = a.re.add_mod(&a.im);
    let b_sum = b.re.add_mod(&b.im);
    let k3 = a_sum.mul_mod(&b_sum);
    let new_re = k1.sub_mod(&k2);
    let k3_minus_k1 = k3.sub_mod(&k1);
    let new_im = k3_minus_k1.sub_mod(&k2);
    PrimeComplex { re: new_re, im: new_im }
}

///  Magnitude squared: |z|^2 = re^2 + im^2 (as a field element).
pub fn magnitude_squared(z: &PrimeComplex) -> (out: RuntimePrimeField<u32>)
    requires z.wf(),
    ensures out.wf(), out.same_field(&z.re),
{
    let re2 = z.re.mul_mod(&z.re);
    let im2 = z.im.mul_mod(&z.im);
    re2.add_mod(&im2)
}

//  ═══════════════════════════════════════════════════════════════
//  Reference orbit: Z_{n+1} = Z_n^2 + c
//  ═══════════════════════════════════════════════════════════════

///  One step of the reference orbit: Z' = Z^2 + c.
pub fn ref_orbit_step(z: &PrimeComplex, c: &PrimeComplex) -> (out: PrimeComplex)
    requires z.wf(), c.wf(), z.same_field(c),
    ensures out.wf(), out.same_field(z),
{
    let z2 = complex_square(z);
    complex_add(&z2, c)
}

///  Spec: the Mandelbrot iteration z_{n+1} = z_n^2 + c produces the
///  correct modular values at each step.
///  On GPU, both reference orbit and perturbation call ref_orbit_step
///  and perturbation_step respectively in a per-thread loop.

//  ═══════════════════════════════════════════════════════════════
//  Perturbation: δ_{n+1} = 2·Z_n·δ_n + δ_n^2 + Δc
//  ═══════════════════════════════════════════════════════════════

///  One step of perturbation orbit: δ' = 2·Z·δ + δ^2 + Δc.
///  Z is the reference orbit value at this iteration.
pub fn perturbation_step(
    z_ref: &PrimeComplex,
    delta: &PrimeComplex,
    delta_c: &PrimeComplex,
) -> (out: PrimeComplex)
    requires z_ref.wf(), delta.wf(), delta_c.wf(),
        z_ref.same_field(delta), delta.same_field(delta_c),
    ensures out.wf(), out.same_field(z_ref),
{
    //  2·Z·δ
    let two_z = complex_double(z_ref);
    let two_z_delta = complex_mul(&two_z, delta);
    //  δ^2
    let delta_sq = complex_square(delta);
    //  2·Z·δ + δ^2
    let sum = complex_add(&two_z_delta, &delta_sq);
    //  + Δc
    complex_add(&sum, delta_c)
}

} // verus!
