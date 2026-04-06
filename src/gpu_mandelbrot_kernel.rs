/// Verified GPU Mandelbrot kernel using signed fixed-point arithmetic.
///
/// Uses GenericFixedPoint<u32> from verus-fixed-point (926 verified, 0 errors).
/// No modular reduction — just Karatsuba multiply + fixed-point shift.
/// Bounds guaranteed by Mandelbrot dynamics: |z| < escape_radius.
///
/// Kernels:
/// 1. Reference orbit: Z_{n+1} = Z_n^2 + c (per reference point)
/// 2. Perturbation: d_{n+1} = 2*Z_n*d_n + d_n^2 + Dc (per pixel)

use vstd::prelude::*;
use verus_fixed_point::runtime_fixed_point::GenericFixedPoint;
use verus_fixed_point::fixed_point::limb_ops::*;

verus! {

/// Complex number as two GenericFixedPoint values.
pub struct FpComplex<T: LimbOps> {
    pub re: GenericFixedPoint<T>,
    pub im: GenericFixedPoint<T>,
}

impl<T: LimbOps> FpComplex<T> {
    pub open spec fn wf(&self) -> bool {
        &&& self.re.wf_spec() && self.im.wf_spec()
        &&& self.re.n_exec == self.im.n_exec
        &&& self.re.frac_exec == self.im.frac_exec
        &&& self.re.n_exec > 0
        &&& self.re.n_exec <= 0x1FFF_FFFF
        &&& self.re.frac_exec % 32 == 0
    }

    pub open spec fn same_format(&self, other: &Self) -> bool {
        self.re.n_exec == other.re.n_exec && self.re.frac_exec == other.re.frac_exec
    }
}

/// Complex squaring: z^2 = (re^2 - im^2, 2*re*im).
/// Uses 3 multiplies: re^2, im^2, (re+im)^2.
pub fn complex_square<T: LimbOps>(z: &FpComplex<T>) -> (out: FpComplex<T>)
    requires z.wf(),
    ensures out.wf(), out.same_format(z),
{
    let re2 = z.re.signed_mul(&z.re);
    let im2 = z.im.signed_mul(&z.im);
    let re_plus_im = z.re.signed_add(&z.im);
    let sum2 = re_plus_im.signed_mul(&re_plus_im);
    let new_re = re2.signed_sub(&im2);
    let t = sum2.signed_sub(&re2);
    let new_im = t.signed_sub(&im2);
    FpComplex { re: new_re, im: new_im }
}

/// Complex addition.
pub fn complex_add<T: LimbOps>(a: &FpComplex<T>, b: &FpComplex<T>) -> (out: FpComplex<T>)
    requires a.wf(), b.wf(), a.same_format(b),
    ensures out.wf(), out.same_format(a),
{
    FpComplex {
        re: a.re.signed_add(&b.re),
        im: a.im.signed_add(&b.im),
    }
}

/// Complex multiplication using 3-multiply Karatsuba trick.
pub fn complex_mul<T: LimbOps>(a: &FpComplex<T>, b: &FpComplex<T>) -> (out: FpComplex<T>)
    requires a.wf(), b.wf(), a.same_format(b),
    ensures out.wf(), out.same_format(a),
{
    let k1 = a.re.signed_mul(&b.re);
    let k2 = a.im.signed_mul(&b.im);
    let a_sum = a.re.signed_add(&a.im);
    let b_sum = b.re.signed_add(&b.im);
    let k3 = a_sum.signed_mul(&b_sum);
    let new_re = k1.signed_sub(&k2);
    let t = k3.signed_sub(&k1);
    let new_im = t.signed_sub(&k2);
    FpComplex { re: new_re, im: new_im }
}

/// Double: 2*z.
pub fn complex_double<T: LimbOps>(z: &FpComplex<T>) -> (out: FpComplex<T>)
    requires z.wf(),
    ensures out.wf(), out.same_format(z),
{
    FpComplex {
        re: z.re.signed_add(&z.re),
        im: z.im.signed_add(&z.im),
    }
}

/// Magnitude squared: |z|^2 = re^2 + im^2.
pub fn magnitude_squared<T: LimbOps>(z: &FpComplex<T>) -> (out: GenericFixedPoint<T>)
    requires z.wf(),
    ensures out.wf_spec(), out.n_exec == z.re.n_exec, out.frac_exec == z.re.frac_exec,
{
    let re2 = z.re.signed_mul(&z.re);
    let im2 = z.im.signed_mul(&z.im);
    re2.signed_add(&im2)
}

/// Reference orbit step: Z' = Z^2 + c.
pub fn ref_orbit_step<T: LimbOps>(z: &FpComplex<T>, c: &FpComplex<T>) -> (out: FpComplex<T>)
    requires z.wf(), c.wf(), z.same_format(c),
    ensures out.wf(), out.same_format(z),
{
    let z2 = complex_square(z);
    complex_add(&z2, c)
}

/// Perturbation step: d' = 2*Z*d + d^2 + Dc.
pub fn perturbation_step<T: LimbOps>(
    z_ref: &FpComplex<T>,
    delta: &FpComplex<T>,
    delta_c: &FpComplex<T>,
) -> (out: FpComplex<T>)
    requires z_ref.wf(), delta.wf(), delta_c.wf(),
        z_ref.same_format(delta), delta.same_format(delta_c),
    ensures out.wf(), out.same_format(z_ref),
{
    let two_z = complex_double(z_ref);
    let two_z_delta = complex_mul(&two_z, delta);
    let delta_sq = complex_square(delta);
    let sum = complex_add(&two_z_delta, &delta_sq);
    complex_add(&sum, delta_c)
}

} // verus!
