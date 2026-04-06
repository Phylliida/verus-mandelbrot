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

// ═══════════════════════════════════════════════════════════════
// Spec-level complex arithmetic (over int, exact, no overflow)
// ═══════════════════════════════════════════════════════════════

/// Complex number as (re, im) pair of ints.
pub struct SpecComplex {
    pub re: int,
    pub im: int,
}

/// Complex squaring: (a+bi)² = (a²-b², 2ab)
pub open spec fn spec_complex_square(z: SpecComplex) -> SpecComplex {
    SpecComplex {
        re: z.re * z.re - z.im * z.im,
        im: 2 * z.re * z.im,
    }
}

/// Complex addition
pub open spec fn spec_complex_add(a: SpecComplex, b: SpecComplex) -> SpecComplex {
    SpecComplex { re: a.re + b.re, im: a.im + b.im }
}

/// Reference orbit step: Z' = Z² + c
pub open spec fn spec_ref_step(z: SpecComplex, c: SpecComplex) -> SpecComplex {
    spec_complex_add(spec_complex_square(z), c)
}

/// Perturbation step: δ' = 2Zδ + δ² + Δc
pub open spec fn spec_pert_step(z: SpecComplex, delta: SpecComplex, dc: SpecComplex) -> SpecComplex {
    SpecComplex {
        re: 2 * z.re * delta.re - 2 * z.im * delta.im
            + delta.re * delta.re - delta.im * delta.im
            + dc.re,
        im: 2 * z.re * delta.im + 2 * z.im * delta.re
            + 2 * delta.re * delta.im
            + dc.im,
    }
}

/// Full orbit value: W = Z + δ
pub open spec fn spec_full_orbit(z: SpecComplex, delta: SpecComplex) -> SpecComplex {
    spec_complex_add(z, delta)
}

// ═══════════════════════════════════════════════════════════════
// THE MAIN THEOREM: Perturbation theory is correct
// ═══════════════════════════════════════════════════════════════

/// Proof that perturbation correctly tracks the actual orbit.
///
/// If Z' = Z² + c_ref (reference step)
/// and δ' = 2Zδ + δ² + Δc (perturbation step)
/// then (Z' + δ') = (Z + δ)² + (c_ref + Δc) (actual orbit step)
///
/// This means: tracking δ relative to the reference orbit Z
/// gives the exact same result as computing the actual orbit W = Z + δ
/// directly via W' = W² + c_pixel.
proof fn theorem_perturbation_correctness(
    z: SpecComplex,
    delta: SpecComplex,
    c_ref: SpecComplex,
    delta_c: SpecComplex,
)
    ensures ({
        let z_next = spec_ref_step(z, c_ref);
        let delta_next = spec_pert_step(z, delta, delta_c);
        let w = spec_full_orbit(z, delta);
        let c_pixel = spec_complex_add(c_ref, delta_c);
        let w_next = spec_ref_step(w, c_pixel);
        let pert_result = spec_complex_add(z_next, delta_next);
        // The perturbation result (Z' + delta') equals the actual orbit step (W^2 + c_pixel)
        &&& pert_result.re == w_next.re
        &&& pert_result.im == w_next.im
    })
{
    let z_re = z.re;
    let z_im = z.im;
    let d_re = delta.re;
    let d_im = delta.im;
    let c_re = c_ref.re;
    let c_im = c_ref.im;
    let dc_re = delta_c.re;
    let dc_im = delta_c.im;

    // W = Z + delta
    let w_re = z_re + d_re;
    let w_im = z_im + d_im;

    // Expand (Z+delta)^2 components — pass definitions via requires
    assert(w_re * w_re == z_re * z_re + 2 * z_re * d_re + d_re * d_re)
        by(nonlinear_arith) requires w_re == z_re + d_re;
    assert(w_im * w_im == z_im * z_im + 2 * z_im * d_im + d_im * d_im)
        by(nonlinear_arith) requires w_im == z_im + d_im;
    assert(w_re * w_im == z_re * z_im + z_re * d_im + d_re * z_im + d_re * d_im)
        by(nonlinear_arith) requires w_re == z_re + d_re, w_im == z_im + d_im;

    // Connect to spec functions: unfold the definitions
    let z_next = spec_ref_step(z, c_ref);
    let delta_next = spec_pert_step(z, delta, delta_c);
    let w = spec_full_orbit(z, delta);
    let c_pixel = spec_complex_add(c_ref, delta_c);
    let w_next = spec_ref_step(w, c_pixel);
    let pert_result = spec_complex_add(z_next, delta_next);

    // Real part: (z_re^2 - z_im^2 + c_re) + (2*z_re*d_re - 2*z_im*d_im + d_re^2 - d_im^2 + dc_re)
    //          = w_re^2 - w_im^2 + c_re + dc_re
    assert(pert_result.re == z_next.re + delta_next.re);
    assert(z_next.re == z_re * z_re - z_im * z_im + c_re);
    assert(delta_next.re == 2 * z_re * d_re - 2 * z_im * d_im + d_re * d_re - d_im * d_im + dc_re);
    assert(w_next.re == w_re * w_re - w_im * w_im + c_re + dc_re);

    // Imaginary part: (2*z_re*z_im + c_im) + (2*z_re*d_im + 2*z_im*d_re + 2*d_re*d_im + dc_im)
    //               = 2*w_re*w_im + c_im + dc_im
    assert(pert_result.im == z_next.im + delta_next.im);
    assert(z_next.im == 2 * z_re * z_im + c_im);
    assert(delta_next.im == 2 * z_re * d_im + 2 * z_im * d_re + 2 * d_re * d_im + dc_im);
    assert(w_next.im == 2 * w_re * w_im + c_im + dc_im);

    // Chain: substitute the product expansions into the postcondition
    assert(pert_result.re == w_next.re) by(nonlinear_arith)
        requires
            pert_result.re == z_re * z_re - z_im * z_im + c_re
                + 2 * z_re * d_re - 2 * z_im * d_im + d_re * d_re - d_im * d_im + dc_re,
            w_next.re == w_re * w_re - w_im * w_im + c_re + dc_re,
            w_re * w_re == z_re * z_re + 2 * z_re * d_re + d_re * d_re,
            w_im * w_im == z_im * z_im + 2 * z_im * d_im + d_im * d_im;
    assert(pert_result.im == w_next.im) by(nonlinear_arith)
        requires
            pert_result.im == 2 * z_re * z_im + c_im
                + 2 * z_re * d_im + 2 * z_im * d_re + 2 * d_re * d_im + dc_im,
            w_next.im == 2 * w_re * w_im + c_im + dc_im,
            w_re * w_im == z_re * z_im + z_re * d_im + d_re * z_im + d_re * d_im;
}

/// Step-correctness predicate: Z_k + delta_k steps to (Z_k + delta_k)^2 + c_pixel
pub open spec fn perturbation_step_correct(
    z_orbit: Seq<SpecComplex>,
    delta_orbit: Seq<SpecComplex>,
    c_ref: SpecComplex,
    delta_c: SpecComplex,
    k: int,
) -> bool {
    let w_k = spec_full_orbit(z_orbit[k], delta_orbit[k]);
    let c_pixel = spec_complex_add(c_ref, delta_c);
    let w_k_next = spec_ref_step(w_k, c_pixel);
    let pert_result = spec_full_orbit(z_orbit[k + 1], delta_orbit[k + 1]);
    pert_result.re == w_k_next.re && pert_result.im == w_k_next.im
}

/// Corollary: perturbation is correct for N iterations.
/// If delta_0 = W_0 - Z_0, then delta_n = W_n - Z_n for all n.
proof fn theorem_perturbation_n_steps(
    z_orbit: Seq<SpecComplex>,     // Z_0, Z_1, ..., Z_n
    delta_orbit: Seq<SpecComplex>, // δ_0, δ_1, ..., δ_n
    c_ref: SpecComplex,
    delta_c: SpecComplex,
    n: nat,
)
    requires
        z_orbit.len() >= n + 1,
        delta_orbit.len() >= n + 1,
        // Reference orbit: Z_{k+1} = Z_k² + c_ref
        forall|k: int| 0 <= k < n as int ==> z_orbit[k + 1] == #[trigger] spec_ref_step(z_orbit[k], c_ref),
        // Perturbation orbit: delta_{k+1} = 2*Z_k*delta_k + delta_k^2 + Dc
        forall|k: int| 0 <= k < n as int ==> delta_orbit[k + 1] == #[trigger] spec_pert_step(z_orbit[k], delta_orbit[k], delta_c),
    ensures
        forall|k: int| 0 <= k < n as int ==>
            #[trigger] perturbation_step_correct(z_orbit, delta_orbit, c_ref, delta_c, k)
    decreases n
{
    if n > 0 {
        // Prove for k = n-1 using the single-step theorem
        let k = (n - 1) as int;
        theorem_perturbation_correctness(z_orbit[k], delta_orbit[k], c_ref, delta_c);
        // Induction: prove for all k < n-1
        if n > 1 {
            theorem_perturbation_n_steps(z_orbit, delta_orbit, c_ref, delta_c, (n - 1) as nat);
        }
    }
}

// ═══════════════════════════════════════════════════════════════
// THEOREM: Glitch detection soundness
// ═══════════════════════════════════════════════════════════════

/// Bound on the next perturbation step given bounded inputs.
/// If |Z_re|,|Z_im| <= R and |delta_re|,|delta_im| <= T and |Dc| <= eps,
/// then |delta'_re|,|delta'_im| <= 4*R*T + 2*T*T + eps.
///
/// For our Mandelbrot renderer: R=2, T=3, eps=1 gives bound=43.
/// Since 43 << 2^32 (u32 max), no fixed-point overflow occurs even
/// if glitch detection is one iteration late.
proof fn theorem_glitch_detection_soundness(
    z_re: int, z_im: int,
    d_re: int, d_im: int,
    dc_re: int, dc_im: int,
    r: int,
    t: int,
    eps: int,
)
    requires
        // Reference orbit bounded by escape radius
        -r <= z_re && z_re <= r,
        -r <= z_im && z_im <= r,
        // Perturbation passed glitch check (bounded by threshold)
        -t <= d_re && d_re <= t,
        -t <= d_im && d_im <= t,
        // Pixel spacing bounded
        -eps <= dc_re && dc_re <= eps,
        -eps <= dc_im && dc_im <= eps,
        r > 0, t > 0, eps >= 0,
    ensures ({
        let dp_re = 2 * z_re * d_re - 2 * z_im * d_im + d_re * d_re - d_im * d_im + dc_re;
        let dp_im = 2 * z_re * d_im + 2 * z_im * d_re + 2 * d_re * d_im + dc_im;
        let bound: int = 4 * r * t + 2 * t * t + eps;
        // Next perturbation step is bounded — no overflow
        &&& -bound <= dp_re && dp_re <= bound
        &&& -bound <= dp_im && dp_im <= bound
    })
{
    // Real part: dp_re = 2*z_re*d_re - 2*z_im*d_im + d_re^2 - d_im^2 + dc_re
    // |2*z_re*d_re| <= 2*r*t, |2*z_im*d_im| <= 2*r*t
    // |d_re^2| <= t^2, |d_im^2| <= t^2, |dc_re| <= eps
    // |dp_re| <= 2*r*t + 2*r*t + t^2 + t^2 + eps = 4*r*t + 2*t^2 + eps
    assert(-2 * r * t <= 2 * z_re * d_re && 2 * z_re * d_re <= 2 * r * t)
        by(nonlinear_arith) requires -r <= z_re <= r, -t <= d_re <= t, r > 0, t > 0;
    assert(-2 * r * t <= 2 * z_im * d_im && 2 * z_im * d_im <= 2 * r * t)
        by(nonlinear_arith) requires -r <= z_im <= r, -t <= d_im <= t, r > 0, t > 0;
    assert(0 <= d_re * d_re && d_re * d_re <= t * t)
        by(nonlinear_arith) requires -t <= d_re <= t, t > 0;
    assert(0 <= d_im * d_im && d_im * d_im <= t * t)
        by(nonlinear_arith) requires -t <= d_im <= t, t > 0;

    // Imaginary part: dp_im = 2*z_re*d_im + 2*z_im*d_re + 2*d_re*d_im + dc_im
    assert(-2 * r * t <= 2 * z_re * d_im && 2 * z_re * d_im <= 2 * r * t)
        by(nonlinear_arith) requires -r <= z_re <= r, -t <= d_im <= t, r > 0, t > 0;
    assert(-2 * r * t <= 2 * z_im * d_re && 2 * z_im * d_re <= 2 * r * t)
        by(nonlinear_arith) requires -r <= z_im <= r, -t <= d_re <= t, r > 0, t > 0;
    assert(-2 * t * t <= 2 * d_re * d_im && 2 * d_re * d_im <= 2 * t * t)
        by(nonlinear_arith) requires -t <= d_re <= t, -t <= d_im <= t, t > 0;

    // Combine: give the solver all bounds + definitions in one block
    let dp_re = 2 * z_re * d_re - 2 * z_im * d_im + d_re * d_re - d_im * d_im + dc_re;
    let dp_im = 2 * z_re * d_im + 2 * z_im * d_re + 2 * d_re * d_im + dc_im;
    let bound: int = 4 * r * t + 2 * t * t + eps;

    assert(-bound <= dp_re && dp_re <= bound) by(nonlinear_arith)
        requires
            dp_re == 2 * z_re * d_re - 2 * z_im * d_im + d_re * d_re - d_im * d_im + dc_re,
            bound == 4 * r * t + 2 * t * t + eps,
            -r <= z_re <= r, -r <= z_im <= r,
            -t <= d_re <= t, -t <= d_im <= t,
            -eps <= dc_re <= eps,
            r > 0, t > 0, eps >= 0;

    assert(-bound <= dp_im && dp_im <= bound) by(nonlinear_arith)
        requires
            dp_im == 2 * z_re * d_im + 2 * z_im * d_re + 2 * d_re * d_im + dc_im,
            bound == 4 * r * t + 2 * t * t + eps,
            -r <= z_re <= r, -r <= z_im <= r,
            -t <= d_re <= t, -t <= d_im <= t,
            -eps <= dc_im <= eps,
            r > 0, t > 0, eps >= 0;
}

/// Concrete instantiation: R=2, T=3, eps=1 gives bound=43.
/// 43 fits in a single u32 limb (43 << 2^32), so no overflow.
proof fn corollary_mandelbrot_no_overflow(
    z_re: int, z_im: int,
    d_re: int, d_im: int,
    dc_re: int, dc_im: int,
)
    requires
        -2 <= z_re && z_re <= 2,
        -2 <= z_im && z_im <= 2,
        -3 <= d_re && d_re <= 3,
        -3 <= d_im && d_im <= 3,
        -1 <= dc_re && dc_re <= 1,
        -1 <= dc_im && dc_im <= 1,
    ensures ({
        let dp_re = 2 * z_re * d_re - 2 * z_im * d_im + d_re * d_re - d_im * d_im + dc_re;
        let dp_im = 2 * z_re * d_im + 2 * z_im * d_re + 2 * d_re * d_im + dc_im;
        // Result fits in integer limb of u32 (bound = 43 << 2^32)
        &&& -43 <= dp_re && dp_re <= 43
        &&& -43 <= dp_im && dp_im <= 43
    })
{
    theorem_glitch_detection_soundness(z_re, z_im, d_re, d_im, dc_re, dc_im, 2, 3, 1);
}

} // verus!
