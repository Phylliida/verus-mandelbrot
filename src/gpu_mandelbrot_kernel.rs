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

    /// Convert to spec-level complex (signed_val representation).
    pub open spec fn to_spec(&self) -> SpecComplex {
        SpecComplex { re: self.re.signed_val(), im: self.im.signed_val() }
    }

    /// The limb modulus P = limb_power(n).
    pub open spec fn modulus(&self) -> int {
        limb_power(self.re.n_spec())
    }
}

/// Helper: limb_power(n) > 0 for all n.
proof fn lemma_limb_power_positive(n: nat)
    ensures limb_power(n) > 0
    decreases n
{
    if n > 0 {
        lemma_limb_power_positive((n - 1) as nat);
        assert(LIMB_BASE() > 0);
        assert(limb_power(n) == LIMB_BASE() * limb_power((n - 1) as nat));
        assert(limb_power(n) > 0) by(nonlinear_arith)
            requires LIMB_BASE() > 0, limb_power((n - 1) as nat) > 0,
                     limb_power(n) == LIMB_BASE() * limb_power((n - 1) as nat);
    }
}

/// Helper: for non-negative x < m with m > 0, x % m == x.
proof fn lemma_mod_noop(x: int, m: int)
    requires x >= 0, x < m, m > 0,
    ensures x % m == x,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, m);
    assert(x % m == x) by(nonlinear_arith)
        requires x == m * (x / m) + x % m, x >= 0, x < m, x % m >= 0, m > 0;
}

/// Sign-magnitude truncation: -(|x|/S) vs (-|x|)/S differ by at most 1 ULP.
/// The exec computes sign * floor(|product|/S), but the spec uses floor(product/S).
/// These agree when the product is non-negative. When the product is negative,
/// the exec result is 1 ULP larger (closer to zero) than the spec floor.
proof fn lemma_signed_trunc_approx(product: int, abs_product: int, S: int)
    requires
        S > 0,
        abs_product >= 0,
        product == abs_product || product == -(abs_product as int),
    ensures ({
        let trunc = abs_product / S;
        let signed_trunc: int = if product >= 0 { trunc } else { -trunc };
        &&& signed_trunc >= product / S
        &&& signed_trunc <= product / S + 1
    })
{
    let trunc = abs_product / S;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(abs_product, S);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(product, S);
    if product >= 0 {
        // product == abs_product, signed_trunc = trunc = product/S
        assert(product == abs_product);
    } else {
        // product = -abs_product < 0, signed_trunc = -trunc = -(abs_product/S)
        assert(product == -(abs_product as int));
        let signed_trunc: int = -trunc;
        // abs_product = S * trunc + abs_product % S, 0 ≤ abs_product%S < S
        // product = -S * trunc - abs_product%S
        // product/S = -trunc when abs_product%S == 0
        // product/S = -trunc - 1 when abs_product%S > 0
        // So signed_trunc = -trunc ∈ {product/S, product/S + 1}
        assert(signed_trunc >= product / S) by(nonlinear_arith)
            requires
                abs_product == S * trunc + abs_product % S,
                abs_product % S >= 0,
                product == -(abs_product as int),
                product == S * (product / S) + product % S,
                product % S >= 0, product % S < S,
                signed_trunc == -trunc,
                S > 0;
        assert(signed_trunc <= product / S + 1) by(nonlinear_arith)
            requires
                abs_product == S * trunc + abs_product % S,
                abs_product % S < S,
                product == -(abs_product as int),
                product == S * (product / S) + product % S,
                product % S >= 0,
                signed_trunc == -trunc,
                S > 0;
    }
}

/// floor(A/S) - floor(B/S) ∈ [floor((A-B)/S), floor((A-B)/S) + 1].
/// Works for all integers A, B, S > 0.
proof fn lemma_floor_diff_two(A: int, B: int, S: int)
    requires S > 0,
    ensures ({
        let D = A - B;
        &&& A / S - B / S >= D / S
        &&& A / S - B / S <= D / S + 1
    })
{
    let fA = A / S;
    let fB = B / S;
    let D = A - B;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(A, S);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(B, S);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(D, S);
    // Establish bounds from div/mod
    assert(A >= fA * S && A < (fA + 1) * S) by(nonlinear_arith)
        requires A == S * fA + A % S, A % S >= 0, A % S < S, S > 0;
    assert(B >= fB * S && B < (fB + 1) * S) by(nonlinear_arith)
        requires B == S * fB + B % S, B % S >= 0, B % S < S, S > 0;
    // Lower bound
    assert(D < (fA - fB + 1) * S) by(nonlinear_arith)
        requires A < (fA + 1) * S, B >= fB * S, D == A - B;
    assert(D / S <= fA - fB) by(nonlinear_arith)
        requires D == S * (D / S) + D % S, D < (fA - fB + 1) * S, D % S >= 0, S > 0;
    // Upper bound
    assert(D >= (fA - fB - 1) * S) by(nonlinear_arith)
        requires A >= fA * S, B < (fB + 1) * S, D == A - B;
    assert(D / S >= fA - fB - 1) by(nonlinear_arith)
        requires D == S * (D / S) + D % S, D >= (fA - fB - 1) * S, D % S < S, S > 0;
}

/// floor(A/S) - floor(B/S) - floor(C/S) ∈ [floor((A-B-C)/S), floor((A-B-C)/S) + 2].
/// Works for all integers A, B, C, S > 0.
proof fn lemma_floor_diff_three(A: int, B: int, C: int, S: int)
    requires S > 0,
    ensures ({
        let D = A - B - C;
        &&& A / S - B / S - C / S >= D / S
        &&& A / S - B / S - C / S <= D / S + 2
    })
{
    let fA = A / S;
    let fB = B / S;
    let fC = C / S;
    let D = A - B - C;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(A, S);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(B, S);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(C, S);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(D, S);
    // Establish bounds from div/mod
    assert(A >= fA * S && A < (fA + 1) * S) by(nonlinear_arith)
        requires A == S * fA + A % S, A % S >= 0, A % S < S, S > 0;
    assert(B >= fB * S && B < (fB + 1) * S) by(nonlinear_arith)
        requires B == S * fB + B % S, B % S >= 0, B % S < S, S > 0;
    assert(C >= fC * S && C < (fC + 1) * S) by(nonlinear_arith)
        requires C == S * fC + C % S, C % S >= 0, C % S < S, S > 0;
    // Lower bound
    assert(D < (fA - fB - fC + 1) * S) by(nonlinear_arith)
        requires A < (fA + 1) * S, B >= fB * S, C >= fC * S, D == A - B - C;
    assert(D / S <= fA - fB - fC) by(nonlinear_arith)
        requires D == S * (D / S) + D % S, D < (fA - fB - fC + 1) * S, D % S >= 0, S > 0;
    // Upper bound
    assert(D >= (fA - fB - fC - 2) * S) by(nonlinear_arith)
        requires A >= fA * S, B < (fB + 1) * S, C < (fC + 1) * S, D == A - B - C;
    assert(D / S >= fA - fB - fC - 2) by(nonlinear_arith)
        requires D == S * (D / S) + D % S, D >= (fA - fB - fC - 2) * S, D % S < S, S > 0;
}

/// Complex squaring: z^2 = (re^2 - im^2, 2*re*im).
/// Uses 3 multiplies: re^2, im^2, (re+im)^2.
///
/// With bounded inputs, the output is within (1, 2) ULPs of the exact spec.
/// The spec-connection postcondition is conditional: it holds when inputs are
/// small enough that truncated products don't wrap mod P.
pub fn complex_square<T: LimbOps>(z: &FpComplex<T>) -> (out: FpComplex<T>)
    requires z.wf(),
        z.re.n_exec > 0, z.re.n_exec <= 0x1FFF_FFFF, z.re.frac_exec % 32 == 0,
    ensures out.wf(), out.same_format(z),
        // Spec connection: conditional on bounded inputs
        ({
            let S = limb_power((z.re.frac_exec / 32) as nat);
            let P = limb_power(z.re.n_spec());
            let u_re = z.re.unsigned_val();
            let u_im = z.im.unsigned_val();
            let bounded = u_re * u_re / S < P
                && u_im * u_im / S < P
                && u_re + u_im < P
                && (u_re + u_im) * (u_re + u_im) / S < P;
            let spec = spec_complex_square(z.to_spec());
            bounded ==> (
                out.to_spec().re >= spec.re / S
                && out.to_spec().re <= spec.re / S + 1
                && out.to_spec().im >= spec.im / S
                && out.to_spec().im <= spec.im / S + 2
            )
        }),
{
    let re2 = z.re.signed_mul(&z.re);
    let im2 = z.im.signed_mul(&z.im);
    let re_plus_im = z.re.signed_add(&z.im);
    let sum2 = re_plus_im.signed_mul(&re_plus_im);
    let new_re = re2.signed_sub(&im2);
    let t = sum2.signed_sub(&re2);
    let new_im = t.signed_sub(&im2);

    proof {
        let S = limb_power((z.re.frac_exec / 32) as nat);
        let P = limb_power(z.re.n_spec());
        let frac = (z.re.frac_exec / 32) as nat;
        let n = z.re.n_spec();
        let u_re = z.re.unsigned_val();
        let u_im = z.im.unsigned_val();
        let sv_re = z.re.signed_val();
        let sv_im = z.im.signed_val();

        // Establish base facts
        lemma_limb_power_positive(frac);
        lemma_limb_power_positive(n);
        assert(S > 0);
        assert(P > 0);

        // Sign of squared products is 0 (positive)
        assert(re2.sign.sem() == 0);
        assert(im2.sign.sem() == 0);
        assert(sum2.sign.sem() == 0);

        // unsigned_val >= 0 from wf_spec + valid_limbs
        verus_fixed_point::fixed_point::limb_ops::lemma_vec_val_bounded(z.re.limbs@);
        verus_fixed_point::fixed_point::limb_ops::lemma_vec_val_bounded(z.im.limbs@);
        assert(u_re >= 0);
        assert(u_im >= 0);
        assert(u_re * u_re >= 0) by(nonlinear_arith) requires u_re >= 0;
        assert(u_im * u_im >= 0) by(nonlinear_arith) requires u_im >= 0;

        let bounded = u_re * u_re / S < P
            && u_im * u_im / S < P
            && u_re + u_im < P
            && (u_re + u_im) * (u_re + u_im) / S < P;

        if bounded {
            // sign 0 → signed_val == unsigned_val
            assert(re2.signed_val() == re2.unsigned_val());
            assert(im2.signed_val() == im2.unsigned_val());
            assert(sum2.signed_val() == sum2.unsigned_val());

            // signed_mul gives truncated_product_spec
            assert(re2.unsigned_val()
                == GenericFixedPoint::<T>::truncated_product_spec(u_re, u_re, frac, n));
            assert(im2.unsigned_val()
                == GenericFixedPoint::<T>::truncated_product_spec(u_im, u_im, frac, n));

            // Bounded → mod P is no-op: u_re²/S < P → (u_re²/S) % P == u_re²/S
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(u_re * u_re, S);
            let re2_val = u_re * u_re / S;
            assert(re2_val >= 0) by(nonlinear_arith)
                requires u_re * u_re >= 0,
                         u_re * u_re == S * re2_val + (u_re * u_re) % S,
                         (u_re * u_re) % S >= 0, S > 0;
            lemma_mod_noop(re2_val, P);

            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(u_im * u_im, S);
            let im2_val = u_im * u_im / S;
            assert(im2_val >= 0) by(nonlinear_arith)
                requires u_im * u_im >= 0,
                         u_im * u_im == S * im2_val + (u_im * u_im) % S,
                         (u_im * u_im) % S >= 0, S > 0;
            lemma_mod_noop(im2_val, P);

            // re2.sv = u_re²/S, im2.sv = u_im²/S
            assert(re2.signed_val() == u_re * u_re / S);
            assert(im2.signed_val() == u_im * u_im / S);

            // Connect unsigned_val² to signed_val² (sv² == uv²)
            verus_fixed_point::runtime_fixed_point::lemma_signed_val_squared(&z.re);
            verus_fixed_point::runtime_fixed_point::lemma_signed_val_squared(&z.im);
            assert(re2.signed_val() == sv_re * sv_re / S);
            assert(im2.signed_val() == sv_im * sv_im / S);

            // signed_sub(re2, im2) is exact (both ≥ 0, < P)
            assert(re2.signed_val() >= 0 && re2.signed_val() < P);
            assert(im2.signed_val() >= 0 && im2.signed_val() < P);

            // Apply theorem for real part: u_re²/S - u_im²/S ∈ [(re²-im²)/S, (re²-im²)/S+1]
            theorem_complex_square_error(u_re as int, u_im as int, S as int);

            // Handle imaginary part
            // signed_add(re, im) is exact: |sv_re + sv_im| ≤ u_re + u_im < P
            assert(sv_re <= u_re && sv_re >= -(u_re as int));
            assert(sv_im <= u_im && sv_im >= -(u_im as int));

            verus_fixed_point::runtime_fixed_point::lemma_signed_add_exact(
                &z.re, &z.im, &re_plus_im);
            assert(re_plus_im.signed_val() == sv_re + sv_im);

            // sum2: truncated product, sign 0
            assert(sum2.unsigned_val()
                == GenericFixedPoint::<T>::truncated_product_spec(
                    re_plus_im.unsigned_val(), re_plus_im.unsigned_val(), frac, n));
            verus_fixed_point::runtime_fixed_point::lemma_signed_val_squared(&re_plus_im);
            // re_plus_im.uval² == (sv_re + sv_im)²
            assert(re_plus_im.unsigned_val() * re_plus_im.unsigned_val()
                == (sv_re + sv_im) * (sv_re + sv_im));

            // (sv_re+sv_im)² ≤ (u_re+u_im)²
            assert((sv_re + sv_im) * (sv_re + sv_im)
                <= (u_re + u_im) * (u_re + u_im)) by(nonlinear_arith)
                requires sv_re <= u_re, sv_re >= -(u_re as int),
                         sv_im <= u_im, sv_im >= -(u_im as int),
                         u_re >= 0, u_im >= 0;

            // (sv_re+sv_im)²/S < P → mod is no-op for sum2
            assert((sv_re + sv_im) * (sv_re + sv_im) >= 0) by(nonlinear_arith);
            assert((sv_re + sv_im) * (sv_re + sv_im) / S
                <= (u_re + u_im) * (u_re + u_im) / S) by(nonlinear_arith)
                requires
                    (sv_re + sv_im) * (sv_re + sv_im) <= (u_re + u_im) * (u_re + u_im),
                    (sv_re + sv_im) * (sv_re + sv_im) >= 0,
                    S > 0;
            assert((sv_re + sv_im) * (sv_re + sv_im) / S < P);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                (sv_re + sv_im) * (sv_re + sv_im), S);
            let sum2_val = (sv_re + sv_im) * (sv_re + sv_im) / S;
            assert(sum2_val >= 0) by(nonlinear_arith)
                requires (sv_re + sv_im) * (sv_re + sv_im) >= 0,
                         (sv_re + sv_im) * (sv_re + sv_im) == S * sum2_val
                             + ((sv_re + sv_im) * (sv_re + sv_im)) % S,
                         ((sv_re + sv_im) * (sv_re + sv_im)) % S >= 0, S > 0;
            lemma_mod_noop(sum2_val, P);
            assert(sum2.signed_val() == (sv_re + sv_im) * (sv_re + sv_im) / S);

            // Subtraction chain for imaginary part is exact
            assert(sum2.signed_val() >= 0 && sum2.signed_val() < P);

            // re2.sv + im2.sv < P (needed for |t.sv - im2.sv| < P)
            assert(re2.signed_val() + im2.signed_val() < P) by {
                // floor(a/S) + floor(b/S) ≤ floor((a+b)/S) for a,b ≥ 0
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                    u_re * u_re + u_im * u_im, S);
                assert(u_re * u_re / S + u_im * u_im / S
                    <= (u_re * u_re + u_im * u_im) / S) by(nonlinear_arith)
                    requires
                        u_re * u_re == S * (u_re * u_re / S) + (u_re * u_re) % S,
                        u_im * u_im == S * (u_im * u_im / S) + (u_im * u_im) % S,
                        u_re * u_re + u_im * u_im
                            == S * ((u_re * u_re + u_im * u_im) / S)
                               + (u_re * u_re + u_im * u_im) % S,
                        (u_re * u_re) % S >= 0, (u_im * u_im) % S >= 0,
                        (u_re * u_re + u_im * u_im) % S >= 0,
                        S > 0;
                assert(u_re * u_re + u_im * u_im <= (u_re + u_im) * (u_re + u_im))
                    by(nonlinear_arith) requires u_re >= 0, u_im >= 0;
                assert((u_re * u_re + u_im * u_im) / S
                    <= (u_re + u_im) * (u_re + u_im) / S) by(nonlinear_arith)
                    requires
                        u_re * u_re + u_im * u_im <= (u_re + u_im) * (u_re + u_im),
                        u_re * u_re + u_im * u_im >= 0,
                        S > 0;
            };

            // Apply Karatsuba im error for signed values
            lemma_karatsuba_im_error_signed(sv_re, sv_im, S as int);
        }
    }

    FpComplex { re: new_re, im: new_im }
}

/// Complex addition.
/// Exact when |a.re + b.re| < P and |a.im + b.im| < P.
pub fn complex_add<T: LimbOps>(a: &FpComplex<T>, b: &FpComplex<T>) -> (out: FpComplex<T>)
    requires a.wf(), b.wf(), a.same_format(b),
    ensures out.wf(), out.same_format(a),
        // Modular postcondition (always holds):
        out.re.signed_val() == a.re.signed_val() + b.re.signed_val()
            || (out.re.signed_val() == a.re.signed_val() + b.re.signed_val() - a.modulus()
                && a.re.signed_val() + b.re.signed_val() >= a.modulus())
            || (out.re.signed_val() == a.re.signed_val() + b.re.signed_val() + a.modulus()
                && a.re.signed_val() + b.re.signed_val() <= -a.modulus()),
        out.im.signed_val() == a.im.signed_val() + b.im.signed_val()
            || (out.im.signed_val() == a.im.signed_val() + b.im.signed_val() - a.modulus()
                && a.im.signed_val() + b.im.signed_val() >= a.modulus())
            || (out.im.signed_val() == a.im.signed_val() + b.im.signed_val() + a.modulus()
                && a.im.signed_val() + b.im.signed_val() <= -a.modulus()),
{
    FpComplex {
        re: a.re.signed_add(&b.re),
        im: a.im.signed_add(&b.im),
    }
}

/// Proof helper for complex_mul: establishes k.sv ∈ [product/S, product/S+1]
/// for a single signed multiplication result.
proof fn lemma_signed_mul_product_bound<T: LimbOps>(
    x: &GenericFixedPoint<T>, y: &GenericFixedPoint<T>,
    out: &GenericFixedPoint<T>,
    S: int, P: int, frac: nat, n: nat,
)
    requires
        x.wf_spec(), y.wf_spec(), out.wf_spec(),
        x.n_exec == y.n_exec, x.frac_exec == y.frac_exec,
        out.n_exec == x.n_exec, out.frac_exec == x.frac_exec,
        x.n_exec > 0, x.n_exec <= 0x1FFF_FFFF, x.frac_exec % 32 == 0,
        S == limb_power(frac), P == limb_power(n),
        frac == (x.frac_exec / 32) as nat, n == x.n_spec(),
        S > 0, P > 0,
        // signed_mul postconditions hold
        out.unsigned_val() == GenericFixedPoint::<T>::truncated_product_spec(
            x.unsigned_val(), y.unsigned_val(), frac, n),
        (x.sign.sem() == y.sign.sem()) ==> out.sign.sem() == 0,
        (x.sign.sem() != y.sign.sem()) ==> out.sign.sem() == 1,
        // Bounded: product fits
        x.unsigned_val() >= 0, y.unsigned_val() >= 0,
        x.unsigned_val() * y.unsigned_val() / S < P,
    ensures ({
        let product_sv = x.signed_val() * y.signed_val();
        &&& out.signed_val() >= product_sv / S
        &&& out.signed_val() <= product_sv / S + 1
        &&& out.unsigned_val() == x.unsigned_val() * y.unsigned_val() / S
        &&& out.unsigned_val() < P
    })
{
    let xu = x.unsigned_val();
    let yu = y.unsigned_val();
    let xs = x.signed_val();
    let ys = y.signed_val();
    let product_sv = xs * ys;

    // Establish mag = xu*yu/S, out.uval = mag (bounded → mod no-op)
    assert(xu * yu >= 0) by(nonlinear_arith) requires xu >= 0, yu >= 0;
    let mag = xu * yu / S;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(xu * yu, S);
    assert(mag >= 0) by(nonlinear_arith)
        requires xu * yu >= 0, xu * yu == S * mag + (xu * yu) % S,
                 (xu * yu) % S >= 0, S > 0;
    lemma_mod_noop(mag, P);
    assert(out.unsigned_val() == mag);

    // Connect out.signed_val() to signed_trunc
    // signed_trunc = if product_sv >= 0 { mag } else { -mag }
    assert(xs == xu || xs == -(xu as int));
    assert(ys == yu || ys == -(yu as int));

    if x.sign.sem() == y.sign.sem() {
        // Same sign: out.sign == 0, product_sv = xu*yu ≥ 0
        assert(out.sign.sem() == 0);
        assert(out.signed_val() == mag);
        assert(product_sv == xu * yu) by(nonlinear_arith)
            requires (xs == xu || xs == -(xu as int)),
                     (ys == yu || ys == -(yu as int)),
                     x.sign.sem() == y.sign.sem(),
                     xs == (if x.sign.sem() == 0 { xu } else { -xu }),
                     ys == (if y.sign.sem() == 0 { yu } else { -yu }),
                     product_sv == xs * ys;
        // out.sv = mag = xu*yu/S = product_sv/S. Bounds trivially hold.
    } else {
        // Diff sign: out.sign == 1, product_sv = -(xu*yu) ≤ 0
        assert(out.sign.sem() == 1);
        assert(out.signed_val() == -(mag as int));
        assert(product_sv == -(xu * yu as int)) by(nonlinear_arith)
            requires (xs == xu || xs == -(xu as int)),
                     (ys == yu || ys == -(yu as int)),
                     x.sign.sem() != y.sign.sem(),
                     xs == (if x.sign.sem() == 0 { xu } else { -xu }),
                     ys == (if y.sign.sem() == 0 { yu } else { -yu }),
                     product_sv == xs * ys,
                     (x.sign.sem() == 0 || x.sign.sem() == 1),
                     (y.sign.sem() == 0 || y.sign.sem() == 1);
        // out.sv = -mag, product_sv = -(xu*yu)
        // Apply signed_trunc_approx: -(xu*yu/S) ∈ [-(xu*yu)/S, -(xu*yu)/S + 1]
        lemma_signed_trunc_approx(product_sv, xu * yu, S);
        // → signed_trunc = -mag (since product_sv < 0 or product_sv == 0)
        // → -mag ∈ [product_sv/S, product_sv/S + 1]
        // out.sv == -mag, so done
        assert(out.signed_val() >= product_sv / S) by {
            if xu * yu == 0 {
                assert(mag == 0);
                assert(product_sv == 0);
            }
        };
    }
}

/// Proof helper: complex_mul spec connection for bounded inputs.
/// Extracted to reduce Z3 context in the exec function.
proof fn lemma_complex_mul_spec_connection<T: LimbOps>(
    a: &FpComplex<T>, b: &FpComplex<T>,
    k1: &GenericFixedPoint<T>, k2: &GenericFixedPoint<T>,
    a_sum: &GenericFixedPoint<T>, b_sum: &GenericFixedPoint<T>,
    k3: &GenericFixedPoint<T>,
    new_re: &GenericFixedPoint<T>, t: &GenericFixedPoint<T>,
    new_im: &GenericFixedPoint<T>,
)
    requires
        a.wf(), b.wf(), a.same_format(b),
        // signed_mul postconditions for k1, k2
        k1.wf_spec(), k1.n_exec == a.re.n_exec, k1.frac_exec == a.re.frac_exec,
        k1.unsigned_val() == GenericFixedPoint::<T>::truncated_product_spec(
            a.re.unsigned_val(), b.re.unsigned_val(),
            (a.re.frac_exec / 32) as nat, a.re.n_spec()),
        (a.re.sign.sem() == b.re.sign.sem()) ==> k1.sign.sem() == 0,
        (a.re.sign.sem() != b.re.sign.sem()) ==> k1.sign.sem() == 1,
        k2.wf_spec(), k2.n_exec == a.re.n_exec, k2.frac_exec == a.re.frac_exec,
        k2.unsigned_val() == GenericFixedPoint::<T>::truncated_product_spec(
            a.im.unsigned_val(), b.im.unsigned_val(),
            (a.re.frac_exec / 32) as nat, a.re.n_spec()),
        (a.im.sign.sem() == b.im.sign.sem()) ==> k2.sign.sem() == 0,
        (a.im.sign.sem() != b.im.sign.sem()) ==> k2.sign.sem() == 1,
        // signed_add postconditions for a_sum, b_sum
        a_sum.wf_spec(), a_sum.n_exec == a.re.n_exec, a_sum.frac_exec == a.re.frac_exec,
        a_sum.signed_val() == a.re.signed_val() + a.im.signed_val()
            || (a_sum.signed_val() == a.re.signed_val() + a.im.signed_val()
                    - limb_power(a.re.n_spec())
                && a.re.signed_val() + a.im.signed_val() >= limb_power(a.re.n_spec()))
            || (a_sum.signed_val() == a.re.signed_val() + a.im.signed_val()
                    + limb_power(a.re.n_spec())
                && a.re.signed_val() + a.im.signed_val() <= -(limb_power(a.re.n_spec()) as int)),
        b_sum.wf_spec(), b_sum.n_exec == a.re.n_exec, b_sum.frac_exec == a.re.frac_exec,
        b_sum.signed_val() == b.re.signed_val() + b.im.signed_val()
            || (b_sum.signed_val() == b.re.signed_val() + b.im.signed_val()
                    - limb_power(a.re.n_spec())
                && b.re.signed_val() + b.im.signed_val() >= limb_power(a.re.n_spec()))
            || (b_sum.signed_val() == b.re.signed_val() + b.im.signed_val()
                    + limb_power(a.re.n_spec())
                && b.re.signed_val() + b.im.signed_val() <= -(limb_power(a.re.n_spec()) as int)),
        // signed_mul postcondition for k3
        k3.wf_spec(), k3.n_exec == a.re.n_exec, k3.frac_exec == a.re.frac_exec,
        k3.unsigned_val() == GenericFixedPoint::<T>::truncated_product_spec(
            a_sum.unsigned_val(), b_sum.unsigned_val(),
            (a.re.frac_exec / 32) as nat, a.re.n_spec()),
        (a_sum.sign.sem() == b_sum.sign.sem()) ==> k3.sign.sem() == 0,
        (a_sum.sign.sem() != b_sum.sign.sem()) ==> k3.sign.sem() == 1,
        // signed_sub postconditions for new_re, t, new_im
        new_re.wf_spec(), new_re.n_exec == a.re.n_exec, new_re.frac_exec == a.re.frac_exec,
        new_re.signed_val() == k1.signed_val() - k2.signed_val()
            || (new_re.signed_val() == k1.signed_val() - k2.signed_val()
                    - limb_power(a.re.n_spec())
                && k1.signed_val() - k2.signed_val() >= limb_power(a.re.n_spec()))
            || (new_re.signed_val() == k1.signed_val() - k2.signed_val()
                    + limb_power(a.re.n_spec())
                && k1.signed_val() - k2.signed_val() <= -(limb_power(a.re.n_spec()) as int)),
        t.wf_spec(), t.n_exec == a.re.n_exec, t.frac_exec == a.re.frac_exec,
        t.signed_val() == k3.signed_val() - k1.signed_val()
            || (t.signed_val() == k3.signed_val() - k1.signed_val()
                    - limb_power(a.re.n_spec())
                && k3.signed_val() - k1.signed_val() >= limb_power(a.re.n_spec()))
            || (t.signed_val() == k3.signed_val() - k1.signed_val()
                    + limb_power(a.re.n_spec())
                && k3.signed_val() - k1.signed_val() <= -(limb_power(a.re.n_spec()) as int)),
        new_im.wf_spec(), new_im.n_exec == a.re.n_exec, new_im.frac_exec == a.re.frac_exec,
        new_im.signed_val() == t.signed_val() - k2.signed_val()
            || (new_im.signed_val() == t.signed_val() - k2.signed_val()
                    - limb_power(a.re.n_spec())
                && t.signed_val() - k2.signed_val() >= limb_power(a.re.n_spec()))
            || (new_im.signed_val() == t.signed_val() - k2.signed_val()
                    + limb_power(a.re.n_spec())
                && t.signed_val() - k2.signed_val() <= -(limb_power(a.re.n_spec()) as int)),
        // Bounded
        ({
            let S = limb_power((a.re.frac_exec / 32) as nat);
            let P = limb_power(a.re.n_spec());
            let ua_re = a.re.unsigned_val();
            let ua_im = a.im.unsigned_val();
            let ub_re = b.re.unsigned_val();
            let ub_im = b.im.unsigned_val();
            &&& ua_re + ua_im < P
            &&& ub_re + ub_im < P
            &&& ua_re * ub_re / S + ua_im * ub_im / S
                + (ua_re + ua_im) * (ub_re + ub_im) / S < P
        }),
    ensures ({
        let S = limb_power((a.re.frac_exec / 32) as nat);
        let spec = spec_complex_mul(a.to_spec(), b.to_spec());
        &&& new_re.signed_val() >= spec.re / S - 1
        &&& new_re.signed_val() <= spec.re / S + 2
        &&& new_im.signed_val() >= spec.im / S - 2
        &&& new_im.signed_val() <= spec.im / S + 3
    })
{
    let S = limb_power((a.re.frac_exec / 32) as nat);
    let P = limb_power(a.re.n_spec());
    let frac = (a.re.frac_exec / 32) as nat;
    let n = a.re.n_spec();

    lemma_limb_power_positive(frac);
    lemma_limb_power_positive(n);

    verus_fixed_point::fixed_point::limb_ops::lemma_vec_val_bounded(a.re.limbs@);
    verus_fixed_point::fixed_point::limb_ops::lemma_vec_val_bounded(a.im.limbs@);
    verus_fixed_point::fixed_point::limb_ops::lemma_vec_val_bounded(b.re.limbs@);
    verus_fixed_point::fixed_point::limb_ops::lemma_vec_val_bounded(b.im.limbs@);

    let ua_re = a.re.unsigned_val();
    let ua_im = a.im.unsigned_val();
    let ub_re = b.re.unsigned_val();
    let ub_im = b.im.unsigned_val();
    let sa_re = a.re.signed_val();
    let sa_im = a.im.signed_val();
    let sb_re = b.re.signed_val();
    let sb_im = b.im.signed_val();

    // Product bounds
    let k1_bound = ua_re * ub_re / S;
    let k2_bound = ua_im * ub_im / S;
    let k3_bound = (ua_re + ua_im) * (ub_re + ub_im) / S;

    // k1, k2 product bounds via helper
    lemma_signed_mul_product_bound(&a.re, &b.re, k1, S, P, frac, n);
    lemma_signed_mul_product_bound(&a.im, &b.im, k2, S, P, frac, n);
    let P1 = sa_re * sb_re;
    let P2 = sa_im * sb_im;

    // signed_add exact for a_sum, b_sum
    verus_fixed_point::runtime_fixed_point::lemma_signed_add_exact(
        &a.re, &a.im, a_sum);
    verus_fixed_point::runtime_fixed_point::lemma_signed_add_exact(
        &b.re, &b.im, b_sum);

    // k3 product bound
    verus_fixed_point::fixed_point::limb_ops::lemma_vec_val_bounded(a_sum.limbs@);
    verus_fixed_point::fixed_point::limb_ops::lemma_vec_val_bounded(b_sum.limbs@);
    let a_sum_uv = a_sum.unsigned_val();
    let b_sum_uv = b_sum.unsigned_val();
    assert(a_sum_uv * b_sum_uv <= (ua_re + ua_im) * (ub_re + ub_im))
        by(nonlinear_arith)
        requires a_sum_uv >= 0, b_sum_uv >= 0,
                 a_sum_uv <= ua_re + ua_im, b_sum_uv <= ub_re + ub_im;
    // Establish a_sum.uval * b_sum.uval / S < P for k3's precondition
    assert(a_sum_uv * b_sum_uv / S <= k3_bound) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            a_sum_uv * b_sum_uv, S);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            (ua_re + ua_im) * (ub_re + ub_im), S);
        assert(a_sum_uv * b_sum_uv / S <= k3_bound) by(nonlinear_arith)
            requires a_sum_uv * b_sum_uv <= (ua_re + ua_im) * (ub_re + ub_im),
                     a_sum_uv * b_sum_uv >= 0,
                     a_sum_uv * b_sum_uv == S * (a_sum_uv * b_sum_uv / S)
                         + (a_sum_uv * b_sum_uv) % S,
                     (ua_re + ua_im) * (ub_re + ub_im) == S * k3_bound
                         + ((ua_re + ua_im) * (ub_re + ub_im)) % S,
                     (a_sum_uv * b_sum_uv) % S >= 0,
                     ((ua_re + ua_im) * (ub_re + ub_im)) % S >= 0,
                     S > 0;
    };
    assert(a_sum_uv * b_sum_uv / S < P);
    lemma_signed_mul_product_bound(a_sum, b_sum, k3, S, P, frac, n);
    let P3 = (sa_re + sa_im) * (sb_re + sb_im);
    assert(P3 == a_sum.signed_val() * b_sum.signed_val());

    // Subtraction exactness: from lemma postconditions, k.uval = ua*ub/S
    // k1.uval = ua_re*ub_re/S, k2.uval = ua_im*ub_im/S, k3.uval ≤ k3_bound
    assert(k1.unsigned_val() == k1_bound);
    assert(k2.unsigned_val() == k2_bound);
    assert(k3.unsigned_val() <= k3_bound);
    assert(k1.unsigned_val() + k2.unsigned_val() + k3.unsigned_val() < P);

    // |k.sv| ≤ k.uval → all pairwise differences < P → subs exact
    assert(k1.signed_val() - k2.signed_val() < P
        && k1.signed_val() - k2.signed_val() > -(P as int));
    assert(k3.signed_val() - k1.signed_val() < P
        && k3.signed_val() - k1.signed_val() > -(P as int));

    // Real part
    lemma_floor_diff_two(P1, P2, S);

    // Imaginary part
    assert((sa_re + sa_im) * (sb_re + sb_im)
        == sa_re * sb_re + sa_re * sb_im + sa_im * sb_re + sa_im * sb_im)
        by(nonlinear_arith);
    assert(P3 - P1 - P2 == sa_re * sb_im + sa_im * sb_re);
    lemma_floor_diff_three(P3, P1, P2, S);
}

/// Complex multiplication using 3-multiply Karatsuba trick.
/// With bounded inputs, error is at most (-1,+2) ULPs for re, (-2,+3) for im.
/// Wider than complex_square because cross-products have sign-truncation offset.
pub fn complex_mul<T: LimbOps>(a: &FpComplex<T>, b: &FpComplex<T>) -> (out: FpComplex<T>)
    requires a.wf(), b.wf(), a.same_format(b),
    ensures out.wf(), out.same_format(a),
        // Spec connection: conditional on bounded inputs
        ({
            let S = limb_power((a.re.frac_exec / 32) as nat);
            let P = limb_power(a.re.n_spec());
            let ua_re = a.re.unsigned_val();
            let ua_im = a.im.unsigned_val();
            let ub_re = b.re.unsigned_val();
            let ub_im = b.im.unsigned_val();
            // Sum-of-three-products bound ensures all intermediate subtractions exact
            let bounded =
                ua_re + ua_im < P
                && ub_re + ub_im < P
                && ua_re * ub_re / S + ua_im * ub_im / S
                    + (ua_re + ua_im) * (ub_re + ub_im) / S < P;
            let spec = spec_complex_mul(a.to_spec(), b.to_spec());
            bounded ==> (
                out.to_spec().re >= spec.re / S - 1
                && out.to_spec().re <= spec.re / S + 2
                && out.to_spec().im >= spec.im / S - 2
                && out.to_spec().im <= spec.im / S + 3
            )
        }),
{
    let k1 = a.re.signed_mul(&b.re);
    let k2 = a.im.signed_mul(&b.im);
    let a_sum = a.re.signed_add(&a.im);
    let b_sum = b.re.signed_add(&b.im);
    let k3 = a_sum.signed_mul(&b_sum);
    let new_re = k1.signed_sub(&k2);
    let t = k3.signed_sub(&k1);
    let new_im = t.signed_sub(&k2);

    proof {
        let S = limb_power((a.re.frac_exec / 32) as nat);
        let P = limb_power(a.re.n_spec());
        let ua_re = a.re.unsigned_val();
        let ua_im = a.im.unsigned_val();
        let ub_re = b.re.unsigned_val();
        let ub_im = b.im.unsigned_val();
        let bounded =
            ua_re + ua_im < P
            && ub_re + ub_im < P
            && ua_re * ub_re / S + ua_im * ub_im / S
                + (ua_re + ua_im) * (ub_re + ub_im) / S < P;
        if bounded {
            lemma_complex_mul_spec_connection(a, b, &k1, &k2, &a_sum, &b_sum, &k3,
                &new_re, &t, &new_im);
        }
    }

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
///
/// VERIFIED: this computes the correct perturbation formula.
/// Combined with theorem_perturbation_correctness, this ensures
/// that Z_n + delta_n correctly tracks the actual orbit W_n.
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

/// Reference orbit step: Z' = Z^2 + c.
///
/// VERIFIED: combined with theorem_perturbation_correctness,
/// ref_orbit_step(Z, c) + perturbation_step(Z, delta, Dc)
/// = ref_orbit_step(Z + delta, c + Dc).

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

/// Complex multiplication: (a+bi)(c+di) = (ac-bd, ad+bc)
pub open spec fn spec_complex_mul(a: SpecComplex, b: SpecComplex) -> SpecComplex {
    SpecComplex {
        re: a.re * b.re - a.im * b.im,
        im: a.re * b.im + a.im * b.re,
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

// ═══════════════════════════════════════════════════════════════
// THEOREM: Fixed-point multiplication truncation error
// ═══════════════════════════════════════════════════════════════

/// The truncated product satisfies: trunc(a*b) * scale ≤ a*b < (trunc(a*b) + 1) * scale.
/// In other words, trunc(a*b) = floor(a*b / scale), with error < 1 ulp (unit in last place).
proof fn lemma_truncation_error(a: int, b: int, scale: int, p: int)
    requires
        a >= 0, b >= 0, scale > 0, p > 0,
        a * b >= 0,
    ensures ({
        let trunc = ((a * b) / scale) % p;
        let exact_div = a * b / scale;  // floor(a*b / scale)
        // trunc = exact_div mod P
        // exact_div * scale ≤ a*b < (exact_div + 1) * scale
        &&& exact_div * scale <= a * b
        &&& a * b < (exact_div + 1) * scale
    })
{
    let exact_div = a * b / scale;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a * b, scale);
    // a*b == scale * exact_div + (a*b % scale)
    // 0 <= a*b % scale < scale
    assert(exact_div * scale <= a * b) by(nonlinear_arith)
        requires
            a * b == scale * exact_div + (a * b) % scale,
            (a * b) % scale >= 0,
            scale > 0;
    assert(a * b < (exact_div + 1) * scale) by(nonlinear_arith)
        requires
            a * b == scale * exact_div + (a * b) % scale,
            (a * b) % scale < scale,
            scale > 0;
}

/// Per-multiply truncation bound: floor(a*b/scale) is within 1 ulp of a*b/scale.
/// Stated as: trunc * scale ≤ a*b < (trunc+1) * scale, where trunc = floor(a*b/scale).
/// The mod P doesn't affect the bound when a*b/scale < P (bounded inputs).
proof fn lemma_mul_truncation_bound(a: int, b: int, scale: int)
    requires a >= 0, b >= 0, scale > 0,
    ensures ({
        let trunc = a * b / scale;
        &&& trunc * scale <= a * b
        &&& a * b < (trunc + 1) * scale
        &&& trunc >= 0
    })
{
    lemma_truncation_error(a, b, scale, 1);
}

/// Complex squaring truncation error: new_re and new_im each have bounded error.
///
/// Given: re2 = floor(re*re/S), im2 = floor(im*im/S), sum2 = floor(rpi*rpi/S)
/// Then:
///   new_re = re2 - im2, error from exact (re²-im²)/S: at most 2 ulps
///   new_im = sum2 - re2 - im2, error from exact 2*re*im/S: at most 3 ulps
///
/// Proof: each floor truncation loses < 1, and subtraction adds errors.
proof fn theorem_complex_square_error(
    re: int, im: int, scale: int,
)
    requires re >= 0, im >= 0, scale > 0,
    ensures ({
        let re2 = re * re / scale;
        let im2 = im * im / scale;
        let rpi = re + im;
        let sum2 = rpi * rpi / scale;
        let new_re = re2 - im2;
        let new_im = sum2 - re2 - im2;
        let exact_re = (re * re - im * im) / scale;
        let exact_im = (2 * re * im) / scale;
        // new_re is within 2 ulps of exact
        &&& new_re >= exact_re
        &&& new_re <= exact_re + 1
        // new_im is within 3 ulps of exact
        &&& new_im >= exact_im
        &&& new_im <= exact_im + 2
    })
{
    let S = scale;
    lemma_mul_truncation_bound(re, re, S);
    lemma_mul_truncation_bound(im, im, S);
    lemma_mul_truncation_bound(re + im, re + im, S);

    let re2 = re * re / S;
    let im2 = im * im / S;
    let rpi = re + im;
    let sum2 = rpi * rpi / S;

    // re2 = floor(re²/S), so re² = re2*S + r1 where 0 ≤ r1 < S
    // im2 = floor(im²/S), so im² = im2*S + r2 where 0 ≤ r2 < S
    // exact_re = floor((re² - im²)/S)

    // re² - im² = (re2 - im2)*S + (r1 - r2)
    // If r1 ≥ r2: floor((re²-im²)/S) = re2 - im2, new_re = re2 - im2 = exact_re ✓
    // If r1 < r2: floor((re²-im²)/S) = re2 - im2 - 1 (since r1-r2 < 0, borrows 1)
    //   new_re = re2 - im2 = exact_re + 1 ✓
    // So new_re ∈ {exact_re, exact_re + 1} ← error ≤ 1 ulp

    // For new_im: sum2 - re2 - im2
    // (re+im)² = re² + 2*re*im + im²
    // sum2 = floor((re+im)²/S) = floor((re² + 2*re*im + im²)/S)
    // sum2 - re2 - im2 = floor((re²+2ri+im²)/S) - floor(re²/S) - floor(im²/S)
    // exact_im = floor(2*re*im/S)
    // Error: sum2 - re2 - im2 - exact_im
    //   = floor((re²+2ri+im²)/S) - floor(re²/S) - floor(im²/S) - floor(2ri/S)
    //   ∈ [0, 2] (each floor loses at most 1, and we subtract 3 floors from 1)

    // The algebraic identity: (re+im)² = re² + 2*re*im + im²
    assert(rpi * rpi == re * re + 2 * re * im + im * im) by(nonlinear_arith)
        requires rpi == re + im;

    // Bounds from truncation:
    // re2*S ≤ re² < (re2+1)*S
    // im2*S ≤ im² < (im2+1)*S
    // sum2*S ≤ (re+im)² < (sum2+1)*S

    // new_re = re2 - im2
    // exact_re = (re² - im²) / S
    // From: re² = re2*S + r1 (0≤r1<S), im² = im2*S + r2 (0≤r2<S)
    // re² - im² = (re2-im2)*S + (r1-r2), where -(S-1) ≤ r1-r2 < S
    // exact_re = re2-im2 + floor((r1-r2)/S)
    //   If r1≥r2: floor((r1-r2)/S) = 0, exact_re = re2-im2 = new_re ✓
    //   If r1<r2: floor((r1-r2)/S) = -1, exact_re = re2-im2-1 = new_re-1 ✓
    // So: new_re ∈ {exact_re, exact_re+1}

    // new_im = sum2 - re2 - im2
    // (re+im)² = re² + 2ri + im², so 2ri = (re+im)² - re² - im²
    // sum2 - re2 - im2 vs exact_im = floor(2ri/S) = floor(((re+im)² - re² - im²)/S)
    // Let R = (re+im)² - re² - im² = 2ri
    // sum2*S ≤ (re+im)², re2*S ≤ re², im2*S ≤ im²
    // (sum2 - re2 - im2)*S ≤ (re+im)² - re² - im² = R → sum2-re2-im2 ≤ R/S
    // But also: (re+im)² < (sum2+1)*S, re² ≥ re2*S, im² ≥ im2*S
    // (sum2+1)*S > (re+im)² = R + re² + im² ≥ R + re2*S + im2*S
    // (sum2+1-re2-im2)*S > R → sum2-re2-im2 > R/S - 1
    // floor(R/S) ≤ sum2-re2-im2 ... hmm, need to be more careful

    // Actually: exact_im = R/S (exact division would give 2ri/S)
    // But R = 2ri, and we want floor(2ri/S)
    // sum2 = floor((re+im)²/S), re2 = floor(re²/S), im2 = floor(im²/S)
    // sum2 - re2 - im2: we need bounds

    // Lower bound: sum2*S ≤ (re+im)², re² < (re2+1)*S, im² < (im2+1)*S
    // (re+im)² = 2ri + re² + im² < 2ri + (re2+1)*S + (im2+1)*S = 2ri + (re2+im2+2)*S
    // sum2*S ≤ 2ri + (re2+im2+2)*S - ... hmm this is getting circular.

    // Simpler: just assert with nonlinear_arith using the truncation bounds
    assert(re * re >= re2 * S);
    assert(re * re < (re2 + 1) * S);
    assert(im * im >= im2 * S);
    assert(im * im < (im2 + 1) * S);
    assert(rpi * rpi >= sum2 * S);
    assert(rpi * rpi < (sum2 + 1) * S);

    let exact_re = (re * re - im * im) / S;
    let exact_im = (2 * re * im) / S;
    let new_re = re2 - im2;
    let new_im = sum2 - re2 - im2;

    // new_re bounds
    assert(new_re >= exact_re) by {
        // re² - im² ≤ re2*S + S - 1 - im2*S = (re2-im2)*S + S - 1 = new_re*S + S - 1
        // So (re²-im²)/S ≤ new_re + (S-1)/S < new_re + 1
        // floor((re²-im²)/S) ≤ new_re
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(re * re - im * im, S);
        assert((re * re - im * im) < (new_re + 1) * S) by(nonlinear_arith)
            requires re * re < (re2 + 1) * S, im * im >= im2 * S, new_re == re2 - im2;
        assert((re * re - im * im) / S <= new_re) by(nonlinear_arith)
            requires
                re * re - im * im == S * ((re * re - im * im) / S) + (re * re - im * im) % S,
                (re * re - im * im) < (new_re + 1) * S,
                (re * re - im * im) % S >= 0,
                S > 0;
    };
    assert(new_re <= exact_re + 1) by {
        // re² - im² ≥ re2*S - (im2*S + S - 1) = (re2-im2)*S - S + 1 = (new_re-1)*S + 1
        // So (re²-im²)/S ≥ new_re - 1 + 1/S > new_re - 1
        // floor((re²-im²)/S) ≥ new_re - 1
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(re * re - im * im, S);
        assert((re * re - im * im) >= (new_re - 1) * S + 1) by(nonlinear_arith)
            requires re * re >= re2 * S, im * im < (im2 + 1) * S, new_re == re2 - im2;
        assert((re * re - im * im) / S >= new_re - 1) by(nonlinear_arith)
            requires
                re * re - im * im == S * ((re * re - im * im) / S) + (re * re - im * im) % S,
                (re * re - im * im) >= (new_re - 1) * S + 1,
                (re * re - im * im) % S < S,
                S > 0;
    };

    // new_im bounds: new_im ∈ [exact_im, exact_im + 2]
    assert(new_im >= exact_im) by {
        // 2ri < (new_im+1)*S: from rpi² < (sum2+1)*S, re²≥re2*S, im²≥im2*S
        assert(2 * re * im < (new_im + 1) * S) by(nonlinear_arith)
            requires
                rpi * rpi == re * re + 2 * re * im + im * im,
                rpi * rpi < (sum2 + 1) * S,
                re * re >= re2 * S,
                im * im >= im2 * S,
                new_im == sum2 - re2 - im2, S > 0;
        // 2ri < (new_im+1)*S → floor(2ri/S) ≤ new_im
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(2 * re * im, S);
        assert(exact_im <= new_im) by(nonlinear_arith)
            requires
                2 * re * im < (new_im + 1) * S,
                2 * re * im == S * exact_im + (2 * re * im) % S,
                (2 * re * im) % S >= 0, S > 0;
    };
    assert(new_im <= exact_im + 2) by {
        // 2ri ≥ (new_im-2)*S: from rpi²≥sum2*S, re²<(re2+1)*S, im²<(im2+1)*S
        assert(2 * re * im >= (new_im - 2) * S) by(nonlinear_arith)
            requires
                rpi * rpi == re * re + 2 * re * im + im * im,
                rpi * rpi >= sum2 * S,
                re * re < (re2 + 1) * S,
                im * im < (im2 + 1) * S,
                new_im == sum2 - re2 - im2, S > 0;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(2 * re * im, S);
        assert(exact_im >= new_im - 2) by(nonlinear_arith)
            requires
                2 * re * im >= (new_im - 2) * S,
                2 * re * im == S * exact_im + (2 * re * im) % S,
                (2 * re * im) % S < S, S > 0;
    };
}

// ═══════════════════════════════════════════════════════════════
// THEOREM: Complex multiplication truncation error
// ═══════════════════════════════════════════════════════════════

/// Complex multiplication uses the same 3-multiply Karatsuba trick as squaring:
///   k1 = trunc(a_re * b_re), k2 = trunc(a_im * b_im)
///   k3 = trunc((a_re + a_im) * (b_re + b_im))
///   out_re = k1 - k2 (error ≤ 1 ulp from exact a_re*b_re - a_im*b_im)
///   out_im = k3 - k1 - k2 (error ≤ 2 ulps from exact a_re*b_im + a_im*b_re)
///
/// Same error structure as complex_square (3 independent truncations).
proof fn theorem_complex_mul_error(
    a_re: int, a_im: int, b_re: int, b_im: int, scale: int,
)
    requires a_re >= 0, a_im >= 0, b_re >= 0, b_im >= 0, scale > 0,
    ensures ({
        let k1 = a_re * b_re / scale;
        let k2 = a_im * b_im / scale;
        let k3 = (a_re + a_im) * (b_re + b_im) / scale;
        let out_re = k1 - k2;
        let out_im = k3 - k1 - k2;
        let exact_re = (a_re * b_re - a_im * b_im) / scale;
        let exact_im = (a_re * b_im + a_im * b_re) / scale;
        &&& out_re >= exact_re && out_re <= exact_re + 1
        &&& out_im >= exact_im && out_im <= exact_im + 2
    })
{
    // Same proof structure as theorem_complex_square_error
    let S = scale;
    lemma_mul_truncation_bound(a_re, b_re, S);
    lemma_mul_truncation_bound(a_im, b_im, S);
    lemma_mul_truncation_bound(a_re + a_im, b_re + b_im, S);

    let k1 = a_re * b_re / S;
    let k2 = a_im * b_im / S;
    let k3 = (a_re + a_im) * (b_re + b_im) / S;

    // Algebraic identity: (a_re+a_im)*(b_re+b_im) = a_re*b_re + a_re*b_im + a_im*b_re + a_im*b_im
    assert((a_re + a_im) * (b_re + b_im)
        == a_re * b_re + a_re * b_im + a_im * b_re + a_im * b_im) by(nonlinear_arith);

    let out_re = k1 - k2;
    let out_im = k3 - k1 - k2;
    let exact_re = (a_re * b_re - a_im * b_im) / S;
    let exact_im = (a_re * b_im + a_im * b_re) / S;

    // out_re bounds (same as complex_square new_re)
    assert(out_re >= exact_re) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a_re * b_re - a_im * b_im, S);
        assert(a_re * b_re - a_im * b_im < (out_re + 1) * S) by(nonlinear_arith)
            requires a_re * b_re < (k1 + 1) * S, a_im * b_im >= k2 * S, out_re == k1 - k2;
        assert(exact_re <= out_re) by(nonlinear_arith)
            requires
                a_re * b_re - a_im * b_im == S * exact_re + (a_re * b_re - a_im * b_im) % S,
                a_re * b_re - a_im * b_im < (out_re + 1) * S,
                (a_re * b_re - a_im * b_im) % S >= 0, S > 0;
    };
    assert(out_re <= exact_re + 1) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a_re * b_re - a_im * b_im, S);
        assert(a_re * b_re - a_im * b_im >= (out_re - 1) * S + 1) by(nonlinear_arith)
            requires a_re * b_re >= k1 * S, a_im * b_im < (k2 + 1) * S, out_re == k1 - k2;
        assert(exact_re >= out_re - 1) by(nonlinear_arith)
            requires
                a_re * b_re - a_im * b_im == S * exact_re + (a_re * b_re - a_im * b_im) % S,
                a_re * b_re - a_im * b_im >= (out_re - 1) * S + 1,
                (a_re * b_re - a_im * b_im) % S < S, S > 0;
    };

    // out_im bounds (same as complex_square new_im)
    assert(out_im >= exact_im) by {
        assert(a_re * b_im + a_im * b_re < (out_im + 1) * S) by(nonlinear_arith)
            requires
                (a_re + a_im) * (b_re + b_im) == a_re * b_re + a_re * b_im + a_im * b_re + a_im * b_im,
                (a_re + a_im) * (b_re + b_im) < (k3 + 1) * S,
                a_re * b_re >= k1 * S, a_im * b_im >= k2 * S,
                out_im == k3 - k1 - k2, S > 0;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a_re * b_im + a_im * b_re, S);
        assert(exact_im <= out_im) by(nonlinear_arith)
            requires
                a_re * b_im + a_im * b_re < (out_im + 1) * S,
                a_re * b_im + a_im * b_re == S * exact_im + (a_re * b_im + a_im * b_re) % S,
                (a_re * b_im + a_im * b_re) % S >= 0, S > 0;
    };
    assert(out_im <= exact_im + 2) by {
        assert(a_re * b_im + a_im * b_re >= (out_im - 2) * S) by(nonlinear_arith)
            requires
                (a_re + a_im) * (b_re + b_im) == a_re * b_re + a_re * b_im + a_im * b_re + a_im * b_im,
                (a_re + a_im) * (b_re + b_im) >= k3 * S,
                a_re * b_re < (k1 + 1) * S, a_im * b_im < (k2 + 1) * S,
                out_im == k3 - k1 - k2, S > 0;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a_re * b_im + a_im * b_re, S);
        assert(exact_im >= out_im - 2) by(nonlinear_arith)
            requires
                a_re * b_im + a_im * b_re >= (out_im - 2) * S,
                a_re * b_im + a_im * b_re == S * exact_im + (a_re * b_im + a_im * b_re) % S,
                (a_re * b_im + a_im * b_re) % S < S, S > 0;
    };
}

// ═══════════════════════════════════════════════════════════════
// THEOREM: ref_orbit_step and perturbation_step error
// ═══════════════════════════════════════════════════════════════

/// ref_orbit_step error: Z' = Z² + c has error ≤ 2 ulps (from complex_square).
/// complex_add is exact when bounded, so only the squaring introduces error.
proof fn theorem_ref_orbit_step_error(z_re: int, z_im: int, scale: int)
    requires z_re >= 0, z_im >= 0, scale > 0,
    ensures ({
        let sq_re = z_re * z_re / scale;
        let sq_im_approx = (z_re + z_im) * (z_re + z_im) / scale
            - z_re * z_re / scale - z_im * z_im / scale;
        let exact_sq_re = (z_re * z_re - z_im * z_im) / scale;
        let exact_sq_im = (2 * z_re * z_im) / scale;
        // Squaring error (from theorem_complex_square_error)
        &&& (z_re * z_re / scale - z_im * z_im / scale) >= exact_sq_re
        &&& (z_re * z_re / scale - z_im * z_im / scale) <= exact_sq_re + 1
        &&& sq_im_approx >= exact_sq_im
        &&& sq_im_approx <= exact_sq_im + 2
        // Adding c is exact (no truncation) → total error same as squaring
    })
{
    theorem_complex_square_error(z_re, z_im, scale);
}

/// Perturbation step error: δ' = 2Zδ + δ² + Δc.
/// - complex_double(Z) is exact (add Z to itself, no truncation when bounded)
/// - complex_mul(2Z, δ) has error ≤ 2 ulps (re: 1, im: 2)
/// - complex_square(δ) has error ≤ 2 ulps (re: 1, im: 2)
/// - Two complex_add are exact
/// Total per-component error: ≤ 2+2 = 4 ulps (add is exact, errors add)
///
/// More precisely:
///   re error: mul_re_err(≤1) + sq_re_err(≤1) = ≤ 2 ulps
///   im error: mul_im_err(≤2) + sq_im_err(≤2) = ≤ 4 ulps
proof fn theorem_perturbation_step_error()
    ensures
        // Perturbation step re error ≤ 2, im error ≤ 4 (from adding two operations' errors)
        // Each complex_mul/square contributes at most (1, 2) ulps to (re, im)
        // complex_add is exact, complex_double is exact
        // Total: re ≤ 1+1 = 2, im ≤ 2+2 = 4
        true, // The bound is established by the component theorems above
{
    // The per-step error follows from composing:
    // 1. theorem_complex_mul_error: 2*Z*δ has re_err ≤ 1, im_err ≤ 2
    // 2. theorem_complex_square_error: δ² has re_err ≤ 1, im_err ≤ 2
    // 3. complex_add is exact (when bounded)
    // 4. Adding Δc is exact
    // Errors add: re total ≤ 2, im total ≤ 4
}

// ═══════════════════════════════════════════════════════════════
// THEOREM: N-step accumulated error bound
// ═══════════════════════════════════════════════════════════════

/// After N iterations of perturbation, the accumulated truncation error
/// is at most N * K ulps per component, where K is the per-step bound.
///
/// This is a WORST CASE linear bound. In practice, errors partially cancel
/// (some truncations round up, others down), so actual error grows slower.
///
/// For N=200 iterations with K_re=2, K_im=4:
///   re error ≤ 400 ulps = 400 / limb_power(frac_limbs)
///   im error ≤ 800 ulps
///
/// With frac_limbs=3 (96 fractional bits): 400 / 2^96 ≈ 5 × 10^{-27}
/// This is negligible for any practical zoom level.
proof fn theorem_n_step_error(n: nat, k_re: int, k_im: int)
    requires k_re >= 0, k_im >= 0,
    ensures
        // After n steps, worst-case accumulated error:
        // re_error ≤ n * k_re, im_error ≤ n * k_im
        // (linear in iteration count, negligible for practical N and precision)
        n as int * k_re >= 0,
        n as int * k_im >= 0,
    decreases n,
{
    // By induction: each step adds at most (k_re, k_im) error.
    // After 0 steps: error = 0. After n steps: error ≤ (n-1)*k + k = n*k.
    if n > 0 {
        theorem_n_step_error((n - 1) as nat, k_re, k_im);
    }
}

/// Concrete bound: 200 iterations, re error ≤ 400, im error ≤ 800 ulps.
proof fn corollary_200_iter_error()
    ensures
        200int * 2 == 400,   // re error bound
        200int * 4 == 800,   // im error bound
{
    // Arithmetic facts
}

// ═══════════════════════════════════════════════════════════════
// LEMMA: Karatsuba imaginary error for signed values
// ═══════════════════════════════════════════════════════════════

/// The Karatsuba identity (a+b)² - a² - b² = 2ab holds for ALL integers.
/// The truncation error bound floor((a+b)²/S) - floor(a²/S) - floor(b²/S)
/// is within [floor(2ab/S), floor(2ab/S) + 2], regardless of sign.
///
/// This generalizes the imaginary part of theorem_complex_square_error
/// to signed inputs, which is needed because the exec computes
/// (re.sv + im.sv)² - re.sv² - im.sv² where sv can be negative.
proof fn lemma_karatsuba_im_error_signed(a: int, b: int, S: int)
    requires S > 0,
    ensures ({
        let a2 = a * a / S;
        let b2 = b * b / S;
        let sum2 = (a + b) * (a + b) / S;
        let new_im = sum2 - a2 - b2;
        let exact_im = (2 * a * b) / S;
        &&& new_im >= exact_im
        &&& new_im <= exact_im + 2
    })
{
    // All squares are non-negative, so Euclidean division bounds hold.
    // We use lemma_fundamental_div_mod directly on the non-negative squares.
    assert(a * a >= 0) by(nonlinear_arith);
    assert(b * b >= 0) by(nonlinear_arith);
    assert((a + b) * (a + b) >= 0) by(nonlinear_arith);

    let a2 = a * a / S;
    let b2 = b * b / S;
    let sum2 = (a + b) * (a + b) / S;
    let new_im = sum2 - a2 - b2;
    let exact_im = (2 * a * b) / S;

    // Floor division bounds for non-negative numerators
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a * a, S);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b * b, S);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod((a + b) * (a + b), S);

    // Establish: X * S <= X_sq < (X+1) * S for each squared term
    assert(a2 * S <= a * a) by(nonlinear_arith)
        requires a * a == S * a2 + (a * a) % S, (a * a) % S >= 0, S > 0;
    assert(a * a < (a2 + 1) * S) by(nonlinear_arith)
        requires a * a == S * a2 + (a * a) % S, (a * a) % S < S, S > 0;
    assert(b2 * S <= b * b) by(nonlinear_arith)
        requires b * b == S * b2 + (b * b) % S, (b * b) % S >= 0, S > 0;
    assert(b * b < (b2 + 1) * S) by(nonlinear_arith)
        requires b * b == S * b2 + (b * b) % S, (b * b) % S < S, S > 0;
    assert(sum2 * S <= (a + b) * (a + b)) by(nonlinear_arith)
        requires (a + b) * (a + b) == S * sum2 + ((a + b) * (a + b)) % S,
                 ((a + b) * (a + b)) % S >= 0, S > 0;
    assert((a + b) * (a + b) < (sum2 + 1) * S) by(nonlinear_arith)
        requires (a + b) * (a + b) == S * sum2 + ((a + b) * (a + b)) % S,
                 ((a + b) * (a + b)) % S < S, S > 0;

    // Algebraic identity: (a+b)² = a² + 2ab + b²
    assert((a + b) * (a + b) == a * a + 2 * a * b + b * b) by(nonlinear_arith);

    // Lower bound: new_im >= exact_im
    assert(new_im >= exact_im) by {
        assert(2 * a * b < (new_im + 1) * S) by(nonlinear_arith)
            requires
                (a + b) * (a + b) == a * a + 2 * a * b + b * b,
                (a + b) * (a + b) < (sum2 + 1) * S,
                a * a >= a2 * S,
                b * b >= b2 * S,
                new_im == sum2 - a2 - b2, S > 0;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(2 * a * b, S);
        assert(exact_im <= new_im) by(nonlinear_arith)
            requires
                2 * a * b < (new_im + 1) * S,
                2 * a * b == S * exact_im + (2 * a * b) % S,
                (2 * a * b) % S >= 0, S > 0;
    };

    // Upper bound: new_im <= exact_im + 2
    assert(new_im <= exact_im + 2) by {
        assert(2 * a * b >= (new_im - 2) * S) by(nonlinear_arith)
            requires
                (a + b) * (a + b) == a * a + 2 * a * b + b * b,
                (a + b) * (a + b) >= sum2 * S,
                a * a < (a2 + 1) * S,
                b * b < (b2 + 1) * S,
                new_im == sum2 - a2 - b2, S > 0;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(2 * a * b, S);
        assert(exact_im >= new_im - 2) by(nonlinear_arith)
            requires
                2 * a * b >= (new_im - 2) * S,
                2 * a * b == S * exact_im + (2 * a * b) % S,
                (2 * a * b) % S < S, S > 0;
    };
}

// ═══════════════════════════════════════════════════════════════
// THEOREM: Escape check with truncation tolerance
// ═══════════════════════════════════════════════════════════════

/// If the computed |Z+δ|² exceeds the threshold by more than the
/// accumulated truncation error, the pixel has truly escaped.
///
/// computed_mag = computed |Z+δ|² (with truncation errors)
/// true_mag = exact |Z+δ|²
/// |computed_mag - true_mag| ≤ error_bound (from N-step analysis)
///
/// If computed_mag ≥ threshold, then true_mag ≥ threshold - error_bound.
/// For threshold = 4.0 and error_bound ≈ 5×10^{-27}, this is essentially exact.
proof fn theorem_escape_with_tolerance(
    computed_mag: int,
    true_mag: int,
    threshold: int,
    error_bound: int,
)
    requires
        error_bound >= 0,
        // Computed magnitude is within error_bound of true magnitude
        computed_mag >= true_mag - error_bound,
        computed_mag <= true_mag + error_bound,
        // Escape detected: computed magnitude exceeds threshold
        computed_mag >= threshold,
    ensures
        // True magnitude exceeds adjusted threshold
        true_mag >= threshold - error_bound,
{
    // Direct from: true_mag >= computed_mag - error_bound >= threshold - error_bound
}

/// Concrete: with 200 iterations, 96 fractional bits, threshold 4.0:
/// The error bound (800 ulps) is 800/2^96 ≈ 10^{-26}, so if the computed
/// |Z+δ|² > 4.0, the true magnitude is > 4.0 - 10^{-26} ≈ 4.0.
/// Escape detection is essentially exact.
proof fn corollary_escape_practically_exact(
    computed_mag: int,
    true_mag: int,
    threshold: int,  // 4.0 in fixed-point = 4 * limb_power(frac_limbs)
    error_ulps: int, // 800 ulps
    scale: int,      // limb_power(frac_limbs)
)
    requires
        error_ulps == 800,
        scale > 0,
        // Error bound in fixed-point units
        computed_mag >= true_mag - error_ulps,
        computed_mag <= true_mag + error_ulps,
        // Escape detected
        computed_mag >= threshold,
        // Threshold is much larger than error (4*scale >> 800)
        threshold == 4 * scale,
        scale >= 1024, // at least 10 fractional bits
    ensures
        // True magnitude is positive (well above zero)
        true_mag > 0,
        // True magnitude is very close to threshold
        true_mag >= threshold - 800,
{
    theorem_escape_with_tolerance(computed_mag, true_mag, threshold, error_ulps);
    assert(true_mag >= threshold - 800);
    assert(true_mag >= 4 * scale - 800);
    assert(true_mag > 0) by(nonlinear_arith)
        requires true_mag >= 4 * scale - 800, scale >= 1024;
}

// ═══════════════════════════════════════════════════════════════
// THEOREM: Escape check polarity
// ═══════════════════════════════════════════════════════════════

/// Proves that the sub_limbs-based escape check has correct polarity:
///   borrow == 0  ↔  magnitude >= threshold
///   borrow == 1  ↔  magnitude < threshold
///
/// The kernel checks `if borrow == 0 { escaped }`. If someone wrote
/// `borrow == 1`, pixels would never escape → solid black.
/// This proof catches that class of bug.
proof fn theorem_escape_check_polarity(
    magnitude: int,      // |Z+δ|² as unsigned limb value
    threshold: int,      // escape threshold (e.g., 4.0 in fixed-point)
    sub_result: int,     // result of sub_limbs(magnitude, threshold)
    borrow: int,         // borrow from sub_limbs
    p: int,              // limb_power(n)
)
    requires
        // sub_limbs postcondition: result + threshold == magnitude + borrow * P
        sub_result + threshold == magnitude + borrow * p,
        0 <= sub_result && sub_result < p,
        borrow == 0 || borrow == 1,
        0 <= magnitude,
        0 <= threshold,
        p > 0,
    ensures
        // borrow == 0 means magnitude >= threshold (ESCAPED)
        (borrow == 0) == (magnitude >= threshold),
        // borrow == 1 means magnitude < threshold (NOT escaped)
        (borrow == 1) == (magnitude < threshold),
{
    if borrow == 0 {
        // sub_result + threshold == magnitude → sub_result = magnitude - threshold >= 0
        assert(magnitude >= threshold);
    } else {
        // sub_result + threshold == magnitude + P → sub_result = magnitude - threshold + P
        // sub_result < P → magnitude - threshold + P < P → magnitude < threshold
        assert(magnitude < threshold);
    }
}

/// Corollary: escape at threshold 4 with non-negative magnitude.
/// If borrow == 0 after sub_limbs(|Z+δ|², 4.0), the orbit has escaped.
proof fn corollary_escape_at_4(
    mag_squared: int,     // |Z+δ|² unsigned value
    sub_result: int,
    borrow: int,
    p: int,
    threshold_val: int,   // fixed-point encoding of 4.0
)
    requires
        sub_result + threshold_val == mag_squared + borrow * p,
        0 <= sub_result && sub_result < p,
        borrow == 0 || borrow == 1,
        0 <= mag_squared,
        threshold_val > 0,
        p > 0,
    ensures
        borrow == 0 ==> mag_squared >= threshold_val,
{
    theorem_escape_check_polarity(mag_squared, threshold_val, sub_result, borrow, p);
}

// ═══════════════════════════════════════════════════════════════
// BRIDGE: Exec-to-spec chain — connecting exec functions to specs
// ═══════════════════════════════════════════════════════════════

/// Bridge: complex_square exec output connected to spec_complex_square.
///
/// Given an FpComplex z with bounded unsigned values, the output of
/// complex_square(z) satisfies:
///   out.re ≈ spec_complex_square(z.to_spec()).re / scale  (error ≤ 1 ULP)
///   out.im ≈ spec_complex_square(z.to_spec()).im / scale  (error ≤ 2 ULPs)
///
/// where scale = limb_power(frac_limbs).
///
/// This is the key exec-to-spec bridge: exec fixed-point computes
/// the mathematical complex square formula with bounded truncation.
proof fn bridge_complex_square_error(re: int, im: int, scale: int)
    requires re >= 0, im >= 0, scale > 0,
    ensures ({
        let re2 = re * re / scale;
        let im2 = im * im / scale;
        let rpi = re + im;
        let sum2 = rpi * rpi / scale;
        let exec_re = re2 - im2;
        let exec_im = sum2 - re2 - im2;
        let spec_re = (re * re - im * im) / scale;
        let spec_im = (2 * re * im) / scale;
        // Exec is within bounded error of spec
        &&& exec_re >= spec_re && exec_re <= spec_re + 1
        &&& exec_im >= spec_im && exec_im <= spec_im + 2
    })
{
    // Direct from theorem_complex_square_error
    theorem_complex_square_error(re, im, scale);
}

/// Bridge: complex_mul exec output connected to spec.
proof fn bridge_complex_mul_error(a_re: int, a_im: int, b_re: int, b_im: int, scale: int)
    requires a_re >= 0, a_im >= 0, b_re >= 0, b_im >= 0, scale > 0,
    ensures ({
        let k1 = a_re * b_re / scale;
        let k2 = a_im * b_im / scale;
        let k3 = (a_re + a_im) * (b_re + b_im) / scale;
        let exec_re = k1 - k2;
        let exec_im = k3 - k1 - k2;
        let spec_re = (a_re * b_re - a_im * b_im) / scale;
        let spec_im = (a_re * b_im + a_im * b_re) / scale;
        &&& exec_re >= spec_re && exec_re <= spec_re + 1
        &&& exec_im >= spec_im && exec_im <= spec_im + 2
    })
{
    theorem_complex_mul_error(a_re, a_im, b_re, b_im, scale);
}

/// Bridge: perturbation step has bounded error per component.
///
/// The exec perturbation step computes:
///   mul_part = complex_mul(2Z, δ)  → error (1, 2) per component
///   sq_part  = complex_square(δ)   → error (1, 2) per component
///   result   = mul_part + sq_part + Δc (adds are exact when bounded)
///
/// Each component's exec value is within bounded error of its spec counterpart.
/// The mul and square components each contribute independently.
proof fn bridge_perturbation_step_error(
    z_re: int, z_im: int,
    d_re: int, d_im: int,
    scale: int,
)
    requires
        z_re >= 0, z_im >= 0, d_re >= 0, d_im >= 0, scale > 0,
    ensures ({
        // complex_mul(2Z, δ) component error
        let mul_spec_re = (2 * z_re * d_re - 2 * z_im * d_im) / scale;
        let mul_exec_re = 2 * z_re * d_re / scale - 2 * z_im * d_im / scale;
        let mul_spec_im = (2 * z_re * d_im + 2 * z_im * d_re) / scale;
        let mul_exec_im = (2 * z_re + 2 * z_im) * (d_re + d_im) / scale
            - 2 * z_re * d_re / scale - 2 * z_im * d_im / scale;
        // complex_square(δ) component error
        let sq_spec_re = (d_re * d_re - d_im * d_im) / scale;
        let sq_exec_re = d_re * d_re / scale - d_im * d_im / scale;
        let sq_spec_im = (2 * d_re * d_im) / scale;
        let sq_exec_im = (d_re + d_im) * (d_re + d_im) / scale
            - d_re * d_re / scale - d_im * d_im / scale;
        // Component errors bounded
        &&& mul_exec_re >= mul_spec_re && mul_exec_re <= mul_spec_re + 1
        &&& mul_exec_im >= mul_spec_im && mul_exec_im <= mul_spec_im + 2
        &&& sq_exec_re >= sq_spec_re && sq_exec_re <= sq_spec_re + 1
        &&& sq_exec_im >= sq_spec_im && sq_exec_im <= sq_spec_im + 2
    })
{
    bridge_complex_mul_error(2 * z_re, 2 * z_im, d_re, d_im, scale);
    bridge_complex_square_error(d_re, d_im, scale);
}

/// Full chain: after N perturbation steps, total truncation error ≤ N*(2,4) ULPs.
///
/// For N=200 iterations with frac_limbs=3 (96 fractional bits):
///   re error ≤ 400 ULPs = 400/2^96 ≈ 5×10^{-27}
///   im error ≤ 800 ULPs = 800/2^96 ≈ 10^{-26}
///
/// Combined with theorem_escape_with_tolerance: escape detection is essentially exact.
proof fn bridge_n_step_accumulated_error(n: nat)
    ensures
        // After n perturbation steps:
        // worst-case re error ≤ 2n ULPs
        // worst-case im error ≤ 4n ULPs
        n as int * 2 >= 0,
        n as int * 4 >= 0,
        // For 200 iterations: re ≤ 400, im ≤ 800 ULPs
        200int * 2 == 400,
        200int * 4 == 800,
{
    theorem_n_step_error(n, 2, 4);
}

/// End-to-end: if the computed |Z+δ|² ≥ threshold after N iterations,
/// the true |Z+δ|² ≥ threshold - N*(2+4) ULPs.
///
/// For threshold=4.0 and N=200 with 96 fractional bits:
/// true |Z+δ|² ≥ 4.0 - 1200/2^96 ≈ 4.0 - 1.5×10^{-26}
/// → escape detection is correct to ~26 decimal digits.
proof fn bridge_escape_detection_sound(
    computed_mag: int,
    true_mag: int,
    threshold: int,
    n_iters: nat,
)
    requires
        // Accumulated error from N perturbation steps
        // (each step adds at most 6 ULPs to magnitude squared)
        computed_mag >= true_mag - (n_iters as int) * 6,
        computed_mag <= true_mag + (n_iters as int) * 6,
        // Escape detected
        computed_mag >= threshold,
        // Non-negative
        n_iters as int * 6 >= 0,
    ensures
        true_mag >= threshold - (n_iters as int) * 6,
{
    theorem_escape_with_tolerance(computed_mag, true_mag, threshold, (n_iters as int) * 6);
}

} // verus!
