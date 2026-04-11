/// Helper proof lemmas for the GPU perturbation kernel.
///
/// Companion module to `gpu_perturbation_entry.rs`. Contains spec functions
/// and bridge lemmas needed by `perturbation_iteration_step`'s value
/// postcondition (Task #81 Stage B), kept here to avoid polluting
/// the kernel function's Z3 context.

use vstd::prelude::*;
use verus_fixed_point::fixed_point::limb_ops::{
    LIMB_BASE, LimbOps, limb_power, limbs_val, sem_seq, vec_val, valid_limbs,
    lemma_vec_val_bounded, lemma_vec_val_split,
};
use verus_fixed_point::fixed_point::limb_ops_proofs::signed_val_of;
use crate::gpu_mandelbrot_kernel::{SpecComplex, spec_pert_step};

verus! {

// Helper: limb_power(n) is strictly positive for any nat n.
pub proof fn lemma_limb_power_pos(n: nat)
    ensures limb_power(n) > 0,
    decreases n,
{
    if n == 0 {
        assert(limb_power(0) == 1);
    } else {
        lemma_limb_power_pos((n - 1) as nat);
        assert(LIMB_BASE() > 0);
        assert(limb_power(n) == LIMB_BASE() * limb_power((n - 1) as nat));
        assert(limb_power(n) > 0) by(nonlinear_arith)
            requires LIMB_BASE() > 0, limb_power((n - 1) as nat) > 0,
                     limb_power(n) == LIMB_BASE() * limb_power((n - 1) as nat);
    }
}

// ═══════════════════════════════════════════════════════════════
// Buffer-level spec functions
//
// These spec functions describe what the kernel actually computes at
// the value level: signed-magnitude integers with truncation by
// `limb_power(frac_limbs)` (fixed-point) and modular wrapping at
// `limb_power(n)` (overflow).
// ═══════════════════════════════════════════════════════════════

/// Buffer-level signed addition: a + b, then if the result wraps, fold
/// it back into the (-P, P) range. This is the deterministic if-then-else
/// form of `signed_add_to`'s 3-way disjunction, valid when the result
/// magnitude is bounded by `limb_power(n)`.
pub open spec fn signed_add_buf(a: int, b: int, n: nat) -> int {
    let s = a + b;
    let p = limb_power(n) as int;
    if s >= p { s - p }
    else if s <= -p { s + p }
    else { s }
}

/// Buffer-level signed subtraction: signed_add_buf(a, -b, n).
pub open spec fn signed_sub_buf(a: int, b: int, n: nat) -> int {
    signed_add_buf(a, -b, n)
}

/// Buffer-level signed multiplication: signed product, truncated toward
/// zero by `limb_power(frac_limbs)` (fractional truncation), then reduced
/// modulo `limb_power(n)` (n-limb wraparound). Mirrors what `signed_mul_to`
/// computes at the buffer level.
pub open spec fn signed_mul_buf(a: int, b: int, n: nat, frac_limbs: nat) -> int {
    let prod = a * b;
    let abs_prod = if prod < 0 { -prod } else { prod };
    let mag = (abs_prod / limb_power(frac_limbs)) % limb_power(n);
    if prod < 0 { -mag } else { mag }
}

/// Buffer-level perturbation step: δ' = 2*Z*δ + δ² + Δc, computed via the
/// SAME sequence of buffer ops the kernel uses, so the helper's postcondition
/// can be stated and proven step-by-step.
///
/// Returns `(new_δ_re, new_δ_im)` as signed integers in (-P, P).
pub open spec fn pert_step_buf_int(
    z_re: int, z_im: int,
    dre_in: int, dim_in: int,
    dcre: int, dcim: int,
    n: nat, frac_limbs: nat,
) -> (int, int) {
    // Part A: 2*Z*δ
    let s1 = signed_mul_buf(z_re, dre_in, n, frac_limbs);  // Z_re * δ_re
    let s2 = signed_mul_buf(z_im, dim_in, n, frac_limbs);  // Z_im * δ_im
    let s3 = signed_mul_buf(z_re, dim_in, n, frac_limbs);  // Z_re * δ_im
    let s4 = signed_mul_buf(z_im, dre_in, n, frac_limbs);  // Z_im * δ_re

    let d1 = signed_sub_buf(s1, s2, n);            // Z_re*δ_re - Z_im*δ_im
    let tzd_re = signed_add_buf(d1, d1, n);         // 2*(Z_re*δ_re - Z_im*δ_im)
    let d2 = signed_add_buf(s3, s4, n);             // Z_re*δ_im + Z_im*δ_re
    let tzd_im = signed_add_buf(d2, d2, n);         // 2*(Z_re*δ_im + Z_im*δ_re)

    // Part B: δ² (Karatsuba-style)
    let drs = signed_mul_buf(dre_in, dre_in, n, frac_limbs);    // δ_re²
    let dis = signed_mul_buf(dim_in, dim_in, n, frac_limbs);    // δ_im²
    let dri = signed_add_buf(dre_in, dim_in, n);                // δ_re + δ_im
    let dri2 = signed_mul_buf(dri, dri, n, frac_limbs);         // (δ_re + δ_im)²

    let dsq_re = signed_sub_buf(drs, dis, n);                    // δ_re² - δ_im²
    let q1 = signed_sub_buf(dri2, drs, n);                       // (δ_re+δ_im)² - δ_re²
    let dsq_im = signed_sub_buf(q1, dis, n);                     // ((δ_re+δ_im)² - δ_re²) - δ_im²

    // Part C: δ' = (2*Z*δ) + δ² + Δc
    let p1 = signed_add_buf(tzd_re, dsq_re, n);
    let new_dre = signed_add_buf(p1, dcre, n);
    let p2 = signed_add_buf(tzd_im, dsq_im, n);
    let new_dim = signed_add_buf(p2, dcim, n);

    (new_dre, new_dim)
}

// ═══════════════════════════════════════════════════════════════
// Bridge lemmas: postconditions → spec functions
// ═══════════════════════════════════════════════════════════════

/// Convert signed_add_to's 3-way disjunction postcondition into the
/// deterministic `signed_add_buf` form. The conversion uses
/// `valid_limbs(out_seq)` to bound `signed_val_of(out)` in (-P, P),
/// which uniquely determines which disjunct holds.
pub proof fn lemma_disjunction_to_signed_add_buf<T: LimbOps>(
    a_seq: Seq<T>, a_sign_v: int,
    b_seq: Seq<T>, b_sign_v: int,
    out_seq: Seq<T>, out_sign_v: int,
    n: nat,
)
    requires
        n > 0,
        a_seq.len() == n,
        b_seq.len() == n,
        out_seq.len() == n,
        valid_limbs(a_seq),
        valid_limbs(b_seq),
        valid_limbs(out_seq),
        a_sign_v == 0 || a_sign_v == 1,
        b_sign_v == 0 || b_sign_v == 1,
        out_sign_v == 0 || out_sign_v == 1,
        // The 3-way disjunction from signed_add_to's postcondition.
        ({
            let sa = signed_val_of(a_seq, a_sign_v);
            let sb = signed_val_of(b_seq, b_sign_v);
            let so = signed_val_of(out_seq, out_sign_v);
            let true_sum = sa + sb;
            let p = limb_power(n);
            so == true_sum
                || (so == true_sum - p && true_sum >= p)
                || (so == true_sum + p && true_sum <= -(p as int))
        }),
    ensures
        signed_val_of(out_seq, out_sign_v) == signed_add_buf(
            signed_val_of(a_seq, a_sign_v),
            signed_val_of(b_seq, b_sign_v),
            n,
        ),
{
    let so = signed_val_of(out_seq, out_sign_v);
    let sa = signed_val_of(a_seq, a_sign_v);
    let sb = signed_val_of(b_seq, b_sign_v);
    let true_sum = sa + sb;
    let p = limb_power(n) as int;

    // Bound out_seq via valid_limbs: vec_val(out_seq) < P, hence so in (-P, P).
    lemma_limb_power_pos(n);
    lemma_vec_val_bounded::<T>(out_seq);
    assert(p > 0);
    let vo = vec_val(out_seq);
    assert(vo >= 0);
    assert(vo < p);
    assert(so == vo || so == -vo);
    assert(so > -p);
    assert(so < p);

    // Case-split on which disjunct of the postcondition holds.
    if so == true_sum {
        // Disjunct 1. Since so in (-P, P), true_sum is in (-P, P).
        assert(true_sum > -p);
        assert(true_sum < p);
        // signed_add_buf returns s (no wrap) when -P < s < P.
        assert(signed_add_buf(sa, sb, n) == true_sum);
    } else if so == true_sum - p && true_sum >= p {
        // Disjunct 2. signed_add_buf returns s - P when s >= P.
        assert(signed_add_buf(sa, sb, n) == true_sum - p);
    } else {
        // Disjunct 3. so == true_sum + p && true_sum <= -p
        assert(signed_add_buf(sa, sb, n) == true_sum + p);
    }
}

/// Convert signed_sub_to's 3-way disjunction postcondition into the
/// deterministic `signed_sub_buf` form. Mirrors `lemma_disjunction_to_signed_add_buf`.
pub proof fn lemma_disjunction_to_signed_sub_buf<T: LimbOps>(
    a_seq: Seq<T>, a_sign_v: int,
    b_seq: Seq<T>, b_sign_v: int,
    out_seq: Seq<T>, out_sign_v: int,
    n: nat,
)
    requires
        n > 0,
        a_seq.len() == n,
        b_seq.len() == n,
        out_seq.len() == n,
        valid_limbs(a_seq),
        valid_limbs(b_seq),
        valid_limbs(out_seq),
        a_sign_v == 0 || a_sign_v == 1,
        b_sign_v == 0 || b_sign_v == 1,
        out_sign_v == 0 || out_sign_v == 1,
        // The 3-way disjunction from signed_sub_to's postcondition.
        ({
            let sa = signed_val_of(a_seq, a_sign_v);
            let sb = signed_val_of(b_seq, b_sign_v);
            let so = signed_val_of(out_seq, out_sign_v);
            let true_diff = sa - sb;
            let p = limb_power(n);
            so == true_diff
                || (so == true_diff - p && true_diff >= p)
                || (so == true_diff + p && true_diff <= -(p as int))
        }),
    ensures
        signed_val_of(out_seq, out_sign_v) == signed_sub_buf(
            signed_val_of(a_seq, a_sign_v),
            signed_val_of(b_seq, b_sign_v),
            n,
        ),
{
    let so = signed_val_of(out_seq, out_sign_v);
    let sa = signed_val_of(a_seq, a_sign_v);
    let sb = signed_val_of(b_seq, b_sign_v);
    let true_diff = sa - sb;
    let p = limb_power(n) as int;

    lemma_limb_power_pos(n);
    lemma_vec_val_bounded::<T>(out_seq);
    assert(p > 0);
    let vo = vec_val(out_seq);
    assert(vo >= 0 && vo < p);
    assert(so == vo || so == -vo);
    assert(so > -p && so < p);

    // signed_sub_buf(sa, sb, n) == signed_add_buf(sa, -sb, n)
    // = if (sa - sb) >= P then sa - sb - P
    //   else if (sa - sb) <= -P then sa - sb + P
    //   else sa - sb
    if so == true_diff {
        assert(true_diff > -p && true_diff < p);
        assert(signed_sub_buf(sa, sb, n) == true_diff);
    } else if so == true_diff - p && true_diff >= p {
        assert(signed_sub_buf(sa, sb, n) == true_diff - p);
    } else {
        assert(signed_sub_buf(sa, sb, n) == true_diff + p);
    }
}

/// Convert signed_mul_to's value-equation postcondition into the
/// deterministic `signed_mul_buf` form.
pub proof fn lemma_signed_mul_postcond_to_buf<T: LimbOps>(
    a_seq: Seq<T>, a_sign_v: int,
    b_seq: Seq<T>, b_sign_v: int,
    out_seq: Seq<T>, out_sign_v: int,
    n: nat, frac_limbs: nat,
)
    requires
        n > 0,
        a_seq.len() == n,
        b_seq.len() == n,
        out_seq.len() == n,
        valid_limbs(a_seq),
        valid_limbs(b_seq),
        valid_limbs(out_seq),
        a_sign_v == 0 || a_sign_v == 1,
        b_sign_v == 0 || b_sign_v == 1,
        out_sign_v == 0 || out_sign_v == 1,
        // From signed_mul_to:
        vec_val(out_seq) == (vec_val(a_seq) * vec_val(b_seq) / limb_power(frac_limbs)) % limb_power(n),
        (a_sign_v == b_sign_v) ==> out_sign_v == 0,
        (a_sign_v != b_sign_v) ==> out_sign_v == 1,
    ensures
        signed_val_of(out_seq, out_sign_v) == signed_mul_buf(
            signed_val_of(a_seq, a_sign_v),
            signed_val_of(b_seq, b_sign_v),
            n, frac_limbs,
        ),
{
    let va = vec_val(a_seq);
    let vb = vec_val(b_seq);
    let vo = vec_val(out_seq);
    let sa = signed_val_of(a_seq, a_sign_v);
    let sb = signed_val_of(b_seq, b_sign_v);
    let so = signed_val_of(out_seq, out_sign_v);
    let pf = limb_power(frac_limbs);
    let pn = limb_power(n);

    lemma_limb_power_pos(frac_limbs);
    lemma_limb_power_pos(n);
    lemma_vec_val_bounded::<T>(a_seq);
    lemma_vec_val_bounded::<T>(b_seq);
    lemma_vec_val_bounded::<T>(out_seq);
    assert(va >= 0);
    assert(vb >= 0);
    assert(vo >= 0);
    assert(pf > 0);
    assert(pn > 0);

    // The product magnitude is va * vb (always non-negative).
    let prod_mag = va * vb;
    assert(prod_mag == va * vb);
    assert(va * vb >= 0) by(nonlinear_arith)
        requires va >= 0, vb >= 0;
    assert(prod_mag >= 0);
    assert(vo == (prod_mag / pf) % pn);

    // Now match against signed_mul_buf(sa, sb, n, frac_limbs).
    // sa * sb has the same magnitude (va*vb) and sign determined by a_sign XOR b_sign.
    let sprod = sa * sb;

    // Case-split on whether the signs match.
    if a_sign_v == b_sign_v {
        // Same sign → out_sign == 0, so so == vo.
        assert(out_sign_v == 0);
        assert(so == vo);

        // Show sprod == va * vb.
        if a_sign_v == 0 {
            assert(sa == va);
            assert(sb == vb);
            assert(sprod == va * vb);
        } else {
            assert(sa == -va);
            assert(sb == -vb);
            assert(sprod == sa * sb);
            assert((-va) * (-vb) == va * vb) by(nonlinear_arith);
            assert(sprod == va * vb);
        }
        assert(sprod == prod_mag);
        assert(sprod >= 0);

        // signed_mul_buf body: abs_prod = sprod (since sprod >= 0), mag = (sprod / pf) % pn,
        //                     return mag (since sprod >= 0).
        // = (prod_mag / pf) % pn = vo.
        assert(signed_mul_buf(sa, sb, n, frac_limbs) == vo);
        assert(so == vo);
    } else {
        // Different signs → out_sign == 1, so so == -vo.
        assert(out_sign_v == 1);
        assert(so == -vo);

        // Show sprod == -(va*vb).
        if a_sign_v == 0 {
            assert(sa == va);
            assert(sb == -vb);
            assert(sprod == sa * sb);
            assert(va * (-vb) == -(va * vb)) by(nonlinear_arith);
            assert(sprod == -(va * vb));
        } else {
            assert(sa == -va);
            assert(sb == vb);
            assert(sprod == sa * sb);
            assert((-va) * vb == -(va * vb)) by(nonlinear_arith);
            assert(sprod == -(va * vb));
        }
        assert(sprod == -prod_mag);
        assert(sprod <= 0);

        // Sub-case on prod_mag.
        if prod_mag == 0 {
            // sprod == 0; signed_mul_buf returns mag (else branch since !(prod < 0)).
            // mag = (0 / pf) % pn. Need vo == 0 too.
            assert(sprod == 0);
            assert((0int / pf) == 0) by(nonlinear_arith)
                requires pf > 0;
            assert(((0int) / pf) % pn == 0) by(nonlinear_arith)
                requires pf > 0, pn > 0;
            // vo == (0 / pf) % pn == 0
            assert(vo == 0) by(nonlinear_arith)
                requires vo == (prod_mag / pf) % pn, prod_mag == 0, pf > 0, pn > 0;
            assert(so == 0);
            assert(signed_mul_buf(sa, sb, n, frac_limbs) == 0);
        } else {
            assert(prod_mag > 0);
            assert(sprod < 0);
            // signed_mul_buf body: abs_prod = -sprod (since sprod < 0) = prod_mag.
            // mag = (prod_mag / pf) % pn = vo.
            // Returns -mag = -vo (since sprod < 0).
            assert(signed_mul_buf(sa, sb, n, frac_limbs) == -vo);
            assert(so == -vo);
        }
    }
}

// ═══════════════════════════════════════════════════════════════
// No-wrap lemmas: signed_*_buf reduces to ordinary integer arithmetic
// when the result fits in (-limb_power(n), limb_power(n)).
// ═══════════════════════════════════════════════════════════════

/// `signed_add_buf` returns `a + b` exactly when no wrap occurs.
pub proof fn lemma_signed_add_buf_no_wrap(a: int, b: int, n: nat)
    requires
        n >= 1,
        a + b > -(limb_power(n) as int),
        a + b < limb_power(n) as int,
    ensures
        signed_add_buf(a, b, n) == a + b,
{
    lemma_limb_power_pos(n);
}

/// `signed_sub_buf` returns `a - b` exactly when no wrap occurs.
pub proof fn lemma_signed_sub_buf_no_wrap(a: int, b: int, n: nat)
    requires
        n >= 1,
        a - b > -(limb_power(n) as int),
        a - b < limb_power(n) as int,
    ensures
        signed_sub_buf(a, b, n) == a - b,
{
    lemma_limb_power_pos(n);
    lemma_signed_add_buf_no_wrap(a, -b, n);
}

/// `signed_mul_buf` with `frac_limbs == 0` returns `a * b` exactly when no wrap occurs.
pub proof fn lemma_signed_mul_buf_no_wrap(a: int, b: int, n: nat)
    requires
        n >= 1,
        a * b > -(limb_power(n) as int),
        a * b < limb_power(n) as int,
    ensures
        signed_mul_buf(a, b, n, 0) == a * b,
{
    lemma_limb_power_pos(n);
    let prod = a * b;
    let abs_prod = if prod < 0 { -prod } else { prod };
    // limb_power(0) == 1, so abs_prod / 1 == abs_prod.
    assert(limb_power(0) == 1) by { reveal_with_fuel(limb_power, 1); }
    assert(abs_prod / 1 == abs_prod);
    // abs_prod < limb_power(n), so abs_prod % limb_power(n) == abs_prod.
    assert(abs_prod < limb_power(n));
    assert(abs_prod >= 0);
    assert(abs_prod % limb_power(n) == abs_prod) by(nonlinear_arith)
        requires 0 <= abs_prod, abs_prod < limb_power(n), limb_power(n) > 0;
    // Putting it together: signed_mul_buf returns ±abs_prod which equals prod.
    if prod < 0 {
        assert(abs_prod == -prod);
        assert(signed_mul_buf(a, b, n, 0) == -abs_prod);
        assert(-abs_prod == prod);
    } else {
        assert(abs_prod == prod);
        assert(signed_mul_buf(a, b, n, 0) == abs_prod);
    }
}

// ═══════════════════════════════════════════════════════════════
// Scaled helpers: signed_*_buf on P_frac-scaled inputs
//
// These show that when both inputs to a buffer op are exact multiples
// of `limb_power(frac_limbs)`, the output is also such a multiple —
// specifically, the P_frac-scaled version of the spec result.
// ═══════════════════════════════════════════════════════════════

/// `signed_add_buf` on P_frac-scaled inputs: returns the P_frac-scaled sum.
pub proof fn lemma_signed_add_buf_scaled(
    a_u: int, b_u: int,
    n: nat, frac_limbs: nat,
)
    requires
        n >= 1,
        -(limb_power(n) as int) < (a_u + b_u) * limb_power(frac_limbs),
        (a_u + b_u) * limb_power(frac_limbs) < limb_power(n) as int,
    ensures
        signed_add_buf(
            a_u * limb_power(frac_limbs),
            b_u * limb_power(frac_limbs),
            n,
        ) == (a_u + b_u) * limb_power(frac_limbs),
{
    let pf = limb_power(frac_limbs);
    // (a_u * pf) + (b_u * pf) == (a_u + b_u) * pf
    assert((a_u * pf) + (b_u * pf) == (a_u + b_u) * pf) by(nonlinear_arith);
    // Apply the no-wrap lemma.
    lemma_signed_add_buf_no_wrap(a_u * pf, b_u * pf, n);
}

/// `signed_sub_buf` on P_frac-scaled inputs: returns the P_frac-scaled difference.
pub proof fn lemma_signed_sub_buf_scaled(
    a_u: int, b_u: int,
    n: nat, frac_limbs: nat,
)
    requires
        n >= 1,
        -(limb_power(n) as int) < (a_u - b_u) * limb_power(frac_limbs),
        (a_u - b_u) * limb_power(frac_limbs) < limb_power(n) as int,
    ensures
        signed_sub_buf(
            a_u * limb_power(frac_limbs),
            b_u * limb_power(frac_limbs),
            n,
        ) == (a_u - b_u) * limb_power(frac_limbs),
{
    let pf = limb_power(frac_limbs);
    assert((a_u * pf) - (b_u * pf) == (a_u - b_u) * pf) by(nonlinear_arith);
    lemma_signed_sub_buf_no_wrap(a_u * pf, b_u * pf, n);
}

/// `signed_mul_buf` on P_frac-scaled inputs: returns the P_frac-scaled product.
///
/// Key property: (a_u * pf) * (b_u * pf) = (a_u * b_u) * pf², and dividing
/// by pf gives `(a_u * b_u) * pf` exactly (since pf² is divisible by pf).
pub proof fn lemma_signed_mul_buf_scaled(
    a_u: int, b_u: int,
    n: nat, frac_limbs: nat,
)
    requires
        n >= 1,
        -(limb_power(n) as int) < a_u * b_u * limb_power(frac_limbs),
        a_u * b_u * limb_power(frac_limbs) < limb_power(n) as int,
    ensures
        signed_mul_buf(
            a_u * limb_power(frac_limbs),
            b_u * limb_power(frac_limbs),
            n,
            frac_limbs,
        ) == a_u * b_u * limb_power(frac_limbs),
{
    lemma_limb_power_pos(n);
    lemma_limb_power_pos(frac_limbs);
    let pf = limb_power(frac_limbs);
    let pn = limb_power(n);
    assert(pf > 0);
    assert(pn > 0);

    let a = a_u * pf;
    let b = b_u * pf;
    let s = a_u * b_u;  // unscaled product
    let prod = a * b;
    // prod = a_u * pf * b_u * pf = s * pf * pf = s * pf² = pf * (s * pf)
    assert(prod == s * pf * pf) by(nonlinear_arith)
        requires a == a_u * pf, b == b_u * pf, prod == a * b, s == a_u * b_u;
    assert(prod == pf * (s * pf)) by(nonlinear_arith)
        requires prod == s * pf * pf;

    // Case-split on sign.
    if s >= 0 {
        // prod ≥ 0 (since pf > 0), so abs_prod == prod == pf * (s * pf).
        assert(prod >= 0) by(nonlinear_arith)
            requires prod == s * pf * pf, s >= 0, pf > 0;
        // abs_prod / pf == s * pf  (via lemma_div_multiples_vanish)
        vstd::arithmetic::div_mod::lemma_div_multiples_vanish(s * pf, pf);
        assert((pf * (s * pf)) / pf == s * pf);
        // So mag = (s * pf) % pn. Since -pn < s*pf < pn and s*pf >= 0, mag == s*pf.
        assert(s * pf >= 0) by(nonlinear_arith) requires s >= 0, pf > 0;
        assert(s * pf < pn);
        assert((s * pf) % pn == s * pf) by(nonlinear_arith)
            requires 0 <= s * pf, s * pf < pn, pn > 0;
        // signed_mul_buf returns mag (since prod >= 0).
        assert(signed_mul_buf(a, b, n, frac_limbs) == s * pf);
    } else {
        // s < 0 ⇒ prod < 0.
        assert(prod < 0) by(nonlinear_arith)
            requires prod == s * pf * pf, s < 0, pf > 0;
        // abs_prod == -prod == -(pf * (s * pf)) == pf * (-(s * pf)) == pf * ((-s) * pf)
        assert(-prod == pf * ((-s) * pf)) by(nonlinear_arith)
            requires prod == pf * (s * pf);
        let abs_prod = -prod;
        assert(abs_prod == pf * ((-s) * pf));
        // abs_prod / pf == (-s) * pf
        vstd::arithmetic::div_mod::lemma_div_multiples_vanish((-s) * pf, pf);
        assert((pf * ((-s) * pf)) / pf == (-s) * pf);
        // mag = ((-s) * pf) % pn. Since -s > 0 and (-s)*pf < pn (from precondition: s*pf > -pn), mag == (-s)*pf.
        assert((-s) * pf > 0) by(nonlinear_arith) requires s < 0, pf > 0;
        assert((-s) * pf < pn) by(nonlinear_arith)
            requires -(pn as int) < s * pf;
        assert(((-s) * pf) % pn == (-s) * pf) by(nonlinear_arith)
            requires 0 <= (-s) * pf, (-s) * pf < pn, pn > 0;
        // signed_mul_buf returns -mag (since prod < 0).
        // -mag = -((-s) * pf) = s * pf
        assert(-((-s) * pf) == s * pf) by(nonlinear_arith);
        assert(signed_mul_buf(a, b, n, frac_limbs) == s * pf);
    }
}

// ═══════════════════════════════════════════════════════════════
// Bridge lemma: pert_step_buf_int matches spec_pert_step under bounds
// ═══════════════════════════════════════════════════════════════

/// Single-bound predicate: every intermediate value in the perturbation step
/// chain stays within (-limb_power(n), limb_power(n)) when this holds.
///
/// `R` bounds |z_re|, |z_im|, |dre|, |dim|; `E` bounds |dcre|, |dcim|.
/// The chain's max intermediate is bounded by `12*R*R + E` (the imaginary
/// branch), so requiring `12*R*R + E < limb_power(n)` is sufficient.
pub open spec fn pert_step_no_overflow(
    z_re: int, z_im: int,
    dre: int, dim: int,
    dcre: int, dcim: int,
    r: int, e: int,
    n: nat,
) -> bool {
    &&& -r <= z_re && z_re <= r
    &&& -r <= z_im && z_im <= r
    &&& -r <= dre && dre <= r
    &&& -r <= dim && dim <= r
    &&& -e <= dcre && dcre <= e
    &&& -e <= dcim && dcim <= e
    &&& r >= 0 && e >= 0
    &&& 12 * r * r + e < limb_power(n)
}

/// Bridge lemma: when no wrap/truncation occurs, the buffer-level
/// perturbation step equals the spec-level (mathematical) one.
///
/// Restricted to `frac_limbs == 0` (integer arithmetic). The kernel uses
/// `frac_limbs > 0` (fixed-point), but the integer case is sufficient to
/// validate the structural correspondence — the fixed-point case follows
/// by linear scaling once a separate fixed-point bridge is proven.
pub proof fn lemma_pert_step_buf_matches_spec(
    z_re: int, z_im: int,
    dre: int, dim: int,
    dcre: int, dcim: int,
    r: int, e: int,
    n: nat,
)
    requires
        n >= 1,
        pert_step_no_overflow(z_re, z_im, dre, dim, dcre, dcim, r, e, n),
    ensures
        ({
            let buf_result = pert_step_buf_int(z_re, z_im, dre, dim, dcre, dcim, n, 0);
            let spec_result = spec_pert_step(
                SpecComplex { re: z_re, im: z_im },
                SpecComplex { re: dre, im: dim },
                SpecComplex { re: dcre, im: dcim },
            );
            buf_result.0 == spec_result.re && buf_result.1 == spec_result.im
        }),
{
    lemma_limb_power_pos(n);
    let p = limb_power(n) as int;
    assert(p > 0);

    // Establish r*r >= 0 (non-negative bound).
    assert(r * r >= 0) by(nonlinear_arith);
    assert(12 * r * r >= 0) by(nonlinear_arith) requires r * r >= 0;
    // Helpful product bounds derived from -r <= x <= r and -r <= y <= r:
    //   |x*y| <= r*r
    // We'll establish these for each pair we need.

    // ── Part A: 4 multiplies — all bounded by r*r ──
    assert(z_re * dre <= r * r) by(nonlinear_arith)
        requires -r <= z_re, z_re <= r, -r <= dre, dre <= r;
    assert(-(r * r) <= z_re * dre) by(nonlinear_arith)
        requires -r <= z_re, z_re <= r, -r <= dre, dre <= r;
    assert(z_re * dre < p) by(nonlinear_arith)
        requires z_re * dre <= r * r, 12 * r * r + e < p, e >= 0;
    assert(z_re * dre > -p) by(nonlinear_arith)
        requires -(r * r) <= z_re * dre, 12 * r * r + e < p, e >= 0;
    lemma_signed_mul_buf_no_wrap(z_re, dre, n);
    let s1 = signed_mul_buf(z_re, dre, n, 0);
    assert(s1 == z_re * dre);

    assert(z_im * dim <= r * r) by(nonlinear_arith)
        requires -r <= z_im, z_im <= r, -r <= dim, dim <= r;
    assert(-(r * r) <= z_im * dim) by(nonlinear_arith)
        requires -r <= z_im, z_im <= r, -r <= dim, dim <= r;
    assert(z_im * dim < p) by(nonlinear_arith)
        requires z_im * dim <= r * r, 12 * r * r + e < p, e >= 0;
    assert(z_im * dim > -p) by(nonlinear_arith)
        requires -(r * r) <= z_im * dim, 12 * r * r + e < p, e >= 0;
    lemma_signed_mul_buf_no_wrap(z_im, dim, n);
    let s2 = signed_mul_buf(z_im, dim, n, 0);
    assert(s2 == z_im * dim);

    assert(z_re * dim <= r * r) by(nonlinear_arith)
        requires -r <= z_re, z_re <= r, -r <= dim, dim <= r;
    assert(-(r * r) <= z_re * dim) by(nonlinear_arith)
        requires -r <= z_re, z_re <= r, -r <= dim, dim <= r;
    assert(z_re * dim < p) by(nonlinear_arith)
        requires z_re * dim <= r * r, 12 * r * r + e < p, e >= 0;
    assert(z_re * dim > -p) by(nonlinear_arith)
        requires -(r * r) <= z_re * dim, 12 * r * r + e < p, e >= 0;
    lemma_signed_mul_buf_no_wrap(z_re, dim, n);
    let s3 = signed_mul_buf(z_re, dim, n, 0);
    assert(s3 == z_re * dim);

    assert(z_im * dre <= r * r) by(nonlinear_arith)
        requires -r <= z_im, z_im <= r, -r <= dre, dre <= r;
    assert(-(r * r) <= z_im * dre) by(nonlinear_arith)
        requires -r <= z_im, z_im <= r, -r <= dre, dre <= r;
    assert(z_im * dre < p) by(nonlinear_arith)
        requires z_im * dre <= r * r, 12 * r * r + e < p, e >= 0;
    assert(z_im * dre > -p) by(nonlinear_arith)
        requires -(r * r) <= z_im * dre, 12 * r * r + e < p, e >= 0;
    lemma_signed_mul_buf_no_wrap(z_im, dre, n);
    let s4 = signed_mul_buf(z_im, dre, n, 0);
    assert(s4 == z_im * dre);

    // d1 = s1 - s2, |d1| <= 2*r*r
    assert(s1 - s2 <= 2 * r * r) by(nonlinear_arith)
        requires s1 == z_re * dre, s2 == z_im * dim,
                 z_re * dre <= r * r, z_im * dim >= -(r * r);
    assert(s1 - s2 >= -(2 * r * r)) by(nonlinear_arith)
        requires s1 == z_re * dre, s2 == z_im * dim,
                 z_re * dre >= -(r * r), z_im * dim <= r * r;
    assert(s1 - s2 < p) by(nonlinear_arith)
        requires s1 - s2 <= 2 * r * r, 12 * r * r + e < p, e >= 0;
    assert(s1 - s2 > -p) by(nonlinear_arith)
        requires s1 - s2 >= -(2 * r * r), 12 * r * r + e < p, e >= 0;
    lemma_signed_sub_buf_no_wrap(s1, s2, n);
    let d1 = signed_sub_buf(s1, s2, n);
    assert(d1 == s1 - s2);

    // tzd_re = d1 + d1, |tzd_re| <= 4*r*r
    assert(d1 + d1 <= 4 * r * r) by(nonlinear_arith)
        requires d1 == s1 - s2, s1 - s2 <= 2 * r * r;
    assert(d1 + d1 >= -(4 * r * r)) by(nonlinear_arith)
        requires d1 == s1 - s2, s1 - s2 >= -(2 * r * r);
    assert(d1 + d1 < p) by(nonlinear_arith)
        requires d1 + d1 <= 4 * r * r, 12 * r * r + e < p, e >= 0;
    assert(d1 + d1 > -p) by(nonlinear_arith)
        requires d1 + d1 >= -(4 * r * r), 12 * r * r + e < p, e >= 0;
    lemma_signed_add_buf_no_wrap(d1, d1, n);
    let tzd_re = signed_add_buf(d1, d1, n);
    assert(tzd_re == 2 * (s1 - s2));

    // d2 = s3 + s4, |d2| <= 2*r*r
    assert(s3 + s4 <= 2 * r * r) by(nonlinear_arith)
        requires s3 == z_re * dim, s4 == z_im * dre,
                 z_re * dim <= r * r, z_im * dre <= r * r;
    assert(s3 + s4 >= -(2 * r * r)) by(nonlinear_arith)
        requires s3 == z_re * dim, s4 == z_im * dre,
                 z_re * dim >= -(r * r), z_im * dre >= -(r * r);
    assert(s3 + s4 < p) by(nonlinear_arith)
        requires s3 + s4 <= 2 * r * r, 12 * r * r + e < p, e >= 0;
    assert(s3 + s4 > -p) by(nonlinear_arith)
        requires s3 + s4 >= -(2 * r * r), 12 * r * r + e < p, e >= 0;
    lemma_signed_add_buf_no_wrap(s3, s4, n);
    let d2 = signed_add_buf(s3, s4, n);
    assert(d2 == s3 + s4);

    // tzd_im = d2 + d2, |tzd_im| <= 4*r*r
    assert(d2 + d2 <= 4 * r * r) by(nonlinear_arith)
        requires d2 == s3 + s4, s3 + s4 <= 2 * r * r;
    assert(d2 + d2 >= -(4 * r * r)) by(nonlinear_arith)
        requires d2 == s3 + s4, s3 + s4 >= -(2 * r * r);
    assert(d2 + d2 < p) by(nonlinear_arith)
        requires d2 + d2 <= 4 * r * r, 12 * r * r + e < p, e >= 0;
    assert(d2 + d2 > -p) by(nonlinear_arith)
        requires d2 + d2 >= -(4 * r * r), 12 * r * r + e < p, e >= 0;
    lemma_signed_add_buf_no_wrap(d2, d2, n);
    let tzd_im = signed_add_buf(d2, d2, n);
    assert(tzd_im == 2 * (s3 + s4));

    // ── Part B: δ² ──
    // drs = dre * dre, |drs| <= r*r
    assert(dre * dre <= r * r) by(nonlinear_arith)
        requires -r <= dre, dre <= r;
    assert(dre * dre >= 0) by(nonlinear_arith);
    assert(dre * dre < p) by(nonlinear_arith)
        requires dre * dre <= r * r, 12 * r * r + e < p, e >= 0;
    assert(dre * dre > -p) by(nonlinear_arith)
        requires dre * dre >= 0, p > 0;
    lemma_signed_mul_buf_no_wrap(dre, dre, n);
    let drs = signed_mul_buf(dre, dre, n, 0);
    assert(drs == dre * dre);

    // dis = dim * dim, |dis| <= r*r
    assert(dim * dim <= r * r) by(nonlinear_arith)
        requires -r <= dim, dim <= r;
    assert(dim * dim >= 0) by(nonlinear_arith);
    assert(dim * dim < p) by(nonlinear_arith)
        requires dim * dim <= r * r, 12 * r * r + e < p, e >= 0;
    assert(dim * dim > -p) by(nonlinear_arith)
        requires dim * dim >= 0, p > 0;
    lemma_signed_mul_buf_no_wrap(dim, dim, n);
    let dis = signed_mul_buf(dim, dim, n, 0);
    assert(dis == dim * dim);

    // dri = dre + dim, |dri| <= 2*r
    assert(dre + dim <= 2 * r) by(nonlinear_arith)
        requires -r <= dre, dre <= r, -r <= dim, dim <= r;
    assert(dre + dim >= -(2 * r)) by(nonlinear_arith)
        requires -r <= dre, dre <= r, -r <= dim, dim <= r;
    // |dre+dim| <= 2*r, but we need < p. From 12*r*r + e < p, r >= 0, e >= 0:
    // 2*r could exceed p? No: if r >= 1, then 12*r*r >= 12*r >= 2*r, so 2*r < p.
    // If r == 0, then dre+dim == 0 < p.
    assert(dre + dim < p) by(nonlinear_arith)
        requires dre + dim <= 2 * r, r >= 0, 12 * r * r + e < p, e >= 0;
    assert(dre + dim > -p) by(nonlinear_arith)
        requires dre + dim >= -(2 * r), r >= 0, 12 * r * r + e < p, e >= 0;
    lemma_signed_add_buf_no_wrap(dre, dim, n);
    let dri = signed_add_buf(dre, dim, n);
    assert(dri == dre + dim);

    // dri2 = dri * dri = (dre + dim)², |dri2| <= 4*r*r
    assert(dri * dri <= 4 * r * r) by(nonlinear_arith)
        requires dri == dre + dim, dre + dim <= 2 * r, dre + dim >= -(2 * r);
    assert(dri * dri >= 0) by(nonlinear_arith);
    assert(dri * dri < p) by(nonlinear_arith)
        requires dri * dri <= 4 * r * r, 12 * r * r + e < p, e >= 0;
    assert(dri * dri > -p) by(nonlinear_arith)
        requires dri * dri >= 0, p > 0;
    lemma_signed_mul_buf_no_wrap(dri, dri, n);
    let dri2 = signed_mul_buf(dri, dri, n, 0);
    assert(dri2 == (dre + dim) * (dre + dim));

    // dsq_re = drs - dis = dre² - dim², |dsq_re| <= 2*r*r
    assert(drs - dis <= 2 * r * r) by(nonlinear_arith)
        requires drs == dre * dre, dis == dim * dim,
                 dre * dre <= r * r, dim * dim >= 0;
    assert(drs - dis >= -(2 * r * r)) by(nonlinear_arith)
        requires drs == dre * dre, dis == dim * dim,
                 dre * dre >= 0, dim * dim <= r * r;
    assert(drs - dis < p) by(nonlinear_arith)
        requires drs - dis <= 2 * r * r, 12 * r * r + e < p, e >= 0;
    assert(drs - dis > -p) by(nonlinear_arith)
        requires drs - dis >= -(2 * r * r), 12 * r * r + e < p, e >= 0;
    lemma_signed_sub_buf_no_wrap(drs, dis, n);
    let dsq_re = signed_sub_buf(drs, dis, n);
    assert(dsq_re == dre * dre - dim * dim);

    // q1 = dri2 - drs = (dre+dim)² - dre², |q1| <= 5*r*r
    assert(dri2 - drs <= 5 * r * r) by(nonlinear_arith)
        requires dri2 == (dre + dim) * (dre + dim), drs == dre * dre,
                 dri2 <= 4 * r * r, drs >= 0;
    assert(dri2 - drs >= -(5 * r * r)) by(nonlinear_arith)
        requires dri2 == (dre + dim) * (dre + dim), drs == dre * dre,
                 dri2 >= 0, drs <= r * r;
    assert(dri2 - drs < p) by(nonlinear_arith)
        requires dri2 - drs <= 5 * r * r, 12 * r * r + e < p, e >= 0;
    assert(dri2 - drs > -p) by(nonlinear_arith)
        requires dri2 - drs >= -(5 * r * r), 12 * r * r + e < p, e >= 0;
    lemma_signed_sub_buf_no_wrap(dri2, drs, n);
    let q1 = signed_sub_buf(dri2, drs, n);
    assert(q1 == (dre + dim) * (dre + dim) - dre * dre);

    // dsq_im = q1 - dis = (dre+dim)² - dre² - dim² = 2*dre*dim, |dsq_im| <= 6*r*r
    assert(q1 - dis <= 6 * r * r) by(nonlinear_arith)
        requires q1 == (dre + dim) * (dre + dim) - dre * dre, dis == dim * dim,
                 q1 <= 5 * r * r, dis >= 0;
    assert(q1 - dis >= -(6 * r * r)) by(nonlinear_arith)
        requires q1 == (dre + dim) * (dre + dim) - dre * dre, dis == dim * dim,
                 q1 >= -(5 * r * r), dis <= r * r;
    assert(q1 - dis < p) by(nonlinear_arith)
        requires q1 - dis <= 6 * r * r, 12 * r * r + e < p, e >= 0;
    assert(q1 - dis > -p) by(nonlinear_arith)
        requires q1 - dis >= -(6 * r * r), 12 * r * r + e < p, e >= 0;
    lemma_signed_sub_buf_no_wrap(q1, dis, n);
    let dsq_im = signed_sub_buf(q1, dis, n);
    assert(dsq_im == (dre + dim) * (dre + dim) - dre * dre - dim * dim);
    // Algebraic simplification: (dre+dim)² - dre² - dim² == 2*dre*dim
    assert(dsq_im == 2 * dre * dim) by(nonlinear_arith)
        requires dsq_im == (dre + dim) * (dre + dim) - dre * dre - dim * dim;

    // ── Part C: δ' = (2*Z*δ) + δ² + Δc ──
    // p1 = tzd_re + dsq_re, |p1| <= 4*r*r + 2*r*r = 6*r*r
    assert(tzd_re + dsq_re <= 6 * r * r) by(nonlinear_arith)
        requires tzd_re == 2 * (s1 - s2), s1 - s2 <= 2 * r * r,
                 dsq_re == dre * dre - dim * dim, dre * dre - dim * dim <= 2 * r * r;
    assert(tzd_re + dsq_re >= -(6 * r * r)) by(nonlinear_arith)
        requires tzd_re == 2 * (s1 - s2), s1 - s2 >= -(2 * r * r),
                 dsq_re == dre * dre - dim * dim, dre * dre - dim * dim >= -(2 * r * r);
    assert(tzd_re + dsq_re < p) by(nonlinear_arith)
        requires tzd_re + dsq_re <= 6 * r * r, 12 * r * r + e < p, e >= 0;
    assert(tzd_re + dsq_re > -p) by(nonlinear_arith)
        requires tzd_re + dsq_re >= -(6 * r * r), 12 * r * r + e < p, e >= 0;
    lemma_signed_add_buf_no_wrap(tzd_re, dsq_re, n);
    let p1 = signed_add_buf(tzd_re, dsq_re, n);
    assert(p1 == 2 * (s1 - s2) + (dre * dre - dim * dim));

    // new_dre = p1 + dcre, |new_dre| <= 6*r*r + e
    assert(p1 + dcre <= 6 * r * r + e) by(nonlinear_arith)
        requires p1 <= 6 * r * r, dcre <= e;
    assert(p1 + dcre >= -(6 * r * r) - e) by(nonlinear_arith)
        requires p1 >= -(6 * r * r), dcre >= -e;
    assert(p1 + dcre < p) by(nonlinear_arith)
        requires p1 + dcre <= 6 * r * r + e, 12 * r * r + e < p;
    assert(p1 + dcre > -p) by(nonlinear_arith)
        requires p1 + dcre >= -(6 * r * r) - e, 12 * r * r + e < p;
    lemma_signed_add_buf_no_wrap(p1, dcre, n);
    let new_dre = signed_add_buf(p1, dcre, n);
    assert(new_dre == 2 * (s1 - s2) + (dre * dre - dim * dim) + dcre);

    // p2 = tzd_im + dsq_im, |p2| <= 4*r*r + 6*r*r = 10*r*r
    assert(tzd_im + dsq_im <= 10 * r * r) by(nonlinear_arith)
        requires tzd_im == 2 * (s3 + s4), s3 + s4 <= 2 * r * r,
                 dsq_im == 2 * dre * dim, q1 - dis <= 6 * r * r,
                 dsq_im == q1 - dis;
    assert(tzd_im + dsq_im >= -(10 * r * r)) by(nonlinear_arith)
        requires tzd_im == 2 * (s3 + s4), s3 + s4 >= -(2 * r * r),
                 dsq_im == q1 - dis, q1 - dis >= -(6 * r * r);
    assert(tzd_im + dsq_im < p) by(nonlinear_arith)
        requires tzd_im + dsq_im <= 10 * r * r, 12 * r * r + e < p, e >= 0;
    assert(tzd_im + dsq_im > -p) by(nonlinear_arith)
        requires tzd_im + dsq_im >= -(10 * r * r), 12 * r * r + e < p, e >= 0;
    lemma_signed_add_buf_no_wrap(tzd_im, dsq_im, n);
    let p2 = signed_add_buf(tzd_im, dsq_im, n);
    assert(p2 == 2 * (s3 + s4) + 2 * dre * dim);

    // new_dim = p2 + dcim
    assert(p2 + dcim <= 10 * r * r + e) by(nonlinear_arith)
        requires p2 <= 10 * r * r, dcim <= e;
    assert(p2 + dcim >= -(10 * r * r) - e) by(nonlinear_arith)
        requires p2 >= -(10 * r * r), dcim >= -e;
    assert(p2 + dcim < p) by(nonlinear_arith)
        requires p2 + dcim <= 10 * r * r + e, 12 * r * r + e < p;
    assert(p2 + dcim > -p) by(nonlinear_arith)
        requires p2 + dcim >= -(10 * r * r) - e, 12 * r * r + e < p;
    lemma_signed_add_buf_no_wrap(p2, dcim, n);
    let new_dim = signed_add_buf(p2, dcim, n);
    assert(new_dim == 2 * (s3 + s4) + 2 * dre * dim + dcim);

    // ── Final spec equality ──
    // spec_pert_step's real part: 2*z_re*dre - 2*z_im*dim + dre*dre - dim*dim + dcre
    // new_dre: 2*(s1 - s2) + (dre*dre - dim*dim) + dcre
    //        = 2*(z_re*dre - z_im*dim) + dre*dre - dim*dim + dcre
    //        = 2*z_re*dre - 2*z_im*dim + dre*dre - dim*dim + dcre  ✓
    assert(new_dre == 2 * z_re * dre - 2 * z_im * dim + dre * dre - dim * dim + dcre)
        by(nonlinear_arith)
        requires new_dre == 2 * (s1 - s2) + (dre * dre - dim * dim) + dcre,
                 s1 == z_re * dre, s2 == z_im * dim;

    // spec_pert_step's imag part: 2*z_re*dim + 2*z_im*dre + 2*dre*dim + dcim
    // new_dim: 2*(s3 + s4) + 2*dre*dim + dcim
    //        = 2*(z_re*dim + z_im*dre) + 2*dre*dim + dcim
    //        = 2*z_re*dim + 2*z_im*dre + 2*dre*dim + dcim  ✓
    assert(new_dim == 2 * z_re * dim + 2 * z_im * dre + 2 * dre * dim + dcim)
        by(nonlinear_arith)
        requires new_dim == 2 * (s3 + s4) + 2 * dre * dim + dcim,
                 s3 == z_re * dim, s4 == z_im * dre;
}

// ═══════════════════════════════════════════════════════════════
// Fixed-point bridge (Stage E): pert_step_buf_int matches spec_pert_step
// when inputs are exact P_frac scalings of the spec values.
// ═══════════════════════════════════════════════════════════════

/// Fixed-point bridge lemma: when all buffer inputs are exact P_frac
/// scalings of "unscaled" (spec) values, `pert_step_buf_int` produces
/// the exact P_frac scaling of `spec_pert_step` on the unscaled values.
///
/// The bound precondition uses `pert_step_no_overflow` at scale
/// `(n - frac_limbs)`, because after multiplying the result is a
/// `P_frac`-scaled spec value whose magnitude must fit in
/// `limb_power(n)` — equivalent to the spec value fitting in
/// `limb_power(n - frac_limbs)`.
pub proof fn lemma_pert_step_buf_matches_spec_scaled(
    z_re_u: int, z_im_u: int,
    dre_u: int, dim_u: int,
    dcre_u: int, dcim_u: int,
    r_u: int, e_u: int,
    n: nat, frac_limbs: nat,
)
    requires
        n >= 1,
        frac_limbs <= n,
        // Bounds on unscaled (spec) values — equivalent to no-overflow at
        // scale (n - frac_limbs).
        pert_step_no_overflow(
            z_re_u, z_im_u, dre_u, dim_u, dcre_u, dcim_u,
            r_u, e_u, (n - frac_limbs) as nat,
        ),
    ensures
        ({
            let pf = limb_power(frac_limbs);
            let buf_result = pert_step_buf_int(
                z_re_u * pf, z_im_u * pf,
                dre_u * pf, dim_u * pf,
                dcre_u * pf, dcim_u * pf,
                n, frac_limbs,
            );
            let spec_result = spec_pert_step(
                SpecComplex { re: z_re_u, im: z_im_u },
                SpecComplex { re: dre_u, im: dim_u },
                SpecComplex { re: dcre_u, im: dcim_u },
            );
            buf_result.0 == spec_result.re * pf
                && buf_result.1 == spec_result.im * pf
        }),
{
    lemma_limb_power_pos(frac_limbs);
    lemma_limb_power_pos(n);
    lemma_limb_power_pos((n - frac_limbs) as nat);
    let pf = limb_power(frac_limbs);
    let pn = limb_power(n);
    let pk = limb_power((n - frac_limbs) as nat);
    assert(pf > 0);
    assert(pn > 0);
    assert(pk > 0);

    // pn = pf * pk via lemma_limb_power_add.
    verus_fixed_point::fixed_point::limb_ops::lemma_limb_power_add(
        frac_limbs, (n - frac_limbs) as nat);
    assert(frac_limbs + ((n - frac_limbs) as nat) == n);
    assert(pn == pf * pk);

    // ── Bound lemma: if an unscaled intermediate |x_u| <= bnd_u and
    //    bnd_u <= pk, then the scaled value |x_u * pf| < pn.
    // We'll reuse this implicitly via nonlinear_arith at each step.

    // Inputs satisfy |x_u| <= r_u (resp. e_u), and 12*r_u*r_u + e_u < pk.

    // Notation: r, e for unscaled bounds (we keep r_u, e_u from precondition).
    assert(r_u >= 0);
    assert(e_u >= 0);
    assert(12 * r_u * r_u + e_u < pk);
    assert(r_u * r_u >= 0) by(nonlinear_arith);

    // ── Part A: 2*Z*δ (4 multiplies + 4 add/sub) ──

    // s1 = z_re * dre (scaled). Spec: z_re_u * dre_u.
    assert(z_re_u * dre_u <= r_u * r_u) by(nonlinear_arith)
        requires -r_u <= z_re_u, z_re_u <= r_u, -r_u <= dre_u, dre_u <= r_u;
    assert(-(r_u * r_u) <= z_re_u * dre_u) by(nonlinear_arith)
        requires -r_u <= z_re_u, z_re_u <= r_u, -r_u <= dre_u, dre_u <= r_u;
    assert(z_re_u * dre_u * pf < pn) by(nonlinear_arith)
        requires z_re_u * dre_u <= r_u * r_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < z_re_u * dre_u * pf) by(nonlinear_arith)
        requires -(r_u * r_u) <= z_re_u * dre_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    lemma_signed_mul_buf_scaled(z_re_u, dre_u, n, frac_limbs);
    let s1 = signed_mul_buf(z_re_u * pf, dre_u * pf, n, frac_limbs);
    assert(s1 == z_re_u * dre_u * pf);

    // s2 = z_im * dim (scaled). Spec: z_im_u * dim_u.
    assert(z_im_u * dim_u <= r_u * r_u) by(nonlinear_arith)
        requires -r_u <= z_im_u, z_im_u <= r_u, -r_u <= dim_u, dim_u <= r_u;
    assert(-(r_u * r_u) <= z_im_u * dim_u) by(nonlinear_arith)
        requires -r_u <= z_im_u, z_im_u <= r_u, -r_u <= dim_u, dim_u <= r_u;
    assert(z_im_u * dim_u * pf < pn) by(nonlinear_arith)
        requires z_im_u * dim_u <= r_u * r_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < z_im_u * dim_u * pf) by(nonlinear_arith)
        requires -(r_u * r_u) <= z_im_u * dim_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    lemma_signed_mul_buf_scaled(z_im_u, dim_u, n, frac_limbs);
    let s2 = signed_mul_buf(z_im_u * pf, dim_u * pf, n, frac_limbs);
    assert(s2 == z_im_u * dim_u * pf);

    // s3 = z_re * dim. Spec: z_re_u * dim_u.
    assert(z_re_u * dim_u <= r_u * r_u) by(nonlinear_arith)
        requires -r_u <= z_re_u, z_re_u <= r_u, -r_u <= dim_u, dim_u <= r_u;
    assert(-(r_u * r_u) <= z_re_u * dim_u) by(nonlinear_arith)
        requires -r_u <= z_re_u, z_re_u <= r_u, -r_u <= dim_u, dim_u <= r_u;
    assert(z_re_u * dim_u * pf < pn) by(nonlinear_arith)
        requires z_re_u * dim_u <= r_u * r_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < z_re_u * dim_u * pf) by(nonlinear_arith)
        requires -(r_u * r_u) <= z_re_u * dim_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    lemma_signed_mul_buf_scaled(z_re_u, dim_u, n, frac_limbs);
    let s3 = signed_mul_buf(z_re_u * pf, dim_u * pf, n, frac_limbs);
    assert(s3 == z_re_u * dim_u * pf);

    // s4 = z_im * dre. Spec: z_im_u * dre_u.
    assert(z_im_u * dre_u <= r_u * r_u) by(nonlinear_arith)
        requires -r_u <= z_im_u, z_im_u <= r_u, -r_u <= dre_u, dre_u <= r_u;
    assert(-(r_u * r_u) <= z_im_u * dre_u) by(nonlinear_arith)
        requires -r_u <= z_im_u, z_im_u <= r_u, -r_u <= dre_u, dre_u <= r_u;
    assert(z_im_u * dre_u * pf < pn) by(nonlinear_arith)
        requires z_im_u * dre_u <= r_u * r_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < z_im_u * dre_u * pf) by(nonlinear_arith)
        requires -(r_u * r_u) <= z_im_u * dre_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    lemma_signed_mul_buf_scaled(z_im_u, dre_u, n, frac_limbs);
    let s4 = signed_mul_buf(z_im_u * pf, dre_u * pf, n, frac_limbs);
    assert(s4 == z_im_u * dre_u * pf);

    // d1 = s1 - s2, spec s1u - s2u where s1u = z_re_u * dre_u, s2u = z_im_u * dim_u
    let s1u = z_re_u * dre_u;
    let s2u = z_im_u * dim_u;
    assert(s1u - s2u <= 2 * r_u * r_u) by(nonlinear_arith)
        requires s1u == z_re_u * dre_u, s2u == z_im_u * dim_u,
                 z_re_u * dre_u <= r_u * r_u, z_im_u * dim_u >= -(r_u * r_u);
    assert(-(2 * r_u * r_u) <= s1u - s2u) by(nonlinear_arith)
        requires s1u == z_re_u * dre_u, s2u == z_im_u * dim_u,
                 z_re_u * dre_u >= -(r_u * r_u), z_im_u * dim_u <= r_u * r_u;
    assert((s1u - s2u) * pf < pn) by(nonlinear_arith)
        requires s1u - s2u <= 2 * r_u * r_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < (s1u - s2u) * pf) by(nonlinear_arith)
        requires -(2 * r_u * r_u) <= s1u - s2u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    // s1 - s2 = (s1u * pf) - (s2u * pf) = (s1u - s2u) * pf
    assert(s1 - s2 == (s1u - s2u) * pf) by(nonlinear_arith)
        requires s1 == s1u * pf, s2 == s2u * pf;
    lemma_signed_sub_buf_scaled(s1u, s2u, n, frac_limbs);
    let d1 = signed_sub_buf(s1u * pf, s2u * pf, n);
    assert(d1 == (s1u - s2u) * pf);
    // signed_sub_buf only uses the values, not their "spec form", so this equates:
    assert(signed_sub_buf(s1, s2, n) == d1) by {
        assert(s1 == s1u * pf);
        assert(s2 == s2u * pf);
    }

    // tzd_re = d1 + d1 = 2*(s1u - s2u) * pf
    assert((s1u - s2u) + (s1u - s2u) == 2 * (s1u - s2u)) by(nonlinear_arith);
    assert(2 * (s1u - s2u) <= 4 * r_u * r_u) by(nonlinear_arith)
        requires s1u - s2u <= 2 * r_u * r_u;
    assert(-(4 * r_u * r_u) <= 2 * (s1u - s2u)) by(nonlinear_arith)
        requires s1u - s2u >= -(2 * r_u * r_u);
    assert(2 * (s1u - s2u) * pf < pn) by(nonlinear_arith)
        requires 2 * (s1u - s2u) <= 4 * r_u * r_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < 2 * (s1u - s2u) * pf) by(nonlinear_arith)
        requires 2 * (s1u - s2u) >= -(4 * r_u * r_u), 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    lemma_signed_add_buf_scaled(s1u - s2u, s1u - s2u, n, frac_limbs);
    let tzd_re = signed_add_buf((s1u - s2u) * pf, (s1u - s2u) * pf, n);
    assert(tzd_re == 2 * (s1u - s2u) * pf) by(nonlinear_arith)
        requires tzd_re == ((s1u - s2u) + (s1u - s2u)) * pf;
    // Connect back to d1:
    assert(signed_add_buf(d1, d1, n) == tzd_re) by {
        assert(d1 == (s1u - s2u) * pf);
    }

    // d2 = s3 + s4, spec s3u + s4u
    let s3u = z_re_u * dim_u;
    let s4u = z_im_u * dre_u;
    assert(s3u + s4u <= 2 * r_u * r_u) by(nonlinear_arith)
        requires s3u == z_re_u * dim_u, s4u == z_im_u * dre_u,
                 z_re_u * dim_u <= r_u * r_u, z_im_u * dre_u <= r_u * r_u;
    assert(-(2 * r_u * r_u) <= s3u + s4u) by(nonlinear_arith)
        requires s3u == z_re_u * dim_u, s4u == z_im_u * dre_u,
                 z_re_u * dim_u >= -(r_u * r_u), z_im_u * dre_u >= -(r_u * r_u);
    assert((s3u + s4u) * pf < pn) by(nonlinear_arith)
        requires s3u + s4u <= 2 * r_u * r_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < (s3u + s4u) * pf) by(nonlinear_arith)
        requires -(2 * r_u * r_u) <= s3u + s4u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    lemma_signed_add_buf_scaled(s3u, s4u, n, frac_limbs);
    let d2 = signed_add_buf(s3u * pf, s4u * pf, n);
    assert(d2 == (s3u + s4u) * pf);
    assert(signed_add_buf(s3, s4, n) == d2) by {
        assert(s3 == s3u * pf);
        assert(s4 == s4u * pf);
    }

    // tzd_im = d2 + d2 = 2*(s3u + s4u) * pf
    assert((s3u + s4u) + (s3u + s4u) == 2 * (s3u + s4u)) by(nonlinear_arith);
    assert(2 * (s3u + s4u) <= 4 * r_u * r_u) by(nonlinear_arith)
        requires s3u + s4u <= 2 * r_u * r_u;
    assert(-(4 * r_u * r_u) <= 2 * (s3u + s4u)) by(nonlinear_arith)
        requires s3u + s4u >= -(2 * r_u * r_u);
    assert(2 * (s3u + s4u) * pf < pn) by(nonlinear_arith)
        requires 2 * (s3u + s4u) <= 4 * r_u * r_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < 2 * (s3u + s4u) * pf) by(nonlinear_arith)
        requires 2 * (s3u + s4u) >= -(4 * r_u * r_u), 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    lemma_signed_add_buf_scaled(s3u + s4u, s3u + s4u, n, frac_limbs);
    let tzd_im = signed_add_buf((s3u + s4u) * pf, (s3u + s4u) * pf, n);
    assert(tzd_im == 2 * (s3u + s4u) * pf) by(nonlinear_arith)
        requires tzd_im == ((s3u + s4u) + (s3u + s4u)) * pf;
    assert(signed_add_buf(d2, d2, n) == tzd_im) by {
        assert(d2 == (s3u + s4u) * pf);
    }

    // ── Part B: δ² ──
    // drs = dre² = dre_u²
    assert(dre_u * dre_u <= r_u * r_u) by(nonlinear_arith)
        requires -r_u <= dre_u, dre_u <= r_u;
    assert(dre_u * dre_u >= 0) by(nonlinear_arith);
    assert(dre_u * dre_u * pf >= 0) by(nonlinear_arith)
        requires dre_u * dre_u >= 0, pf > 0;
    assert(dre_u * dre_u * pf < pn) by(nonlinear_arith)
        requires dre_u * dre_u <= r_u * r_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < dre_u * dre_u * pf) by(nonlinear_arith)
        requires dre_u * dre_u * pf >= 0, pn > 0;
    lemma_signed_mul_buf_scaled(dre_u, dre_u, n, frac_limbs);
    let drs = signed_mul_buf(dre_u * pf, dre_u * pf, n, frac_limbs);
    assert(drs == dre_u * dre_u * pf);

    // dis = dim² = dim_u²
    assert(dim_u * dim_u <= r_u * r_u) by(nonlinear_arith)
        requires -r_u <= dim_u, dim_u <= r_u;
    assert(dim_u * dim_u >= 0) by(nonlinear_arith);
    assert(dim_u * dim_u * pf >= 0) by(nonlinear_arith)
        requires dim_u * dim_u >= 0, pf > 0;
    assert(dim_u * dim_u * pf < pn) by(nonlinear_arith)
        requires dim_u * dim_u <= r_u * r_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < dim_u * dim_u * pf) by(nonlinear_arith)
        requires dim_u * dim_u * pf >= 0, pn > 0;
    lemma_signed_mul_buf_scaled(dim_u, dim_u, n, frac_limbs);
    let dis = signed_mul_buf(dim_u * pf, dim_u * pf, n, frac_limbs);
    assert(dis == dim_u * dim_u * pf);

    // dri = dre + dim
    assert(dre_u + dim_u <= 2 * r_u) by(nonlinear_arith)
        requires -r_u <= dre_u, dre_u <= r_u, -r_u <= dim_u, dim_u <= r_u;
    assert(-(2 * r_u) <= dre_u + dim_u) by(nonlinear_arith)
        requires -r_u <= dre_u, dre_u <= r_u, -r_u <= dim_u, dim_u <= r_u;
    // 2*r_u * pf <= 12*r_u*r_u*pf ... need careful bound
    // dre_u + dim_u fits in pk because 2*r_u <= 12*r_u*r_u (for r_u >= 1) OR dre_u+dim_u == 0 (r_u=0).
    assert((dre_u + dim_u) * pf < pn) by(nonlinear_arith)
        requires dre_u + dim_u <= 2 * r_u, r_u >= 0, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < (dre_u + dim_u) * pf) by(nonlinear_arith)
        requires dre_u + dim_u >= -(2 * r_u), r_u >= 0, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    lemma_signed_add_buf_scaled(dre_u, dim_u, n, frac_limbs);
    let dri = signed_add_buf(dre_u * pf, dim_u * pf, n);
    assert(dri == (dre_u + dim_u) * pf);

    // dri2 = dri² = (dre_u + dim_u)²
    assert((dre_u + dim_u) * (dre_u + dim_u) <= 4 * r_u * r_u) by(nonlinear_arith)
        requires -(2 * r_u) <= dre_u + dim_u, dre_u + dim_u <= 2 * r_u, r_u >= 0;
    assert((dre_u + dim_u) * (dre_u + dim_u) >= 0) by(nonlinear_arith);
    assert((dre_u + dim_u) * (dre_u + dim_u) * pf >= 0) by(nonlinear_arith)
        requires (dre_u + dim_u) * (dre_u + dim_u) >= 0, pf > 0;
    assert((dre_u + dim_u) * (dre_u + dim_u) * pf < pn) by(nonlinear_arith)
        requires (dre_u + dim_u) * (dre_u + dim_u) <= 4 * r_u * r_u,
                 12 * r_u * r_u + e_u < pk, pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < (dre_u + dim_u) * (dre_u + dim_u) * pf) by(nonlinear_arith)
        requires (dre_u + dim_u) * (dre_u + dim_u) * pf >= 0, pn > 0;
    lemma_signed_mul_buf_scaled(dre_u + dim_u, dre_u + dim_u, n, frac_limbs);
    let dri2 = signed_mul_buf((dre_u + dim_u) * pf, (dre_u + dim_u) * pf, n, frac_limbs);
    assert(dri2 == (dre_u + dim_u) * (dre_u + dim_u) * pf);
    assert(signed_mul_buf(dri, dri, n, frac_limbs) == dri2) by {
        assert(dri == (dre_u + dim_u) * pf);
    }

    // dsq_re = drs - dis = dre_u² - dim_u²
    let drs_u = dre_u * dre_u;
    let dis_u = dim_u * dim_u;
    assert(drs_u - dis_u <= 2 * r_u * r_u) by(nonlinear_arith)
        requires drs_u == dre_u * dre_u, dis_u == dim_u * dim_u,
                 drs_u <= r_u * r_u, dis_u >= 0;
    assert(-(2 * r_u * r_u) <= drs_u - dis_u) by(nonlinear_arith)
        requires drs_u == dre_u * dre_u, dis_u == dim_u * dim_u,
                 drs_u >= 0, dis_u <= r_u * r_u;
    assert((drs_u - dis_u) * pf < pn) by(nonlinear_arith)
        requires drs_u - dis_u <= 2 * r_u * r_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < (drs_u - dis_u) * pf) by(nonlinear_arith)
        requires -(2 * r_u * r_u) <= drs_u - dis_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    lemma_signed_sub_buf_scaled(drs_u, dis_u, n, frac_limbs);
    let dsq_re = signed_sub_buf(drs_u * pf, dis_u * pf, n);
    assert(dsq_re == (drs_u - dis_u) * pf);
    assert(signed_sub_buf(drs, dis, n) == dsq_re) by {
        assert(drs == drs_u * pf);
        assert(dis == dis_u * pf);
    }

    // q1 = dri2 - drs = (dre_u + dim_u)² - dre_u²
    let dri2_u = (dre_u + dim_u) * (dre_u + dim_u);
    assert(dri2_u - drs_u <= 5 * r_u * r_u) by(nonlinear_arith)
        requires dri2_u == (dre_u + dim_u) * (dre_u + dim_u), drs_u == dre_u * dre_u,
                 dri2_u <= 4 * r_u * r_u, drs_u >= 0;
    assert(-(5 * r_u * r_u) <= dri2_u - drs_u) by(nonlinear_arith)
        requires dri2_u == (dre_u + dim_u) * (dre_u + dim_u), drs_u == dre_u * dre_u,
                 dri2_u >= 0, drs_u <= r_u * r_u;
    assert((dri2_u - drs_u) * pf < pn) by(nonlinear_arith)
        requires dri2_u - drs_u <= 5 * r_u * r_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < (dri2_u - drs_u) * pf) by(nonlinear_arith)
        requires -(5 * r_u * r_u) <= dri2_u - drs_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    lemma_signed_sub_buf_scaled(dri2_u, drs_u, n, frac_limbs);
    let q1 = signed_sub_buf(dri2_u * pf, drs_u * pf, n);
    assert(q1 == (dri2_u - drs_u) * pf);
    assert(signed_sub_buf(dri2, drs, n) == q1) by {
        assert(dri2 == dri2_u * pf);
        assert(drs == drs_u * pf);
    }

    // dsq_im = q1 - dis = (dri2_u - drs_u) - dis_u
    let q1_u = dri2_u - drs_u;
    assert(q1_u - dis_u <= 6 * r_u * r_u) by(nonlinear_arith)
        requires q1_u == dri2_u - drs_u, dis_u == dim_u * dim_u,
                 q1_u <= 5 * r_u * r_u, dis_u >= 0;
    assert(-(6 * r_u * r_u) <= q1_u - dis_u) by(nonlinear_arith)
        requires q1_u == dri2_u - drs_u, dis_u == dim_u * dim_u,
                 q1_u >= -(5 * r_u * r_u), dis_u <= r_u * r_u;
    assert((q1_u - dis_u) * pf < pn) by(nonlinear_arith)
        requires q1_u - dis_u <= 6 * r_u * r_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < (q1_u - dis_u) * pf) by(nonlinear_arith)
        requires -(6 * r_u * r_u) <= q1_u - dis_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    lemma_signed_sub_buf_scaled(q1_u, dis_u, n, frac_limbs);
    let dsq_im = signed_sub_buf(q1_u * pf, dis_u * pf, n);
    assert(dsq_im == (q1_u - dis_u) * pf);
    assert(signed_sub_buf(q1, dis, n) == dsq_im) by {
        assert(q1 == q1_u * pf);
        assert(dis == dis_u * pf);
    }
    // Algebraic simplification: q1_u - dis_u = (dre_u+dim_u)² - dre_u² - dim_u² = 2*dre_u*dim_u
    assert(q1_u - dis_u == 2 * dre_u * dim_u) by(nonlinear_arith)
        requires q1_u == (dre_u + dim_u) * (dre_u + dim_u) - dre_u * dre_u,
                 dis_u == dim_u * dim_u;
    assert(dsq_im == 2 * dre_u * dim_u * pf);

    // ── Part C: δ' = (2*Z*δ) + δ² + Δc ──
    // p1 = tzd_re + dsq_re = 2*(s1u - s2u) + (drs_u - dis_u)
    let tzd_re_u = 2 * (s1u - s2u);
    let dsq_re_u = drs_u - dis_u;
    assert(tzd_re_u + dsq_re_u <= 6 * r_u * r_u) by(nonlinear_arith)
        requires tzd_re_u == 2 * (s1u - s2u), s1u - s2u <= 2 * r_u * r_u,
                 dsq_re_u == drs_u - dis_u, drs_u - dis_u <= 2 * r_u * r_u;
    assert(-(6 * r_u * r_u) <= tzd_re_u + dsq_re_u) by(nonlinear_arith)
        requires tzd_re_u == 2 * (s1u - s2u), s1u - s2u >= -(2 * r_u * r_u),
                 dsq_re_u == drs_u - dis_u, drs_u - dis_u >= -(2 * r_u * r_u);
    assert((tzd_re_u + dsq_re_u) * pf < pn) by(nonlinear_arith)
        requires tzd_re_u + dsq_re_u <= 6 * r_u * r_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < (tzd_re_u + dsq_re_u) * pf) by(nonlinear_arith)
        requires -(6 * r_u * r_u) <= tzd_re_u + dsq_re_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    lemma_signed_add_buf_scaled(tzd_re_u, dsq_re_u, n, frac_limbs);
    let p1 = signed_add_buf(tzd_re_u * pf, dsq_re_u * pf, n);
    assert(p1 == (tzd_re_u + dsq_re_u) * pf);
    assert(signed_add_buf(tzd_re, dsq_re, n) == p1) by {
        assert(tzd_re == tzd_re_u * pf);
        assert(dsq_re == dsq_re_u * pf);
    }

    // new_dre = p1 + dcre = (tzd_re_u + dsq_re_u) + dcre_u
    let p1_u = tzd_re_u + dsq_re_u;
    assert(p1_u + dcre_u <= 6 * r_u * r_u + e_u) by(nonlinear_arith)
        requires p1_u <= 6 * r_u * r_u, dcre_u <= e_u;
    assert(-(6 * r_u * r_u + e_u) <= p1_u + dcre_u) by(nonlinear_arith)
        requires p1_u >= -(6 * r_u * r_u), dcre_u >= -e_u;
    assert((p1_u + dcre_u) * pf < pn) by(nonlinear_arith)
        requires p1_u + dcre_u <= 6 * r_u * r_u + e_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0;
    assert(-(pn as int) < (p1_u + dcre_u) * pf) by(nonlinear_arith)
        requires -(6 * r_u * r_u + e_u) <= p1_u + dcre_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0;
    lemma_signed_add_buf_scaled(p1_u, dcre_u, n, frac_limbs);
    let new_dre = signed_add_buf(p1_u * pf, dcre_u * pf, n);
    assert(new_dre == (p1_u + dcre_u) * pf);
    assert(signed_add_buf(p1, dcre_u * pf, n) == new_dre) by {
        assert(p1 == p1_u * pf);
    }

    // p2 = tzd_im + dsq_im = 2*(s3u + s4u) + 2*dre_u*dim_u
    let tzd_im_u = 2 * (s3u + s4u);
    let dsq_im_u = 2 * dre_u * dim_u;
    assert(tzd_im_u + dsq_im_u <= 10 * r_u * r_u) by(nonlinear_arith)
        requires tzd_im_u == 2 * (s3u + s4u), s3u + s4u <= 2 * r_u * r_u,
                 dsq_im_u == 2 * dre_u * dim_u, dsq_im_u == q1_u - dis_u,
                 q1_u - dis_u <= 6 * r_u * r_u;
    assert(-(10 * r_u * r_u) <= tzd_im_u + dsq_im_u) by(nonlinear_arith)
        requires tzd_im_u == 2 * (s3u + s4u), s3u + s4u >= -(2 * r_u * r_u),
                 dsq_im_u == 2 * dre_u * dim_u, dsq_im_u == q1_u - dis_u,
                 q1_u - dis_u >= -(6 * r_u * r_u);
    assert((tzd_im_u + dsq_im_u) * pf < pn) by(nonlinear_arith)
        requires tzd_im_u + dsq_im_u <= 10 * r_u * r_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    assert(-(pn as int) < (tzd_im_u + dsq_im_u) * pf) by(nonlinear_arith)
        requires -(10 * r_u * r_u) <= tzd_im_u + dsq_im_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0, e_u >= 0;
    lemma_signed_add_buf_scaled(tzd_im_u, dsq_im_u, n, frac_limbs);
    let p2 = signed_add_buf(tzd_im_u * pf, dsq_im_u * pf, n);
    assert(p2 == (tzd_im_u + dsq_im_u) * pf);
    assert(signed_add_buf(tzd_im, dsq_im, n) == p2) by {
        assert(tzd_im == tzd_im_u * pf);
        assert(dsq_im == dsq_im_u * pf);
    }

    // new_dim = p2 + dcim
    let p2_u = tzd_im_u + dsq_im_u;
    assert(p2_u + dcim_u <= 10 * r_u * r_u + e_u) by(nonlinear_arith)
        requires p2_u <= 10 * r_u * r_u, dcim_u <= e_u;
    assert(-(10 * r_u * r_u + e_u) <= p2_u + dcim_u) by(nonlinear_arith)
        requires p2_u >= -(10 * r_u * r_u), dcim_u >= -e_u;
    assert((p2_u + dcim_u) * pf < pn) by(nonlinear_arith)
        requires p2_u + dcim_u <= 10 * r_u * r_u + e_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0;
    assert(-(pn as int) < (p2_u + dcim_u) * pf) by(nonlinear_arith)
        requires -(10 * r_u * r_u + e_u) <= p2_u + dcim_u, 12 * r_u * r_u + e_u < pk,
                 pn == pf * pk, pf > 0;
    lemma_signed_add_buf_scaled(p2_u, dcim_u, n, frac_limbs);
    let new_dim = signed_add_buf(p2_u * pf, dcim_u * pf, n);
    assert(new_dim == (p2_u + dcim_u) * pf);
    assert(signed_add_buf(p2, dcim_u * pf, n) == new_dim) by {
        assert(p2 == p2_u * pf);
    }

    // ── Final spec equality ──
    // new_dre == spec.re * pf where spec.re == 2*z_re_u*dre_u - 2*z_im_u*dim_u + dre_u² - dim_u² + dcre_u
    // We have new_dre == (p1_u + dcre_u) * pf
    //                 == (tzd_re_u + dsq_re_u + dcre_u) * pf
    //                 == (2*(s1u - s2u) + (drs_u - dis_u) + dcre_u) * pf
    //                 == (2*(z_re_u*dre_u - z_im_u*dim_u) + dre_u² - dim_u² + dcre_u) * pf
    //                 == (2*z_re_u*dre_u - 2*z_im_u*dim_u + dre_u² - dim_u² + dcre_u) * pf
    assert(new_dre == (2 * z_re_u * dre_u - 2 * z_im_u * dim_u
                        + dre_u * dre_u - dim_u * dim_u + dcre_u) * pf)
        by(nonlinear_arith)
        requires
            new_dre == (p1_u + dcre_u) * pf,
            p1_u == tzd_re_u + dsq_re_u,
            tzd_re_u == 2 * (s1u - s2u),
            dsq_re_u == drs_u - dis_u,
            s1u == z_re_u * dre_u, s2u == z_im_u * dim_u,
            drs_u == dre_u * dre_u, dis_u == dim_u * dim_u;

    // new_dim == spec.im * pf
    assert(new_dim == (2 * z_re_u * dim_u + 2 * z_im_u * dre_u
                        + 2 * dre_u * dim_u + dcim_u) * pf)
        by(nonlinear_arith)
        requires
            new_dim == (p2_u + dcim_u) * pf,
            p2_u == tzd_im_u + dsq_im_u,
            tzd_im_u == 2 * (s3u + s4u),
            dsq_im_u == 2 * dre_u * dim_u,
            s3u == z_re_u * dim_u, s4u == z_im_u * dre_u;
}

// ═══════════════════════════════════════════════════════════════
// Task #80: Relational glitch criterion + soundness
// ═══════════════════════════════════════════════════════════════

/// Linearization-invalid criterion: the perturbation δ has grown too large
/// relative to the reference Z for the perturbation theory linearization
/// `(Z+δ)² ≈ Z² + 2Zδ` to be a good approximation.
///
/// Formula: `4 * |δ|² ≥ tolerance * |Z|²`. Larger `tolerance` ⇒ stricter
/// (harder to fire). Some calibrations:
///   * tolerance == 1: |δ| ≥ |Z|/2
///   * tolerance == 4: |δ| ≥ |Z|
///   * tolerance == 16: |δ| ≥ 2|Z|
pub open spec fn is_glitch(z: SpecComplex, delta: SpecComplex, tolerance: int) -> bool {
    let z_mag_sq = z.re * z.re + z.im * z.im;
    let delta_mag_sq = delta.re * delta.re + delta.im * delta.im;
    4 * delta_mag_sq >= tolerance * z_mag_sq
}

/// Building block: if either component magnitude exceeds k, then
/// `4 * delta_mag_sq >= 4 * k²`.
pub proof fn lemma_glitch_magnitude_lower_bound(delta: SpecComplex, k: int)
    requires
        k >= 0,
        delta.re * delta.re >= k * k || delta.im * delta.im >= k * k,
    ensures
        4 * (delta.re * delta.re + delta.im * delta.im) >= 4 * k * k,
{
    assert(delta.re * delta.re >= 0) by(nonlinear_arith);
    assert(delta.im * delta.im >= 0) by(nonlinear_arith);
    let sum = delta.re * delta.re + delta.im * delta.im;
    if delta.re * delta.re >= k * k {
        assert(sum >= k * k);
    } else {
        assert(delta.im * delta.im >= k * k);
        assert(sum >= k * k);
    }
    assert(4 * sum >= 4 * (k * k)) by(nonlinear_arith)
        requires sum >= k * k;
    assert(4 * (k * k) == 4 * k * k) by(nonlinear_arith);
}

/// Soundness, integer level: given a magnitude lower bound on δ and a
/// tolerance/Z bound, is_glitch holds.
pub proof fn lemma_glitch_soundness_int(
    z: SpecComplex,
    delta: SpecComplex,
    k: int,
    tolerance: int,
)
    requires
        k >= 0,
        delta.re * delta.re >= k * k || delta.im * delta.im >= k * k,
        tolerance * (z.re * z.re + z.im * z.im) <= 4 * k * k,
    ensures
        is_glitch(z, delta, tolerance),
{
    lemma_glitch_magnitude_lower_bound(delta, k);
    let z_mag_sq = z.re * z.re + z.im * z.im;
    let delta_mag_sq = delta.re * delta.re + delta.im * delta.im;
    assert(4 * delta_mag_sq >= 4 * k * k);
    assert(4 * delta_mag_sq >= tolerance * z_mag_sq);
}

/// Limb-level: if `vec_val(δ) >= 4 * limb_power(n - 1)`, the top limb > 3.
/// Generic version of `lemma_glitch_completeness_one` (#76).
pub proof fn lemma_magnitude_implies_top<T: LimbOps>(
    delta: Seq<T>, n: nat,
)
    requires
        n >= 1,
        delta.len() == n as int,
        valid_limbs(delta),
        vec_val(delta) >= 4 * limb_power((n - 1) as nat),
    ensures
        delta[(n - 1) as int].sem() > 3,
{
    let s_top = limb_power((n - 1) as nat);
    let lo = delta.subrange(0, (n - 1) as int);
    assert(valid_limbs(lo)) by {
        assert forall |k: int| 0 <= k < lo.len()
            implies 0 <= (#[trigger] lo[k]).sem() && lo[k].sem() < LIMB_BASE() by {
            assert(lo[k] == delta[k]);
        }
    }
    lemma_vec_val_split::<T>(delta, (n - 1) as nat);
    let lo_v = vec_val(lo);
    let top_v = delta[(n - 1) as int].sem();
    let hi_seq = delta.subrange((n - 1) as int, n as int);
    assert(hi_seq.len() == 1);
    assert(hi_seq[0] == delta[(n - 1) as int]);
    reveal_with_fuel(limbs_val, 2);
    assert(sem_seq(hi_seq).len() == 1);
    assert(sem_seq(hi_seq)[0] == top_v);
    assert(sem_seq(hi_seq).subrange(1, 1) =~= Seq::<int>::empty());
    assert(vec_val(hi_seq) == top_v);
    assert(vec_val(delta) == lo_v + top_v * s_top);
    lemma_vec_val_bounded::<T>(lo);
    assert(lo_v < s_top);
    lemma_limb_power_pos((n - 1) as nat);
    assert(s_top > 0);

    // vec_val >= 4*s_top, lo_v < s_top ⇒ top_v * s_top > 3*s_top ⇒ top_v > 3
    assert(top_v * s_top >= 4 * s_top - lo_v);
    assert(top_v * s_top > 3 * s_top) by(nonlinear_arith)
        requires top_v * s_top >= 4 * s_top - lo_v, lo_v < s_top, s_top > 0;
    assert(top_v > 3) by(nonlinear_arith)
        requires top_v * s_top > 3 * s_top, s_top > 0;
}

/// Square-root helper: if `x² ≥ k²` and both x and k are non-negative,
/// then `x ≥ k`.
pub proof fn lemma_sq_monotone(x: int, k: int)
    requires
        x >= 0,
        k >= 0,
        x * x >= k * k,
    ensures
        x >= k,
{
    if x < k {
        // x < k and x >= 0 and k >= 0 ⇒ x*x < k*k, contradiction.
        assert(x * x < k * k) by(nonlinear_arith)
            requires 0 <= x, x < k, 0 <= k;
        assert(false);
    }
}

/// Limb-level helper: if the top limb of δ is greater than 3, then
/// `vec_val(δ) >= 4 * limb_power(n - 1)`. This is the converse direction
/// of `lemma_glitch_completeness_one` (#76).
pub proof fn lemma_glitch_top_implies_magnitude<T: LimbOps>(
    delta: Seq<T>, n: nat,
)
    requires
        n >= 1,
        delta.len() == n as int,
        valid_limbs(delta),
        delta[(n - 1) as int].sem() > 3,
    ensures
        vec_val(delta) >= 4 * limb_power((n - 1) as nat),
{
    let s_top = limb_power((n - 1) as nat);
    let lo = delta.subrange(0, (n - 1) as int);
    assert(valid_limbs(lo)) by {
        assert forall |k: int| 0 <= k < lo.len()
            implies 0 <= (#[trigger] lo[k]).sem() && lo[k].sem() < LIMB_BASE() by {
            assert(lo[k] == delta[k]);
        }
    }
    lemma_vec_val_split::<T>(delta, (n - 1) as nat);
    let lo_v = vec_val(lo);
    let top_v = delta[(n - 1) as int].sem();
    let hi_seq = delta.subrange((n - 1) as int, n as int);
    assert(hi_seq.len() == 1);
    assert(hi_seq[0] == delta[(n - 1) as int]);
    reveal_with_fuel(limbs_val, 2);
    assert(sem_seq(hi_seq).len() == 1);
    assert(sem_seq(hi_seq)[0] == top_v);
    assert(sem_seq(hi_seq).subrange(1, 1) =~= Seq::<int>::empty());
    assert(vec_val(hi_seq) == top_v);
    assert(vec_val(delta) == lo_v + top_v * s_top);
    lemma_limb_power_pos((n - 1) as nat);
    assert(s_top > 0);
    lemma_vec_val_bounded::<T>(lo);
    assert(lo_v >= 0);
    // top_v > 3 ⇒ top_v >= 4 ⇒ top_v * s_top >= 4 * s_top
    assert(top_v >= 4);
    assert(top_v * s_top >= 4 * s_top) by(nonlinear_arith)
        requires top_v >= 4, s_top > 0;
    assert(vec_val(delta) >= 4 * s_top);
}

/// SOUNDNESS: when the kernel's per-component check fires
/// (`δ_re[n-1] > 3` OR `δ_im[n-1] > 3`), `is_glitch(z, delta, tolerance)`
/// holds for any tolerance T such that
/// `T * |Z|² <= 64 * limb_power(2*(n-1))`.
///
/// The 64 comes from: `4 * |δ|² >= 4 * (4*P^(n-1))² = 64 * P^(2*(n-1))`
/// where the inner `4 * P^(n-1)` is the magnitude lower bound from
/// `top > 3` and `4*` is from the is_glitch formula's leading coefficient.
pub proof fn lemma_glitch_check_implies_is_glitch<T: LimbOps>(
    z: SpecComplex,
    dre_seq: Seq<T>, dre_sign: int,
    dim_seq: Seq<T>, dim_sign: int,
    n: nat,
    tolerance: int,
)
    requires
        n >= 1,
        dre_seq.len() == n as int,
        dim_seq.len() == n as int,
        valid_limbs(dre_seq),
        valid_limbs(dim_seq),
        dre_sign == 0 || dre_sign == 1,
        dim_sign == 0 || dim_sign == 1,
        // Kernel check fires
        dre_seq[(n - 1) as int].sem() > 3 || dim_seq[(n - 1) as int].sem() > 3,
        // Tolerance bound
        tolerance * (z.re * z.re + z.im * z.im)
            <= 64 * limb_power((2 * (n - 1)) as nat),
    ensures
        is_glitch(
            z,
            SpecComplex {
                re: signed_val_of(dre_seq, dre_sign),
                im: signed_val_of(dim_seq, dim_sign),
            },
            tolerance,
        ),
{
    let pn1 = limb_power((n - 1) as nat);
    lemma_limb_power_pos((n - 1) as nat);
    assert(pn1 > 0);

    // limb_power(2*(n-1)) == pn1 * pn1, via lemma_limb_power_add(n-1, n-1).
    verus_fixed_point::fixed_point::limb_ops::lemma_limb_power_add(
        (n - 1) as nat, (n - 1) as nat);
    assert(((n - 1) as nat) + ((n - 1) as nat) == (2 * (n - 1)) as nat);
    assert(limb_power((2 * (n - 1)) as nat) == pn1 * pn1);
    let p2n1 = limb_power((2 * (n - 1)) as nat);
    assert(p2n1 == pn1 * pn1);

    let dre_int = signed_val_of(dre_seq, dre_sign);
    let dim_int = signed_val_of(dim_seq, dim_sign);
    let delta = SpecComplex { re: dre_int, im: dim_int };

    // signed_val_of squared equals vec_val squared (since (-x)² = x²).
    let dre_v = vec_val(dre_seq);
    let dim_v = vec_val(dim_seq);
    assert(dre_int == dre_v || dre_int == -dre_v);
    assert(dim_int == dim_v || dim_int == -dim_v);
    assert(dre_int * dre_int == dre_v * dre_v) by(nonlinear_arith)
        requires dre_int == dre_v || dre_int == -dre_v;
    assert(dim_int * dim_int == dim_v * dim_v) by(nonlinear_arith)
        requires dim_int == dim_v || dim_int == -dim_v;

    // Either the re or im top limb exceeds 3 → its vec_val >= 4 * P^(n-1).
    if dre_seq[(n - 1) as int].sem() > 3 {
        lemma_glitch_top_implies_magnitude::<T>(dre_seq, n);
        assert(dre_v >= 4 * pn1);
        // dre_v² >= 16 * pn1²
        assert(dre_v * dre_v >= 16 * (pn1 * pn1)) by(nonlinear_arith)
            requires dre_v >= 4 * pn1, pn1 > 0;
        assert(dre_v * dre_v >= 16 * p2n1);
        assert(dre_int * dre_int >= 16 * p2n1);
    } else {
        assert(dim_seq[(n - 1) as int].sem() > 3);
        lemma_glitch_top_implies_magnitude::<T>(dim_seq, n);
        assert(dim_v >= 4 * pn1);
        assert(dim_v * dim_v >= 16 * (pn1 * pn1)) by(nonlinear_arith)
            requires dim_v >= 4 * pn1, pn1 > 0;
        assert(dim_v * dim_v >= 16 * p2n1);
        assert(dim_int * dim_int >= 16 * p2n1);
    }

    // Now apply lemma_glitch_soundness_int with k² = 16 * p2n1 = (4*pn1)².
    let k = 4 * pn1;
    assert(k >= 0);
    assert(k * k == 16 * (pn1 * pn1)) by(nonlinear_arith) requires k == 4 * pn1;
    assert(k * k == 16 * p2n1);
    assert(delta.re * delta.re >= k * k || delta.im * delta.im >= k * k);

    // The soundness precondition: tolerance * |Z|² <= 4 * k² = 64 * p2n1.
    assert(4 * (k * k) == 64 * p2n1) by(nonlinear_arith)
        requires k * k == 16 * p2n1;
    assert(4 * k * k == 4 * (k * k)) by(nonlinear_arith);
    assert(tolerance * (z.re * z.re + z.im * z.im) <= 4 * k * k);

    lemma_glitch_soundness_int(z, delta, k, tolerance);
}

/// COMPLETENESS (conditional): if `is_glitch(z, delta, T)` holds AND
/// `T * |Z|² >= 128 * limb_power(2*(n-1))`, then the kernel's
/// per-component check fires.
///
/// The factor 2 gap (128 vs soundness's 64) reflects the loss from
/// `max(|δ_re|², |δ_im|²) >= (|δ_re|² + |δ_im|²)/2`: in the worst case
/// the magnitude is split equally between components, so a single
/// component carries only half the total squared magnitude.
///
/// Note this is a CONDITIONAL completeness — strict completeness
/// (`is_glitch ⇒ check fires` for all T) is false because is_glitch
/// can hold with both |Z| and |δ| tiny (e.g., Z=0, δ=ε). The strong
/// tolerance precondition rules out this regime.
pub proof fn lemma_glitch_is_glitch_implies_check<T: LimbOps>(
    z: SpecComplex,
    dre_seq: Seq<T>, dre_sign: int,
    dim_seq: Seq<T>, dim_sign: int,
    n: nat,
    tolerance: int,
)
    requires
        n >= 1,
        dre_seq.len() == n as int,
        dim_seq.len() == n as int,
        valid_limbs(dre_seq),
        valid_limbs(dim_seq),
        dre_sign == 0 || dre_sign == 1,
        dim_sign == 0 || dim_sign == 1,
        // is_glitch holds at the chosen tolerance
        is_glitch(
            z,
            SpecComplex {
                re: signed_val_of(dre_seq, dre_sign),
                im: signed_val_of(dim_seq, dim_sign),
            },
            tolerance,
        ),
        // Strong tolerance precondition: T*|Z|² is at least twice the
        // soundness threshold of 64*P^(2(n-1)).
        tolerance * (z.re * z.re + z.im * z.im)
            >= 128 * limb_power((2 * (n - 1)) as nat),
    ensures
        dre_seq[(n - 1) as int].sem() > 3
            || dim_seq[(n - 1) as int].sem() > 3,
{
    let pn1 = limb_power((n - 1) as nat);
    lemma_limb_power_pos((n - 1) as nat);
    assert(pn1 > 0);

    // p2n1 = limb_power(2*(n-1)) = pn1 * pn1
    verus_fixed_point::fixed_point::limb_ops::lemma_limb_power_add(
        (n - 1) as nat, (n - 1) as nat);
    assert(((n - 1) as nat) + ((n - 1) as nat) == (2 * (n - 1)) as nat);
    let p2n1 = limb_power((2 * (n - 1)) as nat);
    assert(p2n1 == pn1 * pn1);

    let dre_int = signed_val_of(dre_seq, dre_sign);
    let dim_int = signed_val_of(dim_seq, dim_sign);
    let z_mag_sq = z.re * z.re + z.im * z.im;
    let delta_mag_sq = dre_int * dre_int + dim_int * dim_int;

    // From is_glitch: 4 * delta_mag_sq >= tolerance * z_mag_sq.
    assert(4 * delta_mag_sq >= tolerance * z_mag_sq);
    // Combined with the precondition:
    assert(4 * delta_mag_sq >= 128 * p2n1);
    // ⇒ delta_mag_sq >= 32 * p2n1.
    assert(delta_mag_sq >= 32 * p2n1) by(nonlinear_arith)
        requires 4 * delta_mag_sq >= 128 * p2n1;

    // Both component squares are non-negative.
    assert(dre_int * dre_int >= 0) by(nonlinear_arith);
    assert(dim_int * dim_int >= 0) by(nonlinear_arith);

    // max(dre_int², dim_int²) >= delta_mag_sq / 2 >= 16 * p2n1.
    // Equivalently: dre_int² >= 16*p2n1 OR dim_int² >= 16*p2n1.
    if dre_int * dre_int >= 16 * p2n1 {
        // Real component is large enough.
    } else {
        // dim_int² must carry the rest.
        assert(dre_int * dre_int < 16 * p2n1);
        assert(dim_int * dim_int >= delta_mag_sq - dre_int * dre_int);
        assert(dim_int * dim_int >= 32 * p2n1 - 16 * p2n1) by(nonlinear_arith)
            requires
                dim_int * dim_int >= delta_mag_sq - dre_int * dre_int,
                delta_mag_sq >= 32 * p2n1,
                dre_int * dre_int < 16 * p2n1;
        assert(dim_int * dim_int >= 16 * p2n1);
    }
    // After the if-else, at least one of dre_int², dim_int² is >= 16 * p2n1.
    assert(dre_int * dre_int >= 16 * p2n1 || dim_int * dim_int >= 16 * p2n1);

    // signed_val_of squared equals vec_val squared.
    let dre_v = vec_val(dre_seq);
    let dim_v = vec_val(dim_seq);
    assert(dre_int == dre_v || dre_int == -dre_v);
    assert(dim_int == dim_v || dim_int == -dim_v);
    assert(dre_int * dre_int == dre_v * dre_v) by(nonlinear_arith)
        requires dre_int == dre_v || dre_int == -dre_v;
    assert(dim_int * dim_int == dim_v * dim_v) by(nonlinear_arith)
        requires dim_int == dim_v || dim_int == -dim_v;
    assert(dre_v * dre_v >= 16 * p2n1 || dim_v * dim_v >= 16 * p2n1);

    // 16 * p2n1 = 16 * pn1² = (4*pn1)². So vec_val² >= (4*pn1)² ⇒ vec_val >= 4*pn1.
    let four_pn1 = 4 * pn1;
    assert(four_pn1 >= 0);
    assert(four_pn1 * four_pn1 == 16 * (pn1 * pn1)) by(nonlinear_arith)
        requires four_pn1 == 4 * pn1;
    assert(four_pn1 * four_pn1 == 16 * p2n1);

    lemma_vec_val_bounded::<T>(dre_seq);
    lemma_vec_val_bounded::<T>(dim_seq);
    assert(dre_v >= 0);
    assert(dim_v >= 0);

    if dre_v * dre_v >= 16 * p2n1 {
        assert(dre_v * dre_v >= four_pn1 * four_pn1);
        lemma_sq_monotone(dre_v, four_pn1);
        assert(dre_v >= four_pn1);
        assert(dre_v >= 4 * pn1);
        lemma_magnitude_implies_top::<T>(dre_seq, n);
        assert(dre_seq[(n - 1) as int].sem() > 3);
    } else {
        assert(dim_v * dim_v >= 16 * p2n1);
        assert(dim_v * dim_v >= four_pn1 * four_pn1);
        lemma_sq_monotone(dim_v, four_pn1);
        assert(dim_v >= four_pn1);
        assert(dim_v >= 4 * pn1);
        lemma_magnitude_implies_top::<T>(dim_seq, n);
        assert(dim_seq[(n - 1) as int].sem() > 3);
    }
}

} // verus!
