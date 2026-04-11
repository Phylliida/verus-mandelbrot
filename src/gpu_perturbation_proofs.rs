/// Helper proof lemmas for the GPU perturbation kernel.
///
/// Companion module to `gpu_perturbation_entry.rs`. Contains spec functions
/// and bridge lemmas needed by `perturbation_iteration_step`'s value
/// postcondition (Task #81 Stage B), kept here to avoid polluting
/// the kernel function's Z3 context.

use vstd::prelude::*;
use verus_fixed_point::fixed_point::limb_ops::{
    LIMB_BASE, LimbOps, limb_power, vec_val, valid_limbs, lemma_vec_val_bounded,
};
use verus_fixed_point::fixed_point::limb_ops_proofs::signed_val_of;

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

} // verus!
