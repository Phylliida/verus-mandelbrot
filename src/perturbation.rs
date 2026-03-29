use vstd::prelude::*;

use verus_algebra::traits::ring::Ring;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;

verus! {

//  ── Complex pair operations (generic over Ring) ─────────────────

///  Complex addition as pairs: (a_re + a_im·i) + (b_re + b_im·i).
pub open spec fn complex_add<T: Ring>(a: (T, T), b: (T, T)) -> (T, T) {
    (a.0.add(b.0), a.1.add(b.1))
}

///  Complex subtraction as pairs.
pub open spec fn complex_sub<T: Ring>(a: (T, T), b: (T, T)) -> (T, T) {
    (a.0.sub(b.0), a.1.sub(b.1))
}

///  Complex squaring: (re + im·i)² = (re² - im²) + (2·re·im)·i.
pub open spec fn complex_square<T: Ring>(z: (T, T)) -> (T, T) {
    (
        z.0.mul(z.0).sub(z.1.mul(z.1)),
        T::one().add(T::one()).mul(z.0.mul(z.1)),
    )
}

///  Mandelbrot step: z² + c as complex pairs.
pub open spec fn mandelbrot_step_pair<T: Ring>(z: (T, T), c: (T, T)) -> (T, T) {
    complex_add(complex_square(z), c)
}

///  Perturbation step: given reference Z, delta δ, and offset Δc,
///  compute the next delta δ' = 2·Z·δ + δ² + Δc (as complex pairs).
///
///  Component form:
///    δ_re' = 2·Zr·δr - 2·Zi·δi + δr² - δi² + Δcr
///    δ_im' = 2·Zr·δi + 2·Zi·δr + 2·δr·δi + Δci
pub open spec fn perturbation_step<T: Ring>(
    z_ref: (T, T),
    delta: (T, T),
    delta_c: (T, T),
) -> (T, T) {
    let two = T::one().add(T::one());
    (
        two.mul(z_ref.0.mul(delta.0))
            .sub(two.mul(z_ref.1.mul(delta.1)))
            .add(delta.0.mul(delta.0))
            .sub(delta.1.mul(delta.1))
            .add(delta_c.0),
        two.mul(z_ref.0.mul(delta.1))
            .add(two.mul(z_ref.1.mul(delta.0)))
            .add(two.mul(delta.0.mul(delta.1)))
            .add(delta_c.1),
    )
}

///  Reference orbit: iterate mandelbrot_step_pair from (0,0) at center c.
pub open spec fn ref_orbit<T: Ring>(c: (T, T), n: nat) -> (T, T)
    decreases n,
{
    if n == 0 {
        (T::zero(), T::zero())
    } else {
        mandelbrot_step_pair(ref_orbit(c, (n - 1) as nat), c)
    }
}

///  Perturbation orbit: iterate perturbation_step using reference orbit at ref_c.
pub open spec fn perturbation_orbit<T: Ring>(
    ref_c: (T, T),
    delta_c: (T, T),
    n: nat,
) -> (T, T)
    decreases n,
{
    if n == 0 {
        (T::zero(), T::zero())
    } else {
        perturbation_step(
            ref_orbit(ref_c, (n - 1) as nat),
            perturbation_orbit(ref_c, delta_c, (n - 1) as nat),
            delta_c,
        )
    }
}

///  Component-wise equivalence for pairs.
pub open spec fn pair_eqv<T: Ring>(a: (T, T), b: (T, T)) -> bool {
    a.0.eqv(b.0) && a.1.eqv(b.1)
}

//  ── Algebraic helper: 6-term subtraction rearrangement ──────────

///  (a+b+c) - (d+e+f) ≡ (a-d) + ((b-e) + (c-f))
///  where "a+b+c" means (a+b)+c (left-associated).
proof fn lemma_sub_triple_rearrange<T: Ring>(
    a: T, b: T, c: T, d: T, e: T, f: T,
)
    ensures
        a.add(b).add(c).sub(d.add(e).add(f)).eqv(
            a.sub(d).add(b.sub(e).add(c.sub(f)))
        ),
{
    let nd = d.neg();
    let ne = e.neg();
    let nf = f.neg();

    //  Convert sub to add-neg on LHS
    T::axiom_sub_is_add_neg(a.add(b).add(c), d.add(e).add(f));
    //  LHS ≡ s1 := ((a+b)+c) + (-(d+e)+f))

    //  Distribute neg: -((d+e)+f) ≡ -(d+e) + (-f) ≡ ((-d)+(-e)) + (-f)
    additive_group_lemmas::lemma_neg_add::<T>(d.add(e), f);
    additive_group_lemmas::lemma_neg_add::<T>(d, e);
    T::axiom_add_congruence_left(d.add(e).neg(), nd.add(ne), nf);
    T::axiom_eqv_transitive(
        d.add(e).add(f).neg(),
        d.add(e).neg().add(nf),
        nd.add(ne).add(nf),
    );

    //  s1 ≡ s2 := ((a+b)+c) + ((nd+ne)+nf)
    let s2 = a.add(b).add(c).add(nd.add(ne).add(nf));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.add(b).add(c),
        d.add(e).add(f).neg(),
        nd.add(ne).add(nf),
    );
    T::axiom_eqv_transitive(
        a.add(b).add(c).sub(d.add(e).add(f)),
        a.add(b).add(c).add(d.add(e).add(f).neg()),
        s2,
    );

    //  s2 ≡ s3 := ((a+b)+(nd+ne)) + (c+nf)   [rearrange_2x2]
    let s3 = a.add(b).add(nd.add(ne)).add(c.add(nf));
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a.add(b), c, nd.add(ne), nf);

    T::axiom_eqv_transitive(
        a.add(b).add(c).sub(d.add(e).add(f)),
        s2, s3,
    );

    //  s3 ≡ s4 := ((a+nd)+(b+ne)) + (c+nf)   [inner rearrange_2x2]
    let s4 = a.add(nd).add(b.add(ne)).add(c.add(nf));
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a, b, nd, ne);
    T::axiom_add_congruence_left(
        a.add(b).add(nd.add(ne)),
        a.add(nd).add(b.add(ne)),
        c.add(nf),
    );
    T::axiom_eqv_transitive(
        a.add(b).add(c).sub(d.add(e).add(f)),
        s3, s4,
    );

    //  s4 ≡ s5 := (a+nd) + ((b+ne) + (c+nf))   [assoc]
    let s5 = a.add(nd).add(b.add(ne).add(c.add(nf)));
    T::axiom_add_associative(a.add(nd), b.add(ne), c.add(nf));
    T::axiom_eqv_transitive(
        a.add(b).add(c).sub(d.add(e).add(f)),
        s4, s5,
    );

    //  s5 ≡ target := (a-d) + ((b-e) + (c-f))   [convert add-neg to sub]
    T::axiom_sub_is_add_neg(a, d);
    T::axiom_sub_is_add_neg(b, e);
    T::axiom_sub_is_add_neg(c, f);
    T::axiom_eqv_symmetric(a.sub(d), a.add(nd));
    T::axiom_eqv_symmetric(b.sub(e), b.add(ne));
    T::axiom_eqv_symmetric(c.sub(f), c.add(nf));
    additive_group_lemmas::lemma_add_congruence::<T>(
        b.add(ne), b.sub(e), c.add(nf), c.sub(f),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.add(nd), a.sub(d),
        b.add(ne).add(c.add(nf)), b.sub(e).add(c.sub(f)),
    );
    T::axiom_eqv_transitive(
        a.add(b).add(c).sub(d.add(e).add(f)),
        s5,
        a.sub(d).add(b.sub(e).add(c.sub(f))),
    );
}

//  ── Helper: complex square perturbation, real part ──────────────

///  (Zr+dr)² - (Zi+di)² ≡ (Zr²-Zi²) + (2·Zr·dr - 2·Zi·di + dr² - di²)
pub proof fn lemma_complex_square_perturbation_re<T: Ring>(
    zr: T, zi: T, dr: T, di: T,
)
    ensures
        zr.add(dr).mul(zr.add(dr)).sub(zi.add(di).mul(zi.add(di))).eqv(
            zr.mul(zr).sub(zi.mul(zi)).add(
                T::one().add(T::one()).mul(zr.mul(dr))
                    .sub(T::one().add(T::one()).mul(zi.mul(di)))
                    .add(dr.mul(dr))
                    .sub(di.mul(di))
            )
        ),
{
    let two = T::one().add(T::one());

    //  Expand (Zr+dr)² = zr² + 2·zr·dr + dr²
    ring_lemmas::lemma_square_expand::<T>(zr, dr);
    //  Expand (Zi+di)² = zi² + 2·zi·di + di²
    ring_lemmas::lemma_square_expand::<T>(zi, di);

    let lhs_a = zr.add(dr).mul(zr.add(dr));
    let lhs_b = zi.add(di).mul(zi.add(di));
    let rhs_a = zr.mul(zr).add(two.mul(zr.mul(dr))).add(dr.mul(dr));
    let rhs_b = zi.mul(zi).add(two.mul(zi.mul(di))).add(di.mul(di));

    //  Step 1: lhs_a - lhs_b ≡ rhs_a - rhs_b (sub congruence)
    T::axiom_sub_is_add_neg(lhs_a, lhs_b);
    T::axiom_sub_is_add_neg(rhs_a, rhs_b);
    T::axiom_neg_congruence(lhs_b, rhs_b);
    additive_group_lemmas::lemma_add_congruence::<T>(lhs_a, rhs_a, lhs_b.neg(), rhs_b.neg());
    T::axiom_eqv_transitive(lhs_a.sub(lhs_b), lhs_a.add(lhs_b.neg()), rhs_a.add(rhs_b.neg()));
    T::axiom_eqv_symmetric(rhs_a.sub(rhs_b), rhs_a.add(rhs_b.neg()));
    T::axiom_eqv_transitive(lhs_a.sub(lhs_b), rhs_a.add(rhs_b.neg()), rhs_a.sub(rhs_b));

    //  Step 2: rhs_a - rhs_b ≡ (zr²-zi²) + ((2zrdr - 2zidi) + (dr² - di²))
    //  This is the 6-term rearrangement: (a+b+c) - (d+e+f) ≡ (a-d) + ((b-e) + (c-f))
    lemma_sub_triple_rearrange::<T>(
        zr.mul(zr), two.mul(zr.mul(dr)), dr.mul(dr),
        zi.mul(zi), two.mul(zi.mul(di)), di.mul(di),
    );

    //  Step 3: Chain
    T::axiom_eqv_transitive(
        lhs_a.sub(lhs_b),
        rhs_a.sub(rhs_b),
        zr.mul(zr).sub(zi.mul(zi)).add(
            two.mul(zr.mul(dr)).sub(two.mul(zi.mul(di))).add(dr.mul(dr).sub(di.mul(di)))
        ),
    );

    //  Step 4: Show the inner grouping matches the target.
    //  Current: (2zrdr - 2zidi) + (dr² - di²)
    //  Target:  ((2zrdr - 2zidi) + dr²) - di²
    //  These differ only in association:
    //  (X) + (Y - Z) vs (X + Y) - Z  where X = 2zrdr-2zidi, Y = dr², Z = di²
    //  (X + (Y + (-Z))) vs ((X + Y) + (-Z)) — these are equal by assoc (reversed).

    let x_term = two.mul(zr.mul(dr)).sub(two.mul(zi.mul(di)));
    T::axiom_sub_is_add_neg(dr.mul(dr), di.mul(di));
    //  dr²-di² ≡ dr² + (-di²)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        x_term,
        dr.mul(dr).sub(di.mul(di)),
        dr.mul(dr).add(di.mul(di).neg()),
    );
    //  x_term + (dr²-di²) ≡ x_term + (dr² + (-di²))

    //  Assoc: x_term + (dr² + (-di²)) ≡ (x_term + dr²) + (-di²)
    T::axiom_add_associative(x_term, dr.mul(dr), di.mul(di).neg());
    T::axiom_eqv_symmetric(
        x_term.add(dr.mul(dr).add(di.mul(di).neg())),
        x_term.add(dr.mul(dr)).add(di.mul(di).neg()),
    );
    T::axiom_eqv_transitive(
        x_term.add(dr.mul(dr).sub(di.mul(di))),
        x_term.add(dr.mul(dr).add(di.mul(di).neg())),
        x_term.add(dr.mul(dr)).add(di.mul(di).neg()),
    );

    //  Convert back: (x_term + dr²) + (-di²) ≡ (x_term + dr²) - di²
    T::axiom_sub_is_add_neg(x_term.add(dr.mul(dr)), di.mul(di));
    T::axiom_eqv_symmetric(
        x_term.add(dr.mul(dr)).sub(di.mul(di)),
        x_term.add(dr.mul(dr)).add(di.mul(di).neg()),
    );
    T::axiom_eqv_transitive(
        x_term.add(dr.mul(dr).sub(di.mul(di))),
        x_term.add(dr.mul(dr)).add(di.mul(di).neg()),
        x_term.add(dr.mul(dr)).sub(di.mul(di)),
    );

    //  Now lift to the outer add:
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        zr.mul(zr).sub(zi.mul(zi)),
        x_term.add(dr.mul(dr).sub(di.mul(di))),
        x_term.add(dr.mul(dr)).sub(di.mul(di)),
    );

    //  Final chain
    T::axiom_eqv_transitive(
        lhs_a.sub(lhs_b),
        zr.mul(zr).sub(zi.mul(zi)).add(
            x_term.add(dr.mul(dr).sub(di.mul(di)))
        ),
        zr.mul(zr).sub(zi.mul(zi)).add(
            x_term.add(dr.mul(dr)).sub(di.mul(di))
        ),
    );
}

//  ── Helper: complex square perturbation, imaginary part ─────────

///  2·(Zr+dr)·(Zi+di) ≡ 2·Zr·Zi + (2·Zr·di + 2·Zi·dr + 2·dr·di)
pub proof fn lemma_complex_square_perturbation_im<T: Ring>(
    zr: T, zi: T, dr: T, di: T,
)
    ensures
        T::one().add(T::one()).mul(zr.add(dr).mul(zi.add(di))).eqv(
            T::one().add(T::one()).mul(zr.mul(zi)).add(
                T::one().add(T::one()).mul(zr.mul(di))
                    .add(T::one().add(T::one()).mul(zi.mul(dr)))
                    .add(T::one().add(T::one()).mul(dr.mul(di)))
            )
        ),
{
    let two = T::one().add(T::one());

    //  Distribute: (zr+dr)*(zi+di) ≡ zr*zi + zr*di + dr*zi + dr*di
    T::axiom_mul_distributes_left(zr.add(dr), zi, di);
    ring_lemmas::lemma_mul_distributes_right::<T>(zr, dr, zi);
    ring_lemmas::lemma_mul_distributes_right::<T>(zr, dr, di);
    additive_group_lemmas::lemma_add_congruence::<T>(
        zr.add(dr).mul(zi), zr.mul(zi).add(dr.mul(zi)),
        zr.add(dr).mul(di), zr.mul(di).add(dr.mul(di)),
    );
    T::axiom_eqv_transitive(
        zr.add(dr).mul(zi.add(di)),
        zr.add(dr).mul(zi).add(zr.add(dr).mul(di)),
        zr.mul(zi).add(dr.mul(zi)).add(zr.mul(di).add(dr.mul(di))),
    );

    //  Rearrange: (zr*zi + dr*zi) + (zr*di + dr*di) ≡ (zr*zi + zr*di) + (dr*zi + dr*di)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        zr.mul(zi), dr.mul(zi), zr.mul(di), dr.mul(di),
    );
    T::axiom_eqv_transitive(
        zr.add(dr).mul(zi.add(di)),
        zr.mul(zi).add(dr.mul(zi)).add(zr.mul(di).add(dr.mul(di))),
        zr.mul(zi).add(zr.mul(di)).add(dr.mul(zi).add(dr.mul(di))),
    );

    //  Multiply by 2, using congruence
    ring_lemmas::lemma_mul_congruence_right::<T>(
        two,
        zr.add(dr).mul(zi.add(di)),
        zr.mul(zi).add(zr.mul(di)).add(dr.mul(zi).add(dr.mul(di))),
    );

    //  Distribute 2 over the sum: 2*((A+B)+(C+D)) ≡ 2*(A+B) + 2*(C+D)
    let ab = zr.mul(zi).add(zr.mul(di));
    let cd = dr.mul(zi).add(dr.mul(di));
    T::axiom_mul_distributes_left(two, ab, cd);
    T::axiom_eqv_transitive(
        two.mul(zr.add(dr).mul(zi.add(di))),
        two.mul(ab.add(cd)),
        two.mul(ab).add(two.mul(cd)),
    );

    //  Further distribute: 2*(A+B) = 2*A + 2*B
    T::axiom_mul_distributes_left(two, zr.mul(zi), zr.mul(di));
    T::axiom_mul_distributes_left(two, dr.mul(zi), dr.mul(di));
    additive_group_lemmas::lemma_add_congruence::<T>(
        two.mul(ab), two.mul(zr.mul(zi)).add(two.mul(zr.mul(di))),
        two.mul(cd), two.mul(dr.mul(zi)).add(two.mul(dr.mul(di))),
    );
    T::axiom_eqv_transitive(
        two.mul(zr.add(dr).mul(zi.add(di))),
        two.mul(ab).add(two.mul(cd)),
        two.mul(zr.mul(zi)).add(two.mul(zr.mul(di))).add(
            two.mul(dr.mul(zi)).add(two.mul(dr.mul(di)))
        ),
    );

    //  Commute dr*zi → zi*dr for the ensures clause
    T::axiom_mul_commutative(dr, zi);
    ring_lemmas::lemma_mul_congruence_right::<T>(two, dr.mul(zi), zi.mul(dr));
    T::axiom_add_congruence_left(
        two.mul(dr.mul(zi)), two.mul(zi.mul(dr)), two.mul(dr.mul(di)),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        two.mul(zr.mul(zi)).add(two.mul(zr.mul(di))),
        two.mul(dr.mul(zi)).add(two.mul(dr.mul(di))),
        two.mul(zi.mul(dr)).add(two.mul(dr.mul(di))),
    );
    T::axiom_eqv_transitive(
        two.mul(zr.add(dr).mul(zi.add(di))),
        two.mul(zr.mul(zi)).add(two.mul(zr.mul(di))).add(
            two.mul(dr.mul(zi)).add(two.mul(dr.mul(di)))
        ),
        two.mul(zr.mul(zi)).add(two.mul(zr.mul(di))).add(
            two.mul(zi.mul(dr)).add(two.mul(dr.mul(di)))
        ),
    );

    //  Reassociate: (A + B) + (C + D) ≡ A + (B + (C + D)) ≡ A + ((B + C) + D)
    T::axiom_add_associative(
        two.mul(zr.mul(zi)), two.mul(zr.mul(di)),
        two.mul(zi.mul(dr)).add(two.mul(dr.mul(di))),
    );
    T::axiom_eqv_transitive(
        two.mul(zr.add(dr).mul(zi.add(di))),
        two.mul(zr.mul(zi)).add(two.mul(zr.mul(di))).add(
            two.mul(zi.mul(dr)).add(two.mul(dr.mul(di)))
        ),
        two.mul(zr.mul(zi)).add(
            two.mul(zr.mul(di)).add(
                two.mul(zi.mul(dr)).add(two.mul(dr.mul(di)))
            )
        ),
    );

    //  Inner assoc: B + (C + D) ≡ (B + C) + D
    T::axiom_add_associative(
        two.mul(zr.mul(di)), two.mul(zi.mul(dr)), two.mul(dr.mul(di)),
    );
    T::axiom_eqv_symmetric(
        two.mul(zr.mul(di)).add(two.mul(zi.mul(dr))).add(two.mul(dr.mul(di))),
        two.mul(zr.mul(di)).add(two.mul(zi.mul(dr)).add(two.mul(dr.mul(di)))),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        two.mul(zr.mul(zi)),
        two.mul(zr.mul(di)).add(two.mul(zi.mul(dr)).add(two.mul(dr.mul(di)))),
        two.mul(zr.mul(di)).add(two.mul(zi.mul(dr))).add(two.mul(dr.mul(di))),
    );
    T::axiom_eqv_transitive(
        two.mul(zr.add(dr).mul(zi.add(di))),
        two.mul(zr.mul(zi)).add(
            two.mul(zr.mul(di)).add(
                two.mul(zi.mul(dr)).add(two.mul(dr.mul(di)))
            )
        ),
        two.mul(zr.mul(zi)).add(
            two.mul(zr.mul(di)).add(two.mul(zi.mul(dr))).add(two.mul(dr.mul(di)))
        ),
    );
}

//  ── Main Theorem ────────────────────────────────────────────────

///  THE MAIN THEOREM: ref_orbit(C + Δc, n) ≡ ref_orbit(C, n) + perturbation_orbit(C, Δc, n)
///  for all n. The actual orbit at pixel c = C + Δc equals the reference orbit plus
///  the perturbation delta, component-wise up to Ring equivalence.
pub proof fn lemma_perturbation_correct<T: Ring>(
    ref_c: (T, T),
    delta_c: (T, T),
    n: nat,
)
    ensures
        ref_orbit(complex_add(ref_c, delta_c), n).0.eqv(
            ref_orbit(ref_c, n).0.add(perturbation_orbit(ref_c, delta_c, n).0)),
        ref_orbit(complex_add(ref_c, delta_c), n).1.eqv(
            ref_orbit(ref_c, n).1.add(perturbation_orbit(ref_c, delta_c, n).1)),
    decreases n,
{
    if n == 0 {
        //  Both orbits start at (0,0). Need: 0 ≡ 0 + 0.
        T::axiom_add_zero_right(T::zero());
        T::axiom_eqv_symmetric(T::zero().add(T::zero()), T::zero());
    } else {
        let prev = (n - 1) as nat;
        lemma_perturbation_correct::<T>(ref_c, delta_c, prev);

        let c_full = complex_add(ref_c, delta_c);
        let zf = ref_orbit(c_full, prev);       //  full orbit at n-1
        let zr = ref_orbit(ref_c, prev);         //  reference orbit at n-1
        let dp = perturbation_orbit(ref_c, delta_c, prev); //  delta at n-1

        //  IH: zf.0 ≡ zr.0 + dp.0,  zf.1 ≡ zr.1 + dp.1

        //  Real part
        lemma_perturbation_step_re::<T>(
            zr.0, zr.1, dp.0, dp.1, zf.0, zf.1, ref_c.0, delta_c.0,
        );
        //  Imaginary part
        lemma_perturbation_step_im::<T>(
            zr.0, zr.1, dp.0, dp.1, zf.0, zf.1, ref_c.1, delta_c.1,
        );
    }
}

///  Helper for the real part of the inductive step.
proof fn lemma_perturbation_step_re<T: Ring>(
    zr: T, zi: T,        //  reference Z components
    dr: T, di: T,         //  delta components
    zf_re: T, zf_im: T,  //  full orbit components
    cr: T, dcr: T,        //  reference c_re, delta c_re
)
    requires
        zf_re.eqv(zr.add(dr)),
        zf_im.eqv(zi.add(di)),
    ensures
        zf_re.mul(zf_re).sub(zf_im.mul(zf_im)).add(cr.add(dcr)).eqv(
            zr.mul(zr).sub(zi.mul(zi)).add(cr).add(
                T::one().add(T::one()).mul(zr.mul(dr))
                    .sub(T::one().add(T::one()).mul(zi.mul(di)))
                    .add(dr.mul(dr))
                    .sub(di.mul(di))
                    .add(dcr)
            )
        ),
{
    let two = T::one().add(T::one());

    //  Step 1: Substitute zf ≡ zr+dr, zf_im ≡ zi+di
    ring_lemmas::lemma_mul_congruence::<T>(zf_re, zr.add(dr), zf_re, zr.add(dr));
    ring_lemmas::lemma_mul_congruence::<T>(zf_im, zi.add(di), zf_im, zi.add(di));

    //  zf_re² - zf_im² ≡ (zr+dr)² - (zi+di)²
    T::axiom_neg_congruence(zf_im.mul(zf_im), zi.add(di).mul(zi.add(di)));
    T::axiom_sub_is_add_neg(zf_re.mul(zf_re), zf_im.mul(zf_im));
    T::axiom_sub_is_add_neg(zr.add(dr).mul(zr.add(dr)), zi.add(di).mul(zi.add(di)));
    additive_group_lemmas::lemma_add_congruence::<T>(
        zf_re.mul(zf_re), zr.add(dr).mul(zr.add(dr)),
        zf_im.mul(zf_im).neg(), zi.add(di).mul(zi.add(di)).neg(),
    );
    T::axiom_eqv_transitive(
        zf_re.mul(zf_re).sub(zf_im.mul(zf_im)),
        zf_re.mul(zf_re).add(zf_im.mul(zf_im).neg()),
        zr.add(dr).mul(zr.add(dr)).add(zi.add(di).mul(zi.add(di)).neg()),
    );
    T::axiom_eqv_symmetric(
        zr.add(dr).mul(zr.add(dr)).sub(zi.add(di).mul(zi.add(di))),
        zr.add(dr).mul(zr.add(dr)).add(zi.add(di).mul(zi.add(di)).neg()),
    );
    T::axiom_eqv_transitive(
        zf_re.mul(zf_re).sub(zf_im.mul(zf_im)),
        zr.add(dr).mul(zr.add(dr)).add(zi.add(di).mul(zi.add(di)).neg()),
        zr.add(dr).mul(zr.add(dr)).sub(zi.add(di).mul(zi.add(di))),
    );

    //  + (cr + dcr)
    T::axiom_eqv_reflexive(cr.add(dcr));
    additive_group_lemmas::lemma_add_congruence::<T>(
        zf_re.mul(zf_re).sub(zf_im.mul(zf_im)),
        zr.add(dr).mul(zr.add(dr)).sub(zi.add(di).mul(zi.add(di))),
        cr.add(dcr), cr.add(dcr),
    );
    //  LHS ≡ ((zr+dr)² - (zi+di)²) + (cr + dcr)

    //  Step 2: Apply complex square perturbation on real part
    lemma_complex_square_perturbation_re::<T>(zr, zi, dr, di);

    let pert_re = two.mul(zr.mul(dr)).sub(two.mul(zi.mul(di)))
        .add(dr.mul(dr)).sub(di.mul(di));

    additive_group_lemmas::lemma_add_congruence::<T>(
        zr.add(dr).mul(zr.add(dr)).sub(zi.add(di).mul(zi.add(di))),
        zr.mul(zr).sub(zi.mul(zi)).add(pert_re),
        cr.add(dcr), cr.add(dcr),
    );
    T::axiom_eqv_transitive(
        zf_re.mul(zf_re).sub(zf_im.mul(zf_im)).add(cr.add(dcr)),
        zr.add(dr).mul(zr.add(dr)).sub(zi.add(di).mul(zi.add(di))).add(cr.add(dcr)),
        zr.mul(zr).sub(zi.mul(zi)).add(pert_re).add(cr.add(dcr)),
    );

    //  Step 3: Rearrange (A + B) + (C + D) ≡ (A + C) + (B + D)
    //  where A = zr²-zi², B = pert_re, C = cr, D = dcr
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        zr.mul(zr).sub(zi.mul(zi)), pert_re, cr, dcr,
    );
    T::axiom_eqv_transitive(
        zf_re.mul(zf_re).sub(zf_im.mul(zf_im)).add(cr.add(dcr)),
        zr.mul(zr).sub(zi.mul(zi)).add(pert_re).add(cr.add(dcr)),
        zr.mul(zr).sub(zi.mul(zi)).add(cr).add(pert_re.add(dcr)),
    );
}

///  Helper for the imaginary part of the inductive step.
proof fn lemma_perturbation_step_im<T: Ring>(
    zr: T, zi: T,
    dr: T, di: T,
    zf_re: T, zf_im: T,
    ci: T, dci: T,
)
    requires
        zf_re.eqv(zr.add(dr)),
        zf_im.eqv(zi.add(di)),
    ensures
        T::one().add(T::one()).mul(zf_re.mul(zf_im)).add(ci.add(dci)).eqv(
            T::one().add(T::one()).mul(zr.mul(zi)).add(ci).add(
                T::one().add(T::one()).mul(zr.mul(di))
                    .add(T::one().add(T::one()).mul(zi.mul(dr)))
                    .add(T::one().add(T::one()).mul(dr.mul(di)))
                    .add(dci)
            )
        ),
{
    let two = T::one().add(T::one());

    //  Step 1: Replace zf_re*zf_im with (zr+dr)*(zi+di)
    ring_lemmas::lemma_mul_congruence::<T>(zf_re, zr.add(dr), zf_im, zi.add(di));
    ring_lemmas::lemma_mul_congruence_right::<T>(two, zf_re.mul(zf_im), zr.add(dr).mul(zi.add(di)));
    T::axiom_eqv_reflexive(ci.add(dci));
    additive_group_lemmas::lemma_add_congruence::<T>(
        two.mul(zf_re.mul(zf_im)),
        two.mul(zr.add(dr).mul(zi.add(di))),
        ci.add(dci), ci.add(dci),
    );

    //  Step 2: Apply imaginary helper
    lemma_complex_square_perturbation_im::<T>(zr, zi, dr, di);

    let pert_im = two.mul(zr.mul(di))
        .add(two.mul(zi.mul(dr)))
        .add(two.mul(dr.mul(di)));

    additive_group_lemmas::lemma_add_congruence::<T>(
        two.mul(zr.add(dr).mul(zi.add(di))),
        two.mul(zr.mul(zi)).add(pert_im),
        ci.add(dci), ci.add(dci),
    );
    T::axiom_eqv_transitive(
        two.mul(zf_re.mul(zf_im)).add(ci.add(dci)),
        two.mul(zr.add(dr).mul(zi.add(di))).add(ci.add(dci)),
        two.mul(zr.mul(zi)).add(pert_im).add(ci.add(dci)),
    );

    //  Step 3: Rearrange (A + B) + (C + D) ≡ (A + C) + (B + D)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        two.mul(zr.mul(zi)), pert_im, ci, dci,
    );
    T::axiom_eqv_transitive(
        two.mul(zf_re.mul(zf_im)).add(ci.add(dci)),
        two.mul(zr.mul(zi)).add(pert_im).add(ci.add(dci)),
        two.mul(zr.mul(zi)).add(ci).add(pert_im.add(dci)),
    );
}

} //  verus!
