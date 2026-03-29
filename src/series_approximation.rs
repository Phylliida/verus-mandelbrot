use vstd::prelude::*;

use verus_algebra::traits::ring::Ring;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::determinant;
use crate::perturbation::*;

verus! {

//  ── Complex multiplication ─────────────────────────────────────────

///  Complex multiplication: (a_re + a_im·i) * (b_re + b_im·i) = (ac-bd, ad+bc).
pub open spec fn complex_mul<T: Ring>(a: (T, T), b: (T, T)) -> (T, T) {
    (a.0.mul(b.0).sub(a.1.mul(b.1)), a.0.mul(b.1).add(a.1.mul(b.0)))
}

///  Complex multiplicative identity: (1, 0).
pub open spec fn complex_one<T: Ring>() -> (T, T) {
    (T::one(), T::zero())
}

///  Complex additive identity: (0, 0).
pub open spec fn complex_zero<T: Ring>() -> (T, T) {
    (T::zero(), T::zero())
}

//  ── SA coefficient recurrence ──────────────────────────────────────

///  Series Approximation coefficient: A_0 = (0,0), A_{n+1} = 2·Z_n·A_n + 1.
///  Component form (matching perturbation_step structure):
///    A_re' = 2·Zr·Ar - 2·Zi·Ai + 1
///    A_im' = 2·Zr·Ai + 2·Zi·Ar
pub open spec fn sa_coeff<T: Ring>(c: (T, T), n: nat) -> (T, T)
    decreases n,
{
    if n == 0 {
        complex_zero()
    } else {
        let z = ref_orbit(c, (n - 1) as nat);
        let a = sa_coeff(c, (n - 1) as nat);
        let two = T::one().add(T::one());
        (
            two.mul(z.0.mul(a.0)).sub(two.mul(z.1.mul(a.1))).add(T::one()),
            two.mul(z.0.mul(a.1)).add(two.mul(z.1.mul(a.0))),
        )
    }
}

///  SA error: perturbation_orbit(c, dc, n) - sa_coeff(c, n) * dc.
pub open spec fn sa_error<T: Ring>(c: (T, T), dc: (T, T), n: nat) -> (T, T) {
    complex_sub(perturbation_orbit(c, dc, n), complex_mul(sa_coeff(c, n), dc))
}

//  ── Helper: a - 0 ≡ a ─────────────────────────────────────────────

proof fn lemma_sub_zero<T: Ring>(a: T)
    ensures a.sub(T::zero()).eqv(a),
{
    T::axiom_sub_is_add_neg(a, T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    additive_group_lemmas::lemma_add_congruence_right::<T>(a, T::zero().neg(), T::zero());
    T::axiom_eqv_transitive(a.sub(T::zero()), a.add(T::zero().neg()), a.add(T::zero()));
    T::axiom_add_zero_right(a);
    T::axiom_eqv_transitive(a.sub(T::zero()), a.add(T::zero()), a);
}

//  ── Lemma 1: a · (0,0) ≡ (0,0) ────────────────────────────────────

pub proof fn lemma_complex_mul_zero_right<T: Ring>(a: (T, T))
    ensures
        complex_mul(a, complex_zero::<T>()).0.eqv(T::zero()),
        complex_mul(a, complex_zero::<T>()).1.eqv(T::zero()),
{
    let z = T::zero();
    //  Re: a.0*0 - a.1*0 ≡ 0 - 0 ≡ 0
    T::axiom_mul_zero_right(a.0);
    T::axiom_mul_zero_right(a.1);
    additive_group_lemmas::lemma_sub_congruence::<T>(a.0.mul(z), z, a.1.mul(z), z);
    additive_group_lemmas::lemma_sub_self::<T>(z);
    T::axiom_eqv_transitive(a.0.mul(z).sub(a.1.mul(z)), z.sub(z), z);

    //  Im: a.0*0 + a.1*0 ≡ 0 + 0 ≡ 0
    additive_group_lemmas::lemma_add_congruence::<T>(a.0.mul(z), z, a.1.mul(z), z);
    T::axiom_add_zero_right(z);
    T::axiom_eqv_transitive(a.0.mul(z).add(a.1.mul(z)), z.add(z), z);
}

//  ── Lemma 2: (1,0) · b ≡ b ────────────────────────────────────────

pub proof fn lemma_complex_mul_one_left<T: Ring>(b: (T, T))
    ensures
        complex_mul(complex_one::<T>(), b).0.eqv(b.0),
        complex_mul(complex_one::<T>(), b).1.eqv(b.1),
{
    let one = T::one();
    let z = T::zero();
    //  Re: 1*b.0 - 0*b.1 ≡ b.0 - 0 ≡ b.0
    ring_lemmas::lemma_mul_one_left::<T>(b.0);
    ring_lemmas::lemma_mul_zero_left::<T>(b.1);
    additive_group_lemmas::lemma_sub_congruence::<T>(one.mul(b.0), b.0, z.mul(b.1), z);
    lemma_sub_zero::<T>(b.0);
    T::axiom_eqv_transitive(one.mul(b.0).sub(z.mul(b.1)), b.0.sub(z), b.0);

    //  Im: 1*b.1 + 0*b.0 ≡ b.1 + 0 ≡ b.1
    ring_lemmas::lemma_mul_one_left::<T>(b.1);
    ring_lemmas::lemma_mul_zero_left::<T>(b.0);
    additive_group_lemmas::lemma_add_congruence::<T>(one.mul(b.1), b.1, z.mul(b.0), z);
    T::axiom_add_zero_right(b.1);
    T::axiom_eqv_transitive(one.mul(b.1).add(z.mul(b.0)), b.1.add(z), b.1);
}

//  ── Lemma 3: (s,0) · (a,b) ≡ (s·a, s·b) ──────────────────────────

pub proof fn lemma_complex_mul_scalar<T: Ring>(s: T, a: T, b: T)
    ensures
        complex_mul::<T>((s, T::zero()), (a, b)).0.eqv(s.mul(a)),
        complex_mul::<T>((s, T::zero()), (a, b)).1.eqv(s.mul(b)),
{
    let z = T::zero();
    //  Re: s*a - 0*b ≡ s*a - 0 ≡ s*a
    T::axiom_eqv_reflexive(s.mul(a));
    ring_lemmas::lemma_mul_zero_left::<T>(b);
    additive_group_lemmas::lemma_sub_congruence::<T>(s.mul(a), s.mul(a), z.mul(b), z);
    lemma_sub_zero::<T>(s.mul(a));
    T::axiom_eqv_transitive(s.mul(a).sub(z.mul(b)), s.mul(a).sub(z), s.mul(a));

    //  Im: s*b + 0*a ≡ s*b + 0 ≡ s*b
    T::axiom_eqv_reflexive(s.mul(b));
    ring_lemmas::lemma_mul_zero_left::<T>(a);
    additive_group_lemmas::lemma_add_congruence::<T>(s.mul(b), s.mul(b), z.mul(a), z);
    T::axiom_add_zero_right(s.mul(b));
    T::axiom_eqv_transitive(s.mul(b).add(z.mul(a)), s.mul(b).add(z), s.mul(b));
}

//  ── Lemma 4: complex_mul congruence ────────────────────────────────

pub proof fn lemma_complex_mul_congruence<T: Ring>(
    a1: (T, T), a2: (T, T), b1: (T, T), b2: (T, T),
)
    requires pair_eqv(a1, a2), pair_eqv(b1, b2),
    ensures pair_eqv(complex_mul(a1, b1), complex_mul(a2, b2)),
{
    //  Re: a.0*b.0 - a.1*b.1
    ring_lemmas::lemma_mul_congruence::<T>(a1.0, a2.0, b1.0, b2.0);
    ring_lemmas::lemma_mul_congruence::<T>(a1.1, a2.1, b1.1, b2.1);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a1.0.mul(b1.0), a2.0.mul(b2.0),
        a1.1.mul(b1.1), a2.1.mul(b2.1),
    );
    //  Im: a.0*b.1 + a.1*b.0
    ring_lemmas::lemma_mul_congruence::<T>(a1.0, a2.0, b1.1, b2.1);
    ring_lemmas::lemma_mul_congruence::<T>(a1.1, a2.1, b1.0, b2.0);
    additive_group_lemmas::lemma_add_congruence::<T>(
        a1.0.mul(b1.1), a2.0.mul(b2.1),
        a1.1.mul(b1.0), a2.1.mul(b2.0),
    );
}

//  ── Lemma 5: complex_add congruence ────────────────────────────────

pub proof fn lemma_complex_add_congruence<T: Ring>(
    a1: (T, T), a2: (T, T), b1: (T, T), b2: (T, T),
)
    requires pair_eqv(a1, a2), pair_eqv(b1, b2),
    ensures pair_eqv(complex_add(a1, b1), complex_add(a2, b2)),
{
    additive_group_lemmas::lemma_add_congruence::<T>(a1.0, a2.0, b1.0, b2.0);
    additive_group_lemmas::lemma_add_congruence::<T>(a1.1, a2.1, b1.1, b2.1);
}

//  ── Lemma 5b: complex_sub congruence ───────────────────────────────

pub proof fn lemma_complex_sub_congruence<T: Ring>(
    a1: (T, T), a2: (T, T), b1: (T, T), b2: (T, T),
)
    requires pair_eqv(a1, a2), pair_eqv(b1, b2),
    ensures pair_eqv(complex_sub(a1, b1), complex_sub(a2, b2)),
{
    additive_group_lemmas::lemma_sub_congruence::<T>(a1.0, a2.0, b1.0, b2.0);
    additive_group_lemmas::lemma_sub_congruence::<T>(a1.1, a2.1, b1.1, b2.1);
}

//  ── Lemma 6: complex_mul distributes over add ──────────────────────

///  a · (b + c) ≡ a·b + a·c  (complex multiplication distributes over complex addition).
pub proof fn lemma_complex_mul_distributes_over_add<T: Ring>(
    a: (T, T), b: (T, T), c: (T, T),
)
    ensures
        pair_eqv(
            complex_mul(a, complex_add(b, c)),
            complex_add(complex_mul(a, b), complex_mul(a, c)),
        ),
{
    lemma_complex_mul_dist_re::<T>(a, b, c);
    lemma_complex_mul_dist_im::<T>(a, b, c);
}

///  Real part helper for distributivity.
proof fn lemma_complex_mul_dist_re<T: Ring>(a: (T, T), b: (T, T), c: (T, T))
    ensures
        complex_mul(a, complex_add(b, c)).0.eqv(
            complex_add(complex_mul(a, b), complex_mul(a, c)).0),
{
    //  LHS re = a.0*(b.0+c.0) - a.1*(b.1+c.1)
    //  RHS re = (a.0*b.0 - a.1*b.1) + (a.0*c.0 - a.1*c.1)

    //  Distribute: a.0*(b.0+c.0) ≡ a.0*b.0 + a.0*c.0
    T::axiom_mul_distributes_left(a.0, b.0, c.0);
    //  Distribute: a.1*(b.1+c.1) ≡ a.1*b.1 + a.1*c.1
    T::axiom_mul_distributes_left(a.1, b.1, c.1);

    //  Sub congruence: LHS re ≡ (a.0*b.0 + a.0*c.0) - (a.1*b.1 + a.1*c.1)
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.0.mul(b.0.add(c.0)), a.0.mul(b.0).add(a.0.mul(c.0)),
        a.1.mul(b.1.add(c.1)), a.1.mul(b.1).add(a.1.mul(c.1)),
    );

    //  (p+q) - (r+s) ≡ (p-r) + (q-s)
    determinant::lemma_sub_pairs::<T>(
        a.0.mul(b.0), a.0.mul(c.0), a.1.mul(b.1), a.1.mul(c.1),
    );

    //  Chain
    T::axiom_eqv_transitive(
        a.0.mul(b.0.add(c.0)).sub(a.1.mul(b.1.add(c.1))),
        a.0.mul(b.0).add(a.0.mul(c.0)).sub(a.1.mul(b.1).add(a.1.mul(c.1))),
        a.0.mul(b.0).sub(a.1.mul(b.1)).add(a.0.mul(c.0).sub(a.1.mul(c.1))),
    );
}

///  Imaginary part helper for distributivity.
proof fn lemma_complex_mul_dist_im<T: Ring>(a: (T, T), b: (T, T), c: (T, T))
    ensures
        complex_mul(a, complex_add(b, c)).1.eqv(
            complex_add(complex_mul(a, b), complex_mul(a, c)).1),
{
    //  LHS im = a.0*(b.1+c.1) + a.1*(b.0+c.0)
    //  RHS im = (a.0*b.1 + a.1*b.0) + (a.0*c.1 + a.1*c.0)

    //  Distribute: a.0*(b.1+c.1) ≡ a.0*b.1 + a.0*c.1
    T::axiom_mul_distributes_left(a.0, b.1, c.1);
    //  Distribute: a.1*(b.0+c.0) ≡ a.1*b.0 + a.1*c.0
    T::axiom_mul_distributes_left(a.1, b.0, c.0);

    //  Add congruence: LHS im ≡ (a.0*b.1 + a.0*c.1) + (a.1*b.0 + a.1*c.0)
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.0.mul(b.1.add(c.1)), a.0.mul(b.1).add(a.0.mul(c.1)),
        a.1.mul(b.0.add(c.0)), a.1.mul(b.0).add(a.1.mul(c.0)),
    );

    //  Rearrange: (p+q) + (r+s) ≡ (p+r) + (q+s)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        a.0.mul(b.1), a.0.mul(c.1), a.1.mul(b.0), a.1.mul(c.0),
    );

    //  Chain
    T::axiom_eqv_transitive(
        a.0.mul(b.1.add(c.1)).add(a.1.mul(b.0.add(c.0))),
        a.0.mul(b.1).add(a.0.mul(c.1)).add(a.1.mul(b.0).add(a.1.mul(c.0))),
        a.0.mul(b.1).add(a.1.mul(b.0)).add(a.0.mul(c.1).add(a.1.mul(c.0))),
    );
}

//  ── Lemma 7 (Main Theorem): SA Decomposition ──────────────────────

///  THE SA DECOMPOSITION THEOREM:
///  perturbation_orbit(c, dc, n) ≡ complex_mul(sa_coeff(c, n), dc) + sa_error(c, dc, n)
///
///  Since sa_error is defined as perturbation_orbit - sa_coeff*dc, this follows
///  from the algebraic identity x ≡ y + (x - y).
pub proof fn lemma_sa_decomposition<T: Ring>(
    c: (T, T), dc: (T, T), n: nat,
)
    ensures
        pair_eqv(
            perturbation_orbit(c, dc, n),
            complex_add(complex_mul(sa_coeff(c, n), dc), sa_error(c, dc, n)),
        ),
{
    let x_re = perturbation_orbit(c, dc, n).0;
    let x_im = perturbation_orbit(c, dc, n).1;
    let y_re = complex_mul(sa_coeff(c, n), dc).0;
    let y_im = complex_mul(sa_coeff(c, n), dc).1;

    //  Re: x_re ≡ y_re + (x_re - y_re)
    //  (x_re - y_re) + y_re ≡ x_re by sub_then_add_cancel
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(x_re, y_re);
    //  y_re + (x_re - y_re) ≡ (x_re - y_re) + y_re by commutativity
    T::axiom_add_commutative(y_re, x_re.sub(y_re));
    //  y_re + (x_re - y_re) ≡ x_re by transitivity
    T::axiom_eqv_transitive(
        y_re.add(x_re.sub(y_re)),
        x_re.sub(y_re).add(y_re),
        x_re,
    );
    //  x_re ≡ y_re + (x_re - y_re) by symmetry
    T::axiom_eqv_symmetric(y_re.add(x_re.sub(y_re)), x_re);

    //  Im: same pattern
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(x_im, y_im);
    T::axiom_add_commutative(y_im, x_im.sub(y_im));
    T::axiom_eqv_transitive(
        y_im.add(x_im.sub(y_im)),
        x_im.sub(y_im).add(y_im),
        x_im,
    );
    T::axiom_eqv_symmetric(y_im.add(x_im.sub(y_im)), x_im);
}

} //  verus!
