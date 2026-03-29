use vstd::prelude::*;

use verus_rational::Rational;
use verus_interval_arithmetic::Interval;

verus! {

///  Ghost-level complex interval: a box [re_lo, re_hi] × [im_lo, im_hi] in the complex plane.
pub struct ComplexInterval {
    pub re: Interval,
    pub im: Interval,
}

impl ComplexInterval {
    ///  Well-formedness: both component intervals are well-formed.
    pub open spec fn wf_spec(self) -> bool {
        self.re.wf_spec() && self.im.wf_spec()
    }

    ///  Point containment: (x, y) is in the complex box.
    pub open spec fn contains_spec(self, x: Rational, y: Rational) -> bool {
        self.re.contains_spec(x) && self.im.contains_spec(y)
    }

    ///  Construct a point complex interval [(x,x), (y,y)].
    pub open spec fn from_point_spec(x: Rational, y: Rational) -> ComplexInterval {
        ComplexInterval {
            re: Interval::from_point_spec(x),
            im: Interval::from_point_spec(y),
        }
    }

    ///  Complex addition: component-wise.
    pub open spec fn add_spec(self, rhs: ComplexInterval) -> ComplexInterval {
        ComplexInterval {
            re: self.re.add_spec(rhs.re),
            im: self.im.add_spec(rhs.im),
        }
    }

    ///  Complex squaring: (a + bi)² = (a² - b²) + (2ab)i
    ///  re_out = re² - im², im_out = 2 * re * im
    pub open spec fn square_spec(self) -> ComplexInterval {
        let re2 = self.re.square_spec();
        let im2 = self.im.square_spec();
        let two_re_im = Interval::scale_spec(
            Rational::from_int_spec(2),
            self.re.mul_spec(self.im),
        );
        ComplexInterval {
            re: re2.sub_spec(im2),
            im: two_re_im,
        }
    }

    ///  |z|² = re² + im² as an interval.
    pub open spec fn magnitude_squared_spec(self) -> Interval {
        self.re.square_spec().add_spec(self.im.square_spec())
    }

    ///  Reduce both components to dyadic rationals with denominator 2^k.
    pub open spec fn reduce_spec(self, k: nat) -> ComplexInterval {
        ComplexInterval {
            re: self.re.reduce_spec(k),
            im: self.im.reduce_spec(k),
        }
    }

    //  ── Proofs ───────────────────────────────────────────────────

    ///  from_point is well-formed.
    pub proof fn lemma_from_point_wf(x: Rational, y: Rational)
        ensures
            Self::from_point_spec(x, y).wf_spec(),
    {
        Interval::lemma_from_point_wf(x);
        Interval::lemma_from_point_wf(y);
    }

    ///  from_point contains the point.
    pub proof fn lemma_from_point_contains(x: Rational, y: Rational)
        ensures
            Self::from_point_spec(x, y).contains_spec(x, y),
    {
        Interval::lemma_from_point_contains(x);
        Interval::lemma_from_point_contains(y);
    }

    ///  Addition preserves well-formedness.
    pub proof fn lemma_add_wf(a: Self, b: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            a.add_spec(b).wf_spec(),
    {
        Interval::lemma_add_wf(a.re, b.re);
        Interval::lemma_add_wf(a.im, b.im);
    }

    ///  Addition containment: if (x,y) in A and (u,v) in B, then (x+u, y+v) in A+B.
    pub proof fn lemma_add_containment(a: Self, b: Self, x: Rational, y: Rational, u: Rational, v: Rational)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.contains_spec(x, y),
            b.contains_spec(u, v),
        ensures
            a.add_spec(b).contains_spec(x.add_spec(u), y.add_spec(v)),
    {
        Interval::lemma_add_containment(a.re, b.re, x, u);
        Interval::lemma_add_containment(a.im, b.im, y, v);
    }

    ///  Squaring preserves well-formedness.
    pub proof fn lemma_square_wf(a: Self)
        requires
            a.wf_spec(),
        ensures
            a.square_spec().wf_spec(),
    {
        Interval::lemma_square_wf(a.re);
        Interval::lemma_square_wf(a.im);
        Interval::lemma_sub_wf(a.re.square_spec(), a.im.square_spec());
        Interval::lemma_mul_wf(a.re, a.im);
        Interval::lemma_scale_wf(Rational::from_int_spec(2), a.re.mul_spec(a.im));
    }

    ///  Squaring containment: (x,y) in A → (x²-y², 2xy) in square(A).
    pub proof fn lemma_square_containment(a: Self, x: Rational, y: Rational)
        requires
            a.wf_spec(),
            a.contains_spec(x, y),
        ensures
            a.square_spec().contains_spec(
                x.mul_spec(x).sub_spec(y.mul_spec(y)),
                Rational::from_int_spec(2).mul_spec(x.mul_spec(y)),
            ),
    {
        //  wf for squares
        Interval::lemma_square_wf(a.re);
        Interval::lemma_square_wf(a.im);
        //  x² in re.square()
        Interval::lemma_square_containment(a.re, x);
        //  y² in im.square()
        Interval::lemma_square_containment(a.im, y);
        //  x²-y² in re² - im²
        Interval::lemma_sub_containment(
            a.re.square_spec(), a.im.square_spec(),
            x.mul_spec(x), y.mul_spec(y));
        //  x*y in re*im
        Interval::lemma_mul_containment(a.re, a.im, x, y);
        //  2*x*y in scale(2, re*im)
        Interval::lemma_scale_containment(
            Rational::from_int_spec(2), a.re.mul_spec(a.im), x.mul_spec(y));
    }

    ///  Magnitude squared is well-formed.
    pub proof fn lemma_magnitude_squared_wf(a: Self)
        requires
            a.wf_spec(),
        ensures
            a.magnitude_squared_spec().wf_spec(),
    {
        Interval::lemma_square_wf(a.re);
        Interval::lemma_square_wf(a.im);
        Interval::lemma_add_wf(a.re.square_spec(), a.im.square_spec());
    }

    ///  Magnitude squared containment: (x,y) in A → x²+y² in |A|².
    pub proof fn lemma_magnitude_squared_containment(a: Self, x: Rational, y: Rational)
        requires
            a.wf_spec(),
            a.contains_spec(x, y),
        ensures
            a.magnitude_squared_spec().contains_spec(
                x.mul_spec(x).add_spec(y.mul_spec(y))),
    {
        Interval::lemma_square_wf(a.re);
        Interval::lemma_square_wf(a.im);
        Interval::lemma_square_containment(a.re, x);
        Interval::lemma_square_containment(a.im, y);
        Interval::lemma_add_containment(
            a.re.square_spec(), a.im.square_spec(),
            x.mul_spec(x), y.mul_spec(y));
    }

    ///  Reduce preserves well-formedness.
    pub proof fn lemma_reduce_wf(a: Self, k: nat)
        requires
            a.wf_spec(),
        ensures
            a.reduce_spec(k).wf_spec(),
    {
        a.re.lemma_reduce_wf(k);
        a.im.lemma_reduce_wf(k);
    }

    ///  Reduce preserves containment.
    pub proof fn lemma_reduce_containment(a: Self, k: nat, x: Rational, y: Rational)
        requires
            a.wf_spec(),
            a.contains_spec(x, y),
        ensures
            a.reduce_spec(k).contains_spec(x, y),
    {
        a.re.lemma_reduce_containment(k, x);
        a.im.lemma_reduce_containment(k, y);
    }
}

} //  verus!
