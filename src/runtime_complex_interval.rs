#[cfg(verus_keep_ghost)]
use crate::complex_interval::ComplexInterval;
#[cfg(verus_keep_ghost)]
use verus_interval_arithmetic::Interval;
#[cfg(verus_keep_ghost)]
use verus_rational::Rational;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

use verus_rational::RuntimeRational;
use verus_interval_arithmetic::RuntimeInterval;

#[cfg(not(verus_keep_ghost))]
compile_error!(
    "verus-mandelbrot exposes a single verified implementation; \
     build with Verus (`cfg(verus_keep_ghost)`, e.g. `cargo verus verify`)"
);

#[cfg(not(verus_keep_ghost))]
pub struct RuntimeComplexInterval;

#[cfg(verus_keep_ghost)]
verus! {

/// Runtime complex interval backed by RuntimeInterval components.
pub struct RuntimeComplexInterval {
    pub re: RuntimeInterval,
    pub im: RuntimeInterval,
    pub model: Ghost<ComplexInterval>,
}

impl RuntimeComplexInterval {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.re.wf_spec()
        &&& self.im.wf_spec()
        &&& self.re@ == self@.re
        &&& self.im@ == self@.im
        &&& self@.wf_spec()
    }

    /// Construct from a point (x, y).
    pub fn from_point(x: &RuntimeRational, y: &RuntimeRational) -> (out: Self)
        requires
            x.wf_spec(),
            y.wf_spec(),
        ensures
            out.wf_spec(),
            out@.re.lo == x@,
            out@.re.hi == x@,
            out@.im.lo == y@,
            out@.im.hi == y@,
    {
        let re = RuntimeInterval::from_point(x);
        let im = RuntimeInterval::from_point(y);
        let ghost model = ComplexInterval { re: re@, im: im@ };
        proof {
            ComplexInterval::lemma_from_point_wf(x@, y@);
        }
        RuntimeComplexInterval { re, im, model: Ghost(model) }
    }

    /// Complex addition.
    pub fn add(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out@ == self@.add_spec(rhs@),
            out.wf_spec(),
    {
        let re = self.re.add(&rhs.re);
        let im = self.im.add(&rhs.im);
        let ghost model = self@.add_spec(rhs@);
        proof { ComplexInterval::lemma_add_wf(self@, rhs@); }
        RuntimeComplexInterval { re, im, model: Ghost(model) }
    }

    /// Complex squaring: (a + bi)² = (a² - b²) + (2ab)i.
    pub fn square(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out@ == self@.square_spec(),
            out.wf_spec(),
    {
        let re2 = self.re.square();
        let im2 = self.im.square();
        let re_out = re2.sub(&im2);
        let re_im = self.re.mul(&self.im);
        let two = RuntimeRational::from_int(2);
        let im_out = RuntimeInterval::scale(&two, &re_im);
        let ghost model = self@.square_spec();
        proof { ComplexInterval::lemma_square_wf(self@); }
        RuntimeComplexInterval { re: re_out, im: im_out, model: Ghost(model) }
    }

    /// |z|² = re² + im².
    pub fn magnitude_squared(&self) -> (out: RuntimeInterval)
        requires
            self.wf_spec(),
        ensures
            out@ == self@.magnitude_squared_spec(),
            out.wf_spec(),
    {
        let re2 = self.re.square();
        let im2 = self.im.square();
        let out = re2.add(&im2);
        proof { ComplexInterval::lemma_magnitude_squared_wf(self@); }
        out
    }

    /// Reduce both components.
    pub fn reduce(&self, k: u32) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out@ == self@.reduce_spec(k as nat),
            out.wf_spec(),
    {
        let re = self.re.reduce(k);
        let im = self.im.reduce(k);
        let ghost model = self@.reduce_spec(k as nat);
        proof { ComplexInterval::lemma_reduce_wf(self@, k as nat); }
        RuntimeComplexInterval { re, im, model: Ghost(model) }
    }

    /// Normalize both components (GCD reduction).
    pub fn normalize(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@.re.lo.eqv_spec(self@.re.lo),
            out@.re.hi.eqv_spec(self@.re.hi),
            out@.im.lo.eqv_spec(self@.im.lo),
            out@.im.hi.eqv_spec(self@.im.hi),
    {
        let re = self.re.normalize();
        let im = self.im.normalize();
        let ghost model = ComplexInterval { re: re@, im: im@ };
        proof {
            // wf for reduced: re@.wf from normalize, im@ same
            // re@.lo eqv self@.re.lo, re@.hi eqv self@.re.hi (from normalize ensures)
            // so re@.wf follows from re.wf_spec() which normalize guarantees
        }
        RuntimeComplexInterval { re, im, model: Ghost(model) }
    }
}

impl View for RuntimeComplexInterval {
    type V = ComplexInterval;

    open spec fn view(&self) -> ComplexInterval {
        self.model@
    }
}

} // verus!
