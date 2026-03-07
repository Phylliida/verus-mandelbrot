use vstd::prelude::*;

use verus_rational::Rational;
use verus_interval_arithmetic::Interval;
use crate::complex_interval::ComplexInterval;

verus! {

/// One Mandelbrot iteration: z_{n+1} = z_n² + c.
pub open spec fn mandelbrot_step_spec(z: ComplexInterval, c: ComplexInterval) -> ComplexInterval {
    z.square_spec().add_spec(c)
}

/// The escape threshold as an interval: [4, 4].
pub open spec fn escape_threshold_spec() -> Interval {
    Interval::from_point_spec(Rational::from_int_spec(4))
}

/// Certainly escaped: the entire |z|² interval is above 4.
pub open spec fn certainly_escaped_spec(z: ComplexInterval) -> bool {
    escape_threshold_spec().certainly_lt_spec(z.magnitude_squared_spec())
}

/// N iterations of z_{n+1} = z_n² + c starting from z0, reducing each step.
pub open spec fn mandelbrot_iterate_spec(z0: ComplexInterval, c: ComplexInterval, n: nat, k: nat) -> ComplexInterval
    decreases n,
{
    if n == 0 {
        z0
    } else {
        let z_prev = mandelbrot_iterate_spec(z0, c, (n - 1) as nat, k);
        mandelbrot_step_spec(z_prev, c).reduce_spec(k)
    }
}

// ── Proofs ───────────────────────────────────────────────────────

/// One Mandelbrot step preserves well-formedness.
pub proof fn lemma_step_wf(z: ComplexInterval, c: ComplexInterval)
    requires
        z.wf_spec(),
        c.wf_spec(),
    ensures
        mandelbrot_step_spec(z, c).wf_spec(),
{
    ComplexInterval::lemma_square_wf(z);
    ComplexInterval::lemma_add_wf(z.square_spec(), c);
}

/// One step preserves containment:
/// if (zx, zy) in z and (cx, cy) in c,
/// then (zx²-zy²+cx, 2·zx·zy+cy) in step(z, c).
pub proof fn lemma_step_containment(
    z: ComplexInterval, c: ComplexInterval,
    zx: Rational, zy: Rational,
    cx: Rational, cy: Rational,
)
    requires
        z.wf_spec(),
        c.wf_spec(),
        z.contains_spec(zx, zy),
        c.contains_spec(cx, cy),
    ensures
        mandelbrot_step_spec(z, c).contains_spec(
            zx.mul_spec(zx).sub_spec(zy.mul_spec(zy)).add_spec(cx),
            Rational::from_int_spec(2).mul_spec(zx.mul_spec(zy)).add_spec(cy),
        ),
{
    ComplexInterval::lemma_square_wf(z);
    ComplexInterval::lemma_square_containment(z, zx, zy);
    ComplexInterval::lemma_add_containment(
        z.square_spec(), c,
        zx.mul_spec(zx).sub_spec(zy.mul_spec(zy)),
        Rational::from_int_spec(2).mul_spec(zx.mul_spec(zy)),
        cx, cy,
    );
}

/// Escape soundness: if certainly_escaped(z), then for any (x,y) in z, x²+y² > 4.
pub proof fn lemma_escape_soundness(z: ComplexInterval, x: Rational, y: Rational)
    requires
        z.wf_spec(),
        z.contains_spec(x, y),
        certainly_escaped_spec(z),
    ensures
        Rational::from_int_spec(4).lt_spec(
            x.mul_spec(x).add_spec(y.mul_spec(y))),
{
    // certainly_escaped means: 4 < z.magnitude_squared().lo
    // magnitude_squared containment: x²+y² in z.magnitude_squared()
    // so x²+y² >= z.magnitude_squared().lo > 4
    ComplexInterval::lemma_magnitude_squared_containment(z, x, y);
    ComplexInterval::lemma_magnitude_squared_wf(z);
    let mag2 = z.magnitude_squared_spec();
    let val = x.mul_spec(x).add_spec(y.mul_spec(y));
    // val >= mag2.lo (from contains)
    // 4 < mag2.lo (from certainly_escaped)
    // => 4 < val (by transitivity)
    let four = Rational::from_int_spec(4);
    assert(four.lt_spec(mag2.lo));
    assert(mag2.contains_spec(val));
    assert(mag2.lo.le_spec(val));
    Rational::lemma_lt_le_transitive(four, mag2.lo, val);
}

} // verus!
