# Exec-to-Spec Chain: Implementation Guide

## Goal

Prove end-to-end: the GPU kernel's escape detection is correct within bounded truncation error. Concretely: if the kernel reports pixel (x,y) escaped at iteration N, then the true |Z+δ|² ≥ 4.0 - ε where ε ≈ 10⁻²⁶.

## Current State

We have all the PIECES but they're not CONNECTED:

```
Layer 1: Limb arithmetic     → 966 verified (verus-fixed-point)
Layer 2: Complex arithmetic   → 63 verified (gpu_mandelbrot_kernel.rs)  
Layer 3: Kernel buffer safety → 43 verified (gpu_perturbation_entry.rs)
```

**What's proved standalone:**
- `theorem_complex_square_error(re, im, S)`: trunc(re²/S) - trunc(im²/S) ∈ [exact, exact+1]
- `theorem_complex_mul_error(a_re, a_im, b_re, b_im, S)`: similar
- `theorem_perturbation_correctness(z, delta, c_ref, dc)`: Z'+δ' = (Z+δ)² + c_pixel (exact, abstract)
- `theorem_escape_with_tolerance(computed, true, threshold, error)`: escape detection sound

**What's NOT connected:**
- `complex_square` exec function has NO postcondition linking output to spec
- `perturbation_step` exec function has NO postcondition linking output to spec
- Kernel loop has NO ghost error accumulator
- Kernel escape check doesn't invoke the tolerance theorem

## Foundation Lemmas (DONE)

### `lemma_signed_val_squared` (runtime_fixed_point.rs)
```
x.signed_val() * x.signed_val() == x.unsigned_val() * x.unsigned_val()
```
**Why needed:** Truncation theorems work on unsigned vals. Spec uses signed vals. Squaring removes sign.

### `lemma_signed_self_mul_spec` (runtime_fixed_point.rs)
```
truncated_product_spec(uv, uv, frac, n) == (sv * sv / limb_power(frac)) % limb_power(n)
```
**Why needed:** Connects `signed_mul` output (truncated product of unsigned vals) to the spec formula using signed vals.

### `lemma_signed_add_exact` (runtime_fixed_point.rs)
```
|a.sv + b.sv| < P  →  signed_add(a,b).sv == a.sv + b.sv
```
**Why needed:** `signed_add` postcondition is a 3-way disjunction (exact, overflow, underflow). For bounded inputs, only the exact case applies.

### `lemma_signed_sub_exact` (runtime_fixed_point.rs)
```
|a.sv - b.sv| < P  →  signed_sub(a,b).sv == a.sv - b.sv
```
**Why needed:** Same as above for subtraction.

## Task #57: complex_square Postcondition

### What to prove
```rust
pub fn complex_square<T: LimbOps>(z: &FpComplex<T>) -> (out: FpComplex<T>)
    requires z.wf(), /* bounded input requires */
    ensures 
        out.wf(), out.same_format(z),
        // NEW: spec connection with error bound
        out.to_spec().re >= spec_complex_square(z.to_spec()).re / S,
        out.to_spec().re <= spec_complex_square(z.to_spec()).re / S + 1,
        out.to_spec().im >= spec_complex_square(z.to_spec()).im / S,
        out.to_spec().im <= spec_complex_square(z.to_spec()).im / S + 2,
```
where `S = limb_power(frac_limbs)`.

### Bounded input requires
The postcondition only holds when values are small enough that:
1. `signed_mul` products don't overflow 2n limbs (always true for practical values)
2. `truncated_product_spec % P == truncated_product_spec` (mod is no-op)
3. `signed_sub` doesn't wrap modularly

Concrete bound: `z.re.unsigned_val() < limb_power(n) / 2` and same for im. With n=4 limbs (128 bits) and values < 8 (escape radius), this is trivially satisfied: `8 * 2^96 << 2^127`.

### 10-Step Proof Chain

**Step 1:** `signed_mul` postcondition gives us:
```
re2.unsigned_val() == truncated_product_spec(z.re.uval, z.re.uval, frac, n)
re2.sign.sem() == 0  (same-sign multiplication)
```
Available from: `signed_mul` ensures clause.

**Step 2:** For bounded inputs, `truncated_product_spec(a, b, f, n) = (a*b / limb_power(f)) % limb_power(n)`. When `a*b / limb_power(f) < limb_power(n)`, the mod is a no-op:
```
re2.unsigned_val() == z.re.uval * z.re.uval / S
```
Need to prove: `z.re.uval² / S < limb_power(n)`. With `uval < P/2 = limb_power(n)/2`:
`uval² < P²/4`, `uval²/S < P²/(4S)`. With `S = limb_power(f)` and `f < n`:
`P²/(4S) = limb_power(2n-f)/4 > limb_power(n)` only if `2n-f > n+2` i.e. `n > f+2`.
So for `n=4, f=3`: `P²/(4S) = limb_power(5)/4 >> limb_power(4)`. Wait, that means the mod COULD fire.

Actually, we need the product to fit: `a*b < limb_power(2n)` (always true, proved by `lemma_signed_mul_magnitude`). The truncated product `a*b / S` could still be >= P = limb_power(n). The mod IS needed.

**Revised approach:** Don't try to eliminate the mod. Instead, work with `truncated_product_spec` directly. The key insight: `re2.signed_val() == re2.unsigned_val()` (since sign is 0). And `re2.unsigned_val() == truncated_product_spec(uval, uval, frac, n)`. This is what the exec computes.

The spec says: `spec_complex_square(z.to_spec()).re = z.re.sv² - z.im.sv²`.

The exec computes: `out.re.sv = trunc_prod_spec(re.uv, re.uv, f, n) - trunc_prod_spec(im.uv, im.uv, f, n)` (modular sub).

With `lemma_signed_val_squared`: `re.uv² == re.sv²`. So `trunc_prod_spec(re.uv, re.uv, f, n) = (re.sv²/S) % P`.

The exec `out.re.sv` = `(re.sv²/S) % P - (im.sv²/S) % P` (modular).

The spec `spec.re / S` = `(re.sv² - im.sv²) / S`.

The error: `|(re.sv²/S)%P - (im.sv²/S)%P - (re.sv² - im.sv²)/S|`

This is essentially `theorem_complex_square_error` but with the mod P. If values are bounded such that `(re.sv²/S)%P == re.sv²/S` (no mod wrapping), then the theorem applies directly.

**For practical values:** With `|re.sv| < 8*S` (escape radius 8 in fixed point) and `S = limb_power(f)`, `n = 4`:
- `re.sv² / S < 64 * S = 64 * limb_power(f)`
- `limb_power(n) = limb_power(4) = 2^128`
- `64 * limb_power(3) = 64 * 2^96 = 2^102 << 2^128`
- So `re.sv²/S < P`, mod is no-op. ✓

**Bounded input requires (concrete):**
```rust
requires
    z.re.unsigned_val() * z.re.unsigned_val() / limb_power(frac) < limb_power(n),
    z.im.unsigned_val() * z.im.unsigned_val() / limb_power(frac) < limb_power(n),
```

**Step 3:** `re2.sign == 0` → `re2.signed_val() == re2.unsigned_val()`.
Trivial from `signed_val` definition.

**Step 4:** Same for `im2`.

**Step 5:** `new_re = signed_sub(re2, im2)`. Both have sign 0.
`signed_sub` postcondition: `new_re.sv == re2.sv - im2.sv (mod P)`.
With bounded sub (|re2.sv - im2.sv| < P): `new_re.sv == re2.sv - im2.sv`.
Use `lemma_signed_sub_exact`.

**Step 6:** Chain: `new_re.sv == re2.uval - im2.uval == trunc(re.sv²/S) - trunc(im.sv²/S)`.

**Step 7:** `theorem_complex_square_error(re.sv, im.sv, S)` gives:
```
trunc(re²/S) - trunc(im²/S) ∈ [(re²-im²)/S, (re²-im²)/S + 1]
```
Wait — the theorem uses unsigned re, im (requires re ≥ 0, im ≥ 0). But `signed_val` can be negative.

**Key issue:** `theorem_complex_square_error` requires `re ≥ 0, im ≥ 0`. But `z.re.signed_val()` can be negative. Solution: use `unsigned_val` (always ≥ 0) with the theorem, then convert via `lemma_signed_val_squared`.

Since `re.uv² == re.sv²` and `im.uv² == im.sv²`:
- `trunc(re.uv²/S) - trunc(im.uv²/S) ∈ [(re.uv²-im.uv²)/S, (re.uv²-im.uv²)/S + 1]`
- `= [(re.sv²-im.sv²)/S, (re.sv²-im.sv²)/S + 1]`
- `= [spec.re/S, spec.re/S + 1]`

**Step 8-10:** `out.to_spec().re = new_re.sv = trunc(re.uv²/S) - trunc(im.uv²/S) ∈ [spec.re/S, spec.re/S+1]`. Done.

### Implementation approach

Add a proof block inside `complex_square` after computing `new_re`:

```rust
proof {
    // Step 1-2: re2.uval == re.uval²/S (bounded → mod is no-op)
    lemma_signed_val_squared(&z.re);
    let re_u = z.re.unsigned_val();
    let im_u = z.im.unsigned_val();
    let S = limb_power((z.re.frac_exec / 32) as nat);
    assert(re2.unsigned_val() == re_u * re_u / S);  // from signed_mul + bounded
    
    // Step 3-4: sign 0 → sv == uval
    assert(re2.signed_val() == re2.unsigned_val());
    assert(im2.signed_val() == im2.unsigned_val());
    
    // Step 5-6: exact subtraction for bounded inputs
    lemma_signed_sub_exact(&re2, &im2, &new_re);
    assert(new_re.signed_val() == re2.signed_val() - im2.signed_val());
    
    // Step 7: truncation error bound
    theorem_complex_square_error(re_u as int, im_u as int, S as int);
}
```

The tricky parts:
- Step 1-2 needs proving `re.uval²/S < P` (bounded input check)
- Step 5 needs `|re2.sv - im2.sv| < P` (for `lemma_signed_sub_exact`)
- Step 7 needs the values to be ≥ 0 (use unsigned_val)
- The `im` component follows the same pattern with `sum2 - re2 - im2` and error ≤ 2

## Task #58: complex_mul Postcondition

Same structure as #57 but for:
```
out.re.sv = trunc(a_re.uv * b_re.uv / S) - trunc(a_im.uv * b_im.uv / S)
out.im.sv = trunc((a_re.uv+a_im.uv)*(b_re.uv+b_im.uv)/S) - trunc(a_re*b_re/S) - trunc(a_im*b_im/S)
```
Uses `theorem_complex_mul_error` instead of `theorem_complex_square_error`.

Additional challenge: `complex_mul` has TWO input complexes, so the bounded input requires cover both.

## Task #59: perturbation_step Postcondition

Chains through:
1. `complex_double(z_ref)` — exact (signed_add, bounded)
2. `complex_mul(2*z, delta)` — error (1, 2) from #58
3. `complex_square(delta)` — error (1, 2) from #57
4. `complex_add(mul_result, sq_result)` — exact (bounded)
5. `complex_add(sum, delta_c)` — exact (bounded)

Total per-step error: (2, 4) ULPs (sum of mul + square errors).

**Bounded input requires:** `|z_ref|, |delta|, |delta_c| < escape_radius * S` where `S = limb_power(frac_limbs)`.

## Task #62: Kernel Loop Error Invariant

The perturbation while loop in `gpu_perturbation_entry.rs` needs ghost variables:

```rust
let ghost err_re: int = 0;
let ghost err_im: int = 0;

while iter < max_iters
    invariant
        // ... existing invariants ...
        // NEW: accumulated truncation error
        err_re <= (iter as int) * 2,
        err_im <= (iter as int) * 4,
{
    // ... perturbation step ...
    proof {
        // perturbation_step ensures error ≤ (2, 4)
        // err_re += 2; err_im += 4;
    }
}
```

**Challenge:** The kernel uses `_buf` functions (buffer-based), not `FpComplex<T>` wrappers. Need to either:
- (a) Interpret buffer regions as `FpComplex.to_spec()` values via a ghost spec function
- (b) Restate the error bounds directly in terms of buffer contents

Option (a) is cleaner: define `spec fn wg_mem_complex(mem: Seq<u32>, offset: int, n: int) -> SpecComplex` that reads re/im from shared memory at the given offset.

## Task #63: Escape Detection End-to-End

After the perturbation loop, with accumulated error (err_re, err_im):

```rust
// Escape check: sub_limbs_to(&t5, vslice(params, thresh_off), &mut t1, 0, n)
// borrow == 0 means |Z+δ|² ≥ threshold
proof {
    theorem_escape_with_tolerance(
        computed_mag,  // from the exec computation
        true_mag,      // ghost: exact value
        threshold,     // 4.0 in fixed point
        accumulated_error, // from loop invariant
    );
    // Conclusion: true |Z+δ|² ≥ threshold - ε ≈ 4.0
}
```

## Key Functions and Their Locations

| Function | File | Line | What it does |
|----------|------|------|-------------|
| `signed_mul` | runtime_fixed_point.rs | 197 | Truncated product with sign |
| `signed_add` | runtime_fixed_point.rs | 114 | Modular addition with sign |
| `truncated_product_spec` | runtime_fixed_point.rs | 45 | `(a*b / S) % P` |
| `signed_val` | runtime_fixed_point.rs | 56 | `if sign==0 { uval } else { -uval }` |
| `complex_square` | gpu_mandelbrot_kernel.rs | 52 | 3-multiply squaring |
| `complex_mul` | gpu_mandelbrot_kernel.rs | 98 | 3-multiply Karatsuba |
| `perturbation_step` | gpu_mandelbrot_kernel.rs | 148 | δ' = 2Zδ + δ² + Δc |
| `spec_complex_square` | gpu_mandelbrot_kernel.rs | 181 | re²-im², 2·re·im |
| `spec_pert_step` | gpu_mandelbrot_kernel.rs | 199 | Exact perturbation formula |
| `theorem_complex_square_error` | gpu_mandelbrot_kernel.rs | 521 | Error ≤ (1, 2) ULPs |
| `theorem_complex_mul_error` | gpu_mandelbrot_kernel.rs | 697 | Error ≤ (1, 2) ULPs |
| `theorem_escape_with_tolerance` | gpu_mandelbrot_kernel.rs | 891 | Escape sound with error |
| `lemma_signed_val_squared` | runtime_fixed_point.rs | 4617 | sv² == uv² |
| `lemma_signed_add_exact` | runtime_fixed_point.rs | 4641 | No wrapping for bounded |
| `lemma_signed_sub_exact` | runtime_fixed_point.rs | 4666 | No wrapping for bounded |

## Estimated Effort

| Task | Difficulty | Why |
|------|-----------|-----|
| #57 complex_square | Medium-High | 10-step proof chain, mod-P reasoning |
| #58 complex_mul | Medium-High | Same structure, two input complexes |
| #59 perturbation_step | High | Chains through #57 + #58 |
| #62 kernel loop invariant | High | Bridge buffer ops ↔ FpComplex specs |
| #63 escape end-to-end | Medium | Connecting existing theorems |

The hardest part is #62 (kernel loop invariant) because the kernel uses raw buffer operations (`signed_mul_to_buf` with offsets into `wg_mem`) while the spec functions use `FpComplex.to_spec()`. Bridging this gap requires defining ghost functions that interpret buffer regions as complex values.
