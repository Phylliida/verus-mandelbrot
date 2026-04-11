# Session 2026-04-10: Exec-to-Spec Chain Complete + Buffer Op Strengthening

## TL;DR

Completed the full exec-to-spec verification chain for the GPU Mandelbrot
kernel, end-to-end from `complex_square` through escape detection. Also added
four new kernel-level invariants and strengthened two foundational buffer
operations in `verus-fixed-point`.

**Total: 1160+ verified, 0 errors across the entire stack.**

## What We Did

### 1. Spec-Connection Postconditions for Complex Arithmetic (#57-#59)

Each function now has a conditional postcondition relating its exec output to
the mathematical spec, with bounded truncation error:

| Function           | re error      | im error      | Condition       |
|--------------------|---------------|---------------|-----------------|
| `complex_square`   | `[0, +1]`     | `[0, +2]`     | bounded inputs  |
| `complex_mul`      | `[-1, +2]`    | `[-2, +3]`    | bounded inputs  |
| `perturbation_step`| `[-1, +3]`    | `[-2, +5]`    | `pert_inputs_bounded` |

Errors are in ULPs (units in the last place of the fixed-point representation).

The signed Karatsuba multiplication was the key subtlety. We discovered that
the standard unsigned analysis (re ≤ 1, im ≤ 2) understates the error when
inputs can be negative — there's a sign-truncation offset because
`-(|x|/S) ≠ (-|x|)/S` when there's a non-zero remainder. The actual bounds
are wider but still negligible at 96 fractional bits.

### 2. End-to-End Escape Detection Soundness (#62-#63)

The chain now goes:
```
per-step error (3 re, 5 im)
  → N-step accumulation (3N re, 5N im)
  → magnitude error (≤10N ULPs)
  → escape check (true |Z+δ|² ≥ threshold - 10N ULPs)
```

For 200 iterations at 96 fractional bits: error ≤ 2000/2^96 ≈ 2.5×10⁻²⁶.
Escape detection is correct to ~25 decimal digits.

### 3. Kernel-Level Bug-Catching Invariants (#64-#67)

Four new properties verified inside the GPU kernel itself:

1. **Delta initial condition**: `δ₀ = (0, 0)` confirmed after the zeroing loop
   via `lemma_vec_val_zeros`.

2. **Magnitude signs**: Squaring in the escape check produces sign 0
   (`fr2_s == 0`, `fi2_s == 0`). Required strengthening `signed_mul_to` in
   verus-fixed-point to export the sign XOR property.

3. **Orbit slot correspondence**: The perturbation loop reads `Z_k` from
   offset `k*z_stride` — the same slot the reference orbit loop wrote `Z_k`
   to. Both use `orbit_base=0` and `z_stride=2n+2`. Catches off-by-one stride
   or iteration index bugs.

4. **Output pixel correspondence**: `iter_counts[gid_y*width + gid_x]` stores
   the result for pixel `(gid_x, gid_y)` using row-major linearization, and
   `c_data[tid*c_stride_px]` loads the matching complex coordinate.

### 4. Foundation Crate Strengthening (#68-#69)

Two buffer operations in `verus-fixed-point/src/fixed_point/limb_ops.rs` now
export their fundamental integer equations:

```rust
// add_limbs_to
limbs_val(out[off..off+n]) + carry * P == limbs_val(a[0..n]) + limbs_val(b[0..n])

// sub_limbs_to
limbs_val(out[off..off+n]) + limbs_val(b[0..n]) == limbs_val(a[0..n]) + borrow * P
```

These match the equations exported by `generic_add_limbs`/`generic_sub_limbs`
(which allocate fresh `Vec<T>`). The `_to` variants are GPU-friendly (no
allocation) but had weaker postconditions until now.

The proof technique: subrange-based loop invariant tracking
`limbs_val(sem_seq(out.subrange(off, off+i)))`, with a ghost `pre_sub` snapshot
before `out.set(...)` and extensional equality (`=~=`) to connect the pre/post
states.

### 5. Rlimit Regression Fix

Strengthening `add_limbs_to`/`sub_limbs_to` enlarged Z3's context, pushing
`lemma_perturbation_step_spec` over its rlimit. Fixed by:

1. Extracting Steps 3-4 (~60 assertions) into focused
   `lemma_pert_step_magnitude_bounds`.
2. Replacing `mul_3sum < P/4` in `nonlinear_arith` requires with the derived
   form `4*mul_3sum < P` (Z3 treats `/` as uninterpreted in nonlinear mode).
3. Proving `P > 24` from `limb_power(n) = LIMB_BASE * limb_power(n-1) ≥ 2^32`.

## Key Lessons Learned

### Verification is Deterministic

Verus failures are never "cache issues" — if a function fails, it will always
fail with the same inputs. Don't retry hoping for different results;
diagnose the actual cause. Saved this to memory as
`feedback_no_cache_issue.md`.

### Sign-Magnitude Truncation Offset

For sign-magnitude fixed-point, signed multiplication has wider error bounds
than unsigned because `-(|x|/S)` and `(-|x|)/S` differ by 1 ULP when there's
a remainder. The exec computes the former (truncate then negate), but the
spec uses the latter (negate then truncate, via floor division).

This affects the per-component error bounds:
- Unsigned analysis: re ≤ 1, im ≤ 2
- Signed analysis: re ∈ [-1, +2], im ∈ [-2, +3]

The wider bounds propagate through the perturbation step but are still
negligible at practical precision.

### Buffer Op Postconditions vs. Generic Variants

The `_to` variants (`add_limbs_to`, `sub_limbs_to`, `signed_mul_to`,
`signed_add_to`) were designed for GPU compatibility (no `Vec::new()`) but
had weaker postconditions than their `generic_*` counterparts. This created a
"buffer-to-FpComplex bridge gap": the kernel uses `_to` variants directly,
but the spec-connection proofs work on `FpComplex<T>` wrappers that internally
call `generic_*` functions with the full equations.

Strengthening the `_to` variants closes this gap. The pattern:
- Generic: works on `Vec<T>` of length `n`, equation about `sem_seq(result@)`
- `_to`: writes to `out[off..off+n]`, equation about
  `sem_seq(out@.subrange(off, off+n))`

The proof structure is identical, just with offset addressing and an extra
`extensional equality` (`=~=`) step to connect subranges across `out.set(...)`.

### Z3 and Integer Division

`by(nonlinear_arith)` treats integer `/` as an uninterpreted function. So
`mul_3sum < P/4` cannot be combined with arithmetic facts about `mul_3sum`
to derive `4*mul_3sum < P`. Fix: call `lemma_fundamental_div_mod(P, 4)` to
get `P == 4*(P/4) + P%4`, then derive `4*mul_3sum < P` directly.

### Extracting Heavy Proof Blocks

When a function gets too big for Z3 (rlimit exceeded), the rlimit tips
recommend extracting heavy assertion blocks into separate proof functions.
The extracted helper has its own focused Z3 context, dramatically reducing
verification cost. We did this twice this session:
- `lemma_complex_mul_spec_connection` (extracted from `complex_mul` proof)
- `lemma_pert_step_magnitude_bounds` (extracted from `lemma_perturbation_step_spec`)

## Bugs Found by Verification

Recap of bugs the verification process caught (some from previous sessions,
discovered while building this proof chain):

1. **`lprod` buffer half required size** — Karatsuba intermediate product
   needs `2n` limbs, buffer was only `n`.
2. **Border workgroup OOB** — edge workgroups could access pixels beyond
   the buffer.
3. **Reference orbit escape without glitch flag** — kept using garbage Z
   values without marking the pixel as glitched.
4. **`select_limb` arg order swapped** — `select_limb(cond, if_zero, if_nonzero)`
   was called with arguments backwards, silently producing wrong results.
5. **Sign-truncation offset** — original error estimates didn't account
   for the negate-vs-truncate ordering issue in signed Karatsuba.

Bug #4 is the scariest — it would produce silently wrong Mandelbrot images
with subtle visual artifacts indistinguishable from normal rendering glitches.

## Buffer-to-FpComplex Bridge Closed (#70 & #71)

After the initial summary, we completed the remaining two foundation
strengthenings, fully closing the buffer-to-FpComplex bridge.

### 6. `mul_schoolbook_to` Value Equation (prerequisite for #70)

Strengthened `mul_schoolbook_to` to export the value equation:

```rust
vec_val(out@.subrange(out_off, out_off + 2*n))
    == vec_val(a@.subrange(0, n)) * vec_val(b@.subrange(0, n))
```

The proof tracks three loop invariants through the nested schoolbook loops:

1. **Outer value invariant**: `vec_val(subrange) == a * limbs_val(sb[0..i])`
   — after `i` rows of `b` accumulated.
2. **Inner carry-augmented invariant**: tracks the partial row contribution
   plus the propagating carry: `V + carry*BASE^(i+j) == V_initial + limbs_val(sa[0..j]) * sb[i] * BASE^i`.
3. **Zero-tail invariant**: positions `[i+n, 2n)` still hold zero, ensuring
   the carry-set at position `i+n` overwrites a zero (so the value change is
   exactly `carry*BASE^(i+n)`).

The per-step proof had a subtle requirement: showing that the discarded
`_c2` carry from `prod_hi.add3(c1, 0)` is always zero. We derived this from
the joint sum bound: `a*b + out_old + carry < BASE²`, which implies
`new_carry < BASE` and forces `_c2 == 0`.

New helper: `lemma_vec_val_set_one` — updating one element of a `Seq<T>`
changes `vec_val` by `(new - old) * limb_power(idx)`.

### 7. `signed_mul_to` Truncated Product Equation (#70)

Built on the new `mul_schoolbook_to` postcondition + `slice_vec_to`'s frame
property. Added the postcondition:

```rust
vec_val(out@.subrange(out_off, out_off + n))
    == ((vec_val(a) * vec_val(b)) / limb_power(frac_limbs)) % limb_power(n)
```

New helper: `lemma_truncated_product_seq` — Seq-friendly version of the
existing `lemma_truncated_product` (which required `Vec<T>`). Same proof
structure (split at `frac_limbs`, split upper at `n`, derive the truncation
via `lemma_fundamental_div_mod` + `lemma_mod_multiples_vanish`).

Required adding the precondition `frac_limbs <= n` (necessary for the
truncation to fit within the lower half of the 2n product). All existing
callers satisfy this.

### 8. `signed_add_to` 3-Way Modular Sum Equation (#71)

Added the postcondition matching `signed_add` (the `GenericFixedPoint`
method): the signed-magnitude result equals `a + b`, possibly modulo
`P = limb_power(n)` if the true sum overflows the representable range.

```rust
let true_sum = signed_a + signed_b;
result_signed == true_sum
    || (result_signed == true_sum - P && true_sum >= P)
    || (result_signed == true_sum + P && true_sum <= -P)
```

New helpers:
- `signed_val_of(limbs, sign_v)` — sign-magnitude interpretation.
- `lemma_signed_add_correct_seq` — Seq-friendly mirror of
  `GenericFixedPoint::lemma_signed_add_correct`. Proves the 3-way disjunction
  by case-splitting on `same_sign × borrow_ab × per-sign signs` (8 leaves).

The proof for `signed_add_to` itself ghost-tracks `sum_sub`, `amb_sub`,
`bma_sub` subranges through the `add+sub+sub+select` pipeline. The final
loop's invariant carries:
- `forall j in [0, i): out[off+j].sem() == selected_seq[j].sem()`
- `forall j in [i, n): out[off+j].sem() == bma_sub[j].sem()` (untouched)

After the loop, applies `lemma_signed_add_correct_seq` to derive the postcondition.

The same-sign indicator proof required explicit case analysis on
`(a_sign, b_sign)` with modular arithmetic to derive
`(a_sign == b_sign) <==> same_sign == 1`.

### 9. Z3 Context Pollution Fix (split into `limb_ops_proofs.rs`)

Adding the new helper lemmas to `limb_ops.rs` pushed `mul2`'s verification
over its rlimit (32M+) due to context pollution. Per the rlimit tips, the
right fix is module separation: created `verus-fixed-point/src/fixed_point/limb_ops_proofs.rs`
and moved the four new helpers there:

- `lemma_vec_val_set_one`
- `lemma_truncated_product_seq`
- `signed_val_of`
- `lemma_signed_add_correct_seq`

This isolates them from `limb_ops.rs`'s Z3 context (where bodies of all
sibling functions get loaded), restoring `mul2`'s verification.

**Lesson**: When adding helper lemmas to a module that contains a function
near its rlimit ceiling, expect context pollution. Plan to put new helpers
in a `_proofs.rs` companion module from the start.

## Escape Branch Fully Verified (#72 & #73)

With #68–#71 in place, we connected the strengthened buffer ops directly
to the kernel's escape check.

### 10. Escape Check Polarity (#72)

Added a proof block right after `sub_limbs_to(t5, threshold, t1, ...)`:

```
borrow == 0  ⟺  vec_val(t5) ≥ vec_val(threshold)
```

The proof follows immediately from `sub_limbs_to`'s strengthened
postcondition (#69):
- `t1 + threshold == t5 + borrow * P`
- `0 ≤ vec_val(t1) < P` (from `valid_limbs`)
- `borrow ∈ {0, 1}`

Both directions of the polarity follow by case analysis on `borrow`.
Before this proof, the kernel's escape branch (`if borrow == 0u32`) was
an opaque check. Now it's a verified test that the magnitude is at
least the threshold at the limb-value level.

### 11. Magnitude Full Equation (#73)

Added a proof block in the escape check chaining the strengthened buffer
ops through the squaring + summing:

```
vec_val(t5) + mag_carry * P
    == trunc_sq(vec_val(t1)) + trunc_sq(vec_val(t2))
```

where `trunc_sq(x) = (x*x / BASE^frac) % BASE^n`, and `t1`, `t2` are the
magnitudes of `(Z_re + δ_re)` and `(Z_im + δ_im)` produced by `signed_add_to`.

The proof chains:
- **#70** (`signed_mul_to`): `vec_val(t3) == trunc_sq(vec_val(t1))`,
  similarly for `t4`
- **#68** (`add_limbs_to`): `vec_val(t5) + carry*P == vec_val(t3) + vec_val(t4)`

To enable this, the previously-discarded `add_limbs_to` carry is now bound
to a local variable `mag_carry`.

### Combined Effect

The kernel's escape branch is now fully verified at the buffer-value level:

1. Squaring uses verified truncated multiplication (#70)
2. Summing uses the verified add equation (#68)
3. Threshold comparison uses the verified subtract equation (#69) + the
   polarity proof (#72)
4. The complete chain (#73) connects squared magnitudes to the final
   compared value

The remaining gap — connecting `vec_val(t1)` back to the original
`(Z_re + δ_re)` signed inputs — is closed by #74 below.

## Kernel Robustness (#74, #75, #76)

After the escape branch was verified, we added three follow-up proofs
that extend the kernel's verification to fully connect the math, the
truncation error budget, and the glitch detection logic.

### 12. Magnitudes Connected to Signed Inputs (#74)

Extends #73 with the chain through `signed_val_of` and the #71 disjunction.

The chain (now exposed at the assertion level):
- **#71** disjunction (explicit): `signed_full_re == signed_zre + signed_dre`
  (or ±P offset on overflow)
- `(-x)² == x²` (nonlinear_arith): `signed_full_re² == vec_val(t1)²`
- **#70**: `vec_val(t3) == trunc_sq(vec_val(t1))`
- **#68**: `vec_val(t5) + carry*P == vec_val(t3) + vec_val(t4)`

End state: the kernel's escape decision is verified end-to-end at the
buffer-value level — from the original `Z_re`, `δ_re`, `Z_im`, `δ_im`
inputs through the squaring + summing all the way to the borrow that
decides escape (combined with #72's polarity proof).

Imports `signed_val_of` from `limb_ops_proofs` (gated on `verus_keep_ghost`).

### 13. Reference Orbit Error Accumulation (#75)

Adds the linearized N-step error bound for the reference orbit
`Z_{n+1} = Z_n² + c`, characterizing the geometric error growth.

New definitions in `gpu_mandelbrot_kernel.rs`:

```rust
// Recursive bound: bound(0) = 0, bound(k+1) = m * bound(k) + epsilon
pub open spec fn ref_orbit_error_bound(n: nat, m: int, epsilon: int) -> int

proof fn lemma_ref_orbit_error_bound_nonneg(...)
proof fn lemma_ref_orbit_error_bound_monotone(...)

// Connects any sequence satisfying the linear recurrence to the spec fn
proof fn theorem_ref_orbit_n_steps_error(
    bounds: Seq<int>, n: nat, m: int, epsilon: int,
) ...

// Concrete values for Mandelbrot (m=4 from R=2, ε=2 from complex_square)
proof fn corollary_mandelbrot_ref_orbit_bound() ...
```

The closed-form is `bound(N) = epsilon * (m^N - 1) / (m - 1)`. For
Mandelbrot (m=4, ε=2): the bound exceeds 1.0 already at N≈45 — beyond
that, the kernel relies on glitch detection rather than asymptotic
accuracy of the reference orbit.

Together with `theorem_ref_orbit_step_error` (per-step bound), this
documents the complete error budget for the reference orbit:
- per-step: ≤ 2 ULPs (re), ≤ 2 ULPs (im) [from `complex_square`]
- N-step: `ref_orbit_error_bound(N, 4, 2)`

### 14. Glitch Detection Completeness (#76)

Adds `lemma_glitch_completeness_one` proving the converse direction
of the kernel's glitch check:

```
vec_val(δ) >= 4 * BASE^(n-1)  ⟹  δ[n-1] > 3
```

Combined with the existing forward direction (the if-statement sets
`is_glitched` when the check fires), this gives bidirectional
correctness:

- forward: `δ[n-1] > 3` → `is_glitched = 1` (kernel structure)
- completeness: `vec_val(δ) >= 4 * BASE^(n-1)` → check fires (this proof)

So all "value too large" δ values are caught by the glitch detection.

The proof splits `vec_val(δ)` at index `n-1` using `lemma_vec_val_split`,
shows that the lower part is bounded by `BASE^(n-1)`, then uses
`nonlinear_arith` to derive the bound on the top limb.

Per the rlimit tips, the proof was extracted to a helper lemma to avoid
pushing the perturbation while loop's Z3 context over its rlimit. The
kernel call site only invokes the helper.

## Buffer-to-buf Closure & Glitch Refinement (#77, #80)

After completing the kernel robustness work (#74-#76), we attempted to
close the remaining gap between the verified buffer operations and the
kernel's actual perturbation theory implementation. Wrote a roadmap doc
(`exec-verification-roadmap.md`) characterizing four follow-up tasks:
- Task 1 (#77): Strengthen `*_to_buf` variants
- Task 2 (#78): Add value invariants to perturbation while loop
- Task 3 (#79): Bridge to `theorem_perturbation_n_steps`
- Task 4 (#80): Refine glitch detection criterion

### 15. Strengthen `*_to_buf` Variants (#77)

Adds value-equation postconditions to the three single-buffer signed
operations (`signed_add_to_buf`, `signed_sub_to_buf`, `signed_mul_to_buf`).
Mirrors the work for `signed_add_to`/`signed_mul_to` but adapted for the
single-buffer + offsets pattern with explicit non-overlap preconditions.

The proofs reuse the helpers in `limb_ops_proofs.rs`
(`lemma_signed_add_correct_seq`, `lemma_truncated_product_seq`).

**rlimit consequence**: After #77, the kernel function `mandelbrot_perturbation`
exceeded its default rlimit because the strengthened postconditions added
facts to Z3's context for every call inside the reference orbit and
perturbation while loops. Bumped to `rlimit(100)` as a stopgap. The proper
fix is loop body extraction (Task #81 below).

### 16. Refined Glitch Criterion (#80)

Defines `is_perturbation_glitch` — the math criterion for when the
perturbation linearization breaks down:

> **Glitch** ⟺ `max(|δ_re|, |δ_im|) ≥ 2 * z_max`

At this threshold, the `δ²` correction term equals the `2Zδ` linear
term, so the `(Z+δ)² ≈ Z² + 2Zδ` linearization has completely broken down.

`theorem_glitch_check_sound` proves that when the kernel's coarse
buffer-level check fires (`vec_val(δ) >= 4*S` with `frac_limbs == n-1`),
the math glitch criterion holds. The kernel marks pixels as glitched
when the linearization actually broke — no false positives.

Combined with #76 (limb-level completeness), the kernel's check is
sound w.r.t. **both**:
- the limb-level threshold (via #76)
- the math criterion (via #80)

### 17. Task 2 (#78) Discovery: Loop Body Extraction Prerequisite

Attempted to add ghost value tracking (`delta_re_int`, `delta_im_int`) to
the perturbation while loop. **Result**: even with `rlimit(200)`, the
loop's Z3 context exceeded its budget when adding two simple invariants.

**Conclusion**: Task #78 cannot be done in-place. The perturbation
iteration body (~30 buffer ops, ~150 lines) must first be extracted into
a focused helper function `perturbation_iteration_step`. The helper has
its own clean Z3 context and could carry the ghost invariants without
polluting the kernel function.

This created Task #81 as a new prerequisite. Documented in
`exec-verification-roadmap.md` and `loop-extraction-plan.md`.

## What Remains

### Active Tasks

- **#81**: Extract perturbation iteration body to helper function (NEW prerequisite for #78)
- **#78**: Add value invariants to perturbation while loop (depends on #81)
- **#79**: Bridge per-iteration ghost values to `theorem_perturbation_n_steps` (depends on #78)

### Other Future Work

Possible additional verification targets:
- **Series approximation kernel** — additional optimization not yet verified
- **Tighten reference orbit error bound** — currently the bound assumes
  worst-case amplification at every step. A bound that uses the actual
  `|Z_k|` at each step would be much tighter.
- **WGSL transpilation correctness** — `wgsl_emit.rs` has some proofs but
  the bridge from Rust IR to WGSL semantics involves trust.

### TODO: Workgroup Barrier Semantics

The `gpu_workgroup_barrier()` is currently trusted as `#[verifier::external_body]`.
Modeling it properly would require a GPU memory model that captures:
- Memory ordering across threads in a workgroup
- The "happens-before" relationship that the barrier establishes
- Visibility of writes from one thread to others after the barrier

This is a foundational gap — every kernel that uses workgroup memory currently
relies on this assumption. Filling it would unlock end-to-end verification of
the workgroup-shared parts of the perturbation kernel (vote tabulation, best
reference selection, shared-memory orbit reads).

Worth doing because:
1. It removes one of the few `external_body` dependencies in the verified path
2. It would catch potential race-condition bugs that are currently invisible
3. The same model would benefit any future GPU kernel work in this codebase

Effort estimate: high (requires designing/adopting a memory model and
re-proving the kernel's barrier-dependent invariants).

## Files Changed

- `verus-fixed-point/src/fixed_point/limb_ops.rs` — strengthened
  `add_limbs_to`, `sub_limbs_to`, `mul_schoolbook_to`, `signed_mul_to`,
  `signed_add_to`
- `verus-fixed-point/src/fixed_point/limb_ops_proofs.rs` — **new** companion
  module containing helper lemmas (`lemma_vec_val_set_one`,
  `lemma_truncated_product_seq`, `signed_val_of`, `lemma_signed_add_correct_seq`)
- `verus-fixed-point/src/fixed_point/mod.rs` — register the new module
- `verus-mandelbrot/src/gpu_mandelbrot_kernel.rs` — spec connection proofs
  for `complex_square`, `complex_mul`, `perturbation_step`; end-to-end escape
  theorems; helper lemmas; rlimit fix; reference orbit error accumulation (#75)
- `verus-mandelbrot/src/gpu_perturbation_entry.rs` — kernel invariants
  (delta init, magnitude signs, orbit slots, pixel correspondence);
  escape check polarity (#72); magnitude full equation (#73);
  signed-input chain (#74); glitch detection completeness helper (#76)

## Verification Counts

| Module                                        | Verified | Errors |
|-----------------------------------------------|----------|--------|
| `verus-fixed-point/src/fixed_point/limb_ops`  | 203      | 0      |
| `verus-fixed-point/src/fixed_point/limb_ops_proofs` | 15  | 0      |
| `verus-mandelbrot/src/gpu_mandelbrot_kernel`  | 165      | 0      |
| `verus-mandelbrot/src/gpu_perturbation_entry` | 49       | 0      |
| **Total (this session)**                      | **432**  | **0**  |

Plus ~800 verified across other modules in `verus-fixed-point` (all unchanged
and still passing).

## Commits

- `9c3616a` — Fix iszero_im completely (pre-session)
- `1b10dc9` — Strengthen mul_schoolbook_to with value equation postcondition
- `043eae2` — Strengthen signed_mul_to with truncated product value equation (#70)
- `a50c660` — Strengthen signed_add_to with 3-way modular sum equation (#71)
- `5519340` — Add session 2026-04-10 summary
- `69ba144` — Prove escape check polarity (#72)
- `ab6e026` — Prove magnitude full equation (#73)
- `3aa7698` — Update session summary with #72 and #73
- `3089bba` — Add workgroup barrier semantics TODO
- `cfc2b6e` — Connect magnitudes back to signed inputs (#74)
- `1135093` — Reference orbit error accumulation (#75)
- `af27fbc` — Glitch detection completeness (#76)
- `9ca7a0e` — Update session summary with kernel robustness work
- `d65eff6` — Add exec verification roadmap doc
- `995f447` — Strengthen *_to_buf variants with value equations (#77)
- `26eb016` — Bump rlimit on mandelbrot_perturbation
- `13a011f` — Document Task #78 prerequisite: loop body extraction needed
- `c43e707` — Refine glitch detection criterion (#80)
- `73580ea` — Update roadmap: Task 2 needs loop body extraction first
