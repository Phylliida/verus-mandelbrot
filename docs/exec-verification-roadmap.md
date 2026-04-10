# Exec Verification Roadmap: Closing the Buffer-to-Math Gap

**Status**: 2026-04-10 — written after completing #68–#76 (buffer ops, escape branch, kernel robustness)

**Audience**: Future-you (or future Claude) picking up the GPU Mandelbrot
verification work after the current session's foundation work.

---

## TL;DR

We have **strong foundations** but a **substantial gap** between the verified
buffer operations and the kernel's perturbation theory implementation. This
doc characterizes the gap, explains what we learned getting here, and lays out
four concrete tasks (Tasks 1–4) that would close it.

---

## Honest Assessment of the Current State

### What's verified

1. **Individual buffer ops** (`*_to` variants): `add_limbs_to`, `sub_limbs_to`,
   `signed_mul_to`, `signed_add_to`, `mul_schoolbook_to` all have value
   equations as postconditions. Each call computes the correct value.

2. **Per-iteration escape check at the buffer level**: For *one iteration*,
   `vec_val(t5) + carry*P == trunc_sq(t1) + trunc_sq(t2)` and the borrow
   polarity (`borrow == 0 ⟺ vec_val(t5) ≥ vec_val(threshold)`).

3. **Signed-input chain at the escape check**: The 3-way disjunction from
   `signed_add_to` is exposed at the assertion level, connecting the
   magnitudes back to `(Z_re + δ_re)` and `(Z_im + δ_im)`.

4. **Standalone math theorems** (in `gpu_mandelbrot_kernel.rs`):
   - `theorem_complex_square_error`, `theorem_complex_mul_error`
   - `theorem_perturbation_correctness`, `theorem_perturbation_n_steps`
   - `theorem_ref_orbit_step_error`, `ref_orbit_error_bound`,
     `theorem_ref_orbit_n_steps_error`
   - `theorem_glitch_detection_soundness`, `theorem_escape_end_to_end`
   - These prove how perturbation theory and the reference orbit *should*
     behave mathematically.

5. **Glitch completeness w.r.t. the simplified threshold**: If
   `vec_val(δ) >= 4 * BASE^(n-1)`, the kernel's `δ[n-1] > 3` check fires.

6. **Various kernel structural invariants**: delta init at zero, magnitude
   signs, orbit-slot correspondence, output pixel correspondence,
   non-overlap of buffer regions, etc.

### What is NOT verified (the gap)

#### Gap A: The kernel's perturbation loop body is opaque to verification

The kernel computes `δ' = 2*Z*δ + δ² + Δc` via a sequence of `signed_mul_to`,
`signed_add_to`, `signed_sub_to` calls. We've verified each call individually,
but **there's no proof that the composition equals one perturbation step**.

The math theorems (`perturbation_step`, `theorem_perturbation_correctness`)
operate on `FpComplex<T>` values. The kernel uses raw `Vec<u32>` buffers
with offsets. **They are two parallel tracks that don't connect.**

#### Gap B: No loop invariant carries values across iterations

The perturbation `while iter < max_iters` loop has invariants about lengths,
`valid_limbs`, signs, and shared-memory bounds — but **nothing about the
values**. So after iteration k, we cannot conclude "`delta_re` represents
δ_k of the mathematical orbit". The per-iteration value proofs we added
(#73, #74) hold *only at that one iteration*; the next iteration loses them.

#### Gap C: The reference orbit is unverified at the value level

The reference orbit uses `signed_mul_to_buf`, `signed_add_to_buf`,
`signed_sub_to_buf` — the **buf** variants. These still have weak
postconditions (only `valid_limbs` + frame). The entire reference orbit
computation is opaque to value-level reasoning. `theorem_ref_orbit_n_steps_error`
exists but doesn't apply to the actual code.

#### Gap D: Glitch completeness is "w.r.t. the kernel's coarse threshold"

The proof we have:
> `vec_val(δ) >= 4 * BASE^(n-1) → check fires`

This is "completeness given the unsigned magnitude is large". The classical
perturbation glitch criterion is more subtle — it's about **relative
precision loss as `|δ|/|Z|` grows**. The kernel uses a coarse approximation
(`top limb > 3`), and we've only proved that approximation's completeness,
not that it catches all *real* glitches.

#### Gap E: WGSL transpilation is trusted

`wgsl_emit.rs` has *some* proofs, but the bridge from the Rust IR to the
actual semantics of the emitted WGSL involves trust. Even with everything
in Rust verified, the running GPU shader could in principle differ.

#### Gap F: `gpu_workgroup_barrier()` is `external_body`

Modeling the workgroup memory barrier requires a GPU memory model. Tracked
as a separate TODO in `session-2026-04-10-summary.md`.

---

## What Got Built This Session (For Context)

### Completed: #68–#76

| # | What | Where |
|---|------|-------|
| #68 | `add_limbs_to` value equation | `limb_ops.rs` |
| #69 | `sub_limbs_to` value equation | `limb_ops.rs` |
| #70 | `signed_mul_to` truncated product equation + `mul_schoolbook_to` value equation | `limb_ops.rs` |
| #71 | `signed_add_to` 3-way modular sum equation | `limb_ops.rs` |
| #72 | Escape check polarity (`borrow == 0 ⟺ vec_val(t5) ≥ threshold`) | `gpu_perturbation_entry.rs` |
| #73 | Magnitude full equation (`vec_val(t5) == trunc_sq(t1) + trunc_sq(t2)`) | `gpu_perturbation_entry.rs` |
| #74 | Signed-input chain via `signed_val_of` and #71 disjunction | `gpu_perturbation_entry.rs` |
| #75 | Reference orbit error accumulation (standalone) | `gpu_mandelbrot_kernel.rs` |
| #76 | Glitch detection completeness (limb-level) | `gpu_perturbation_entry.rs` |

### Companion module created

`verus-fixed-point/src/fixed_point/limb_ops_proofs.rs` — companion module
holding helper lemmas extracted to avoid Z3 context pollution in `limb_ops.rs`
(specifically, `mul2`'s heavy nonlinear_arith proof).

Helpers in this module:
- `lemma_vec_val_set_one`: in-place updates to a Seq change vec_val by
  `(new - old) * BASE^idx`
- `lemma_truncated_product_seq`: Seq-friendly version of
  `lemma_truncated_product`
- `signed_val_of`: sign-magnitude interpretation
- `lemma_signed_add_correct_seq`: Seq-friendly correctness for
  signed addition with the 3-way modular disjunction

---

## Key Lessons Learned

### 1. Verification is deterministic — failures are never cache issues

Z3 does the same work given the same inputs. If a function fails after a
change, the change increased the work somehow. Don't retry hoping for
different results; diagnose. (Saved as `feedback_no_cache_issue.md` in
auto-memory.)

### 2. Helper lemmas pollute their containing module's Z3 context

Adding even pure proof-mode lemmas to a module loads their bodies/ensures
into Z3's context for *every* function in that module. If a sibling function
is near its rlimit ceiling (like `mul2` in `limb_ops.rs` at 32M+), new
helpers will push it over.

**Fix**: put helper lemmas in a `_proofs.rs` companion module from the start.
We hit this with `#71` and had to refactor; `limb_ops_proofs.rs` is the result.

### 3. `assert by(nonlinear_arith) requires X` — X must be locally provable

When the precondition `X` references ghost let-bindings, Z3 inside the
nonlinear context may not see the binding's expansion. Use intermediate
local variables (e.g., `let aj_v: int = aj; assert(aj_v == aj);`) before
the by-block to give Z3 a clean variable name.

### 4. `_to` and `_to_buf` have different non-overlap structures

`_to` variants take separate `&mut Vec` arguments — non-overlap is implicit
because they're distinct. `_to_buf` variants take ONE `&mut Vec` with
multiple offsets, requiring explicit non-overlap preconditions. When
strengthening `_to_buf`, the value-equation proof has to manage these.

### 5. Strengthening foundation ops can break callers via context bloat

After #70, `lemma_perturbation_step_spec` (200+ lines, 60+ assertions)
exceeded its rlimit because the new `signed_mul_to` postcondition added
facts to Z3's context. **Fix**: extract heavy proof blocks into focused
helper lemmas so each gets its own clean context.

### 6. Sign-magnitude truncation has wider error bounds than unsigned

For signed Karatsuba, the per-component error bounds are wider than the
naive unsigned analysis suggests:
- Unsigned: `re ≤ 1, im ≤ 2` ULPs
- Signed: `re ∈ [-1, +2], im ∈ [-2, +3]` ULPs

The reason: `-(|x|/S) ≠ (-|x|)/S` when there's a non-zero remainder. The
exec computes the former (truncate then negate), the spec uses the latter
(negate then truncate via floor division).

### 7. Loop invariants strip ghost let-bindings

Ghost variables defined in the loop body are not available to subsequent
iterations. Anything you want to carry across iterations *must* be in the
loop invariant.

### 8. The kernel is not the FpComplex code — they're parallel tracks

The biggest insight: `gpu_mandelbrot_kernel.rs` defines `complex_square`,
`complex_mul`, `perturbation_step`, etc., as functions on `FpComplex<T>`.
These are wrappers around the Vec ops with all the proof scaffolding.

But the **GPU kernel doesn't use them**. It calls the buffer ops directly
(`signed_mul_to`, `signed_add_to`, etc.) with raw `&[u32]` slices and
offsets. So the FpComplex-level theorems are mathematical models that
need to be *connected* to the kernel computation, not automatic.

This is the core gap that Tasks 2 and 3 address.

---

## Files To Know

| File | Role |
|------|------|
| `verus-fixed-point/src/fixed_point/limb_ops.rs` | Buffer ops (add/sub/mul, signed variants, *_to, *_to_buf) |
| `verus-fixed-point/src/fixed_point/limb_ops_proofs.rs` | Helper lemmas for value equations |
| `verus-fixed-point/src/runtime_fixed_point.rs` | `GenericFixedPoint<T>` (signed_add, signed_mul, etc. — Vec-allocating) |
| `verus-mandelbrot/src/gpu_mandelbrot_kernel.rs` | FpComplex-level math: complex_square, complex_mul, perturbation_step + theorems |
| `verus-mandelbrot/src/gpu_perturbation_entry.rs` | The actual GPU kernel — buffer ops + while loops + glitch detection |
| `verus-mandelbrot/docs/exec-to-spec-chain-guide.md` | How spec connection postconditions work |
| `verus-mandelbrot/docs/session-2026-04-10-summary.md` | This session's full chronological summary |

---

## Tasks 1–4: Detailed Plans

### Task 1: Strengthen `*_to_buf` variants with value equations

**Status**: Pending (`#77`)
**Effort**: Moderate (mostly mechanical adaptation of `*_to` proofs)
**Unblocks**: Task 2 (for the reference orbit verification)

**Functions to strengthen**:
- `add_limbs_to_buf`
- `sub_limbs_to_buf`
- `mul_schoolbook_to_buf`
- `signed_mul_to_buf`
- `signed_add_to_buf`
- `signed_sub_to_buf` (if it exists separately)

**What's different from `*_to`**: The `_to_buf` variants take a single
`&mut Vec<T> buf` and use multiple offsets. They need explicit non-overlap
preconditions. The value equation proof has to:
1. Track the input subranges by offset (not by separate `&[T]` arguments)
2. Use the non-overlap precondition to prove that writes to `out_off` don't
   modify the input regions

**Proof approach** (mostly mechanical):
1. Look at the corresponding `*_to` function's value-equation proof
2. Replace `a@`/`b@` with `buf@.subrange(a_off, a_off + n)` etc.
3. Add ghost capture of input subranges *before* the body modifies the buffer
4. Use the non-overlap precondition to prove the captured subranges are
   unchanged after writes

**Background needed**:
- Read `add_limbs_to`, `sub_limbs_to`, `signed_mul_to`, `signed_add_to`
  in `limb_ops.rs` for the proof patterns.
- The helper lemmas in `limb_ops_proofs.rs` should be reused as-is.
- Read `mul_schoolbook_to` for the more complex inner-loop value invariant
  pattern.

**Pitfalls**:
- Z3 context pollution: if any helpers are needed, put them in
  `limb_ops_proofs.rs`, not `limb_ops.rs`.
- The `mul_schoolbook_to_buf` proof will be the longest (matches the
  complexity of `mul_schoolbook_to`).
- Verify each function in isolation before adding the next; rlimit
  regressions are easier to localize.

**Definition of done**: All `*_to_buf` variants export value equations
analogous to their `*_to` counterparts. Build still passes for
`verus-fixed-point` and `verus-mandelbrot`.

---

### Task 2: Add value invariants to perturbation while loop

**Status**: Pending (`#78`)
**Effort**: HIGH (the largest task — many buffers, many ops, non-trivial chain)
**Unblocks**: Task 3
**Depends on**: Task 1 (only for the reference orbit; the perturbation loop
itself uses `*_to` which is already strengthened)

**What it is**:

The kernel has a `while iter < max_iters` loop that repeatedly computes
`δ_{k+1} = 2*Z_k*δ_k + δ_k² + Δc`. Each iteration body is ~30 buffer op
calls (signed_mul_to, signed_add_to, signed_sub_to). We need a loop
invariant tracking ghost values that connect the buffer state to the
mathematical orbit.

**Approach**:

Define ghost `SpecComplex` values for:
- `z_k_spec`: the reference orbit Z_k at iteration k
- `delta_k_spec`: the perturbation δ_k at iteration k
- `dc_spec`: the constant Δc (doesn't change across iterations)

Loop invariant should include:
- `delta_re@.subrange(0, n).vec_val()` matches `|delta_k_spec.re|`
  via the sign-magnitude relationship (using `delta_re_sign`)
- Similarly for `delta_im`
- The ghost values satisfy `delta_k_spec == spec_pert_step(z_{k-1}, delta_{k-1}, dc)`
  for all completed iterations
- `z_k_spec` satisfies `z_k == spec_ref_step(z_{k-1}, c_ref)`

Inside each iteration body:
- Each buffer op call already gives a value postcondition (after Task 1
  for the *_to_buf variants in the reference orbit, or directly for *_to
  in the perturbation loop)
- Chain them through the iteration, showing the post-iteration `delta_re`/
  `delta_im` buffers represent `spec_pert_step(z_k, delta_k, dc)`.

**Background needed**:
- `gpu_mandelbrot_kernel.rs` definitions:
  - `SpecComplex` struct
  - `spec_complex_add`, `spec_complex_mul`, `spec_complex_square`
  - `spec_ref_step`, `spec_pert_step`, `spec_full_orbit`
  - `perturbation_step_correct` predicate
- `gpu_perturbation_entry.rs` perturbation loop body (~lines 800–900)
  to understand the exact sequence of ops
- The signed-input chain in the escape check (#74) — same pattern, just
  for one iteration instead of all of them

**Detailed sub-steps**:

1. **Define a wf predicate** for the kernel state at each iteration:
   ```rust
   spec fn delta_buffers_match_spec(
       delta_re: Seq<u32>, dre_sign: u32,
       delta_im: Seq<u32>, dim_sign: u32,
       delta_spec: SpecComplex,
       n: nat, frac_limbs: nat,
   ) -> bool { ... }
   ```
   This says: the buffer values represent `delta_spec` modulo the
   sign-magnitude encoding and the truncation by `frac_limbs`.

2. **Add ghost variables** at the start of the perturbation loop:
   - `let ghost mut delta_spec: SpecComplex = SpecComplex { re: 0, im: 0 };`
     (initial δ is zero)
   - `let ghost mut z_spec_seq: Seq<SpecComplex> = ...;` (the ref orbit
     ghost sequence, populated as the ref orbit loop runs)

3. **Add loop invariant clauses**:
   - `delta_buffers_match_spec(delta_re@, delta_re_sign, delta_im@, delta_im_sign, delta_spec, n as nat, frac_limbs as nat)`
   - `z_spec_seq.len() == iter + 1`
   - `forall|k| 0 <= k <= iter ==> z_spec_seq[k] satisfies the ref orbit recurrence`
   - `delta_spec is the result of `iter` applications of spec_pert_step`

4. **Chain the iteration body proofs**:
   - After each `signed_mul_to` or `signed_add_to` call, assert the
     buffer matches the corresponding intermediate ghost value
   - At the end of the iteration body, assert
     `delta_buffers_match_spec(...)` with the new `delta_spec` value
   - Update the ghost: `proof { delta_spec = spec_pert_step(z_k, delta_spec, dc_spec); }`

**Pitfalls**:
- This will be a *lot* of proof code. Plan to extract per-iteration helper
  lemmas like `lemma_perturbation_iteration_step` to keep the loop body's
  Z3 context manageable.
- The buffer ops use `_to` variants (not `_to_buf`), so Task 1 is not
  strictly required for *this* loop. But the reference orbit uses `_to_buf`,
  so Task 1 IS required for verifying the ref orbit ghost values.
- The sign-magnitude encoding adds complexity. Use `signed_val_of` from
  `limb_ops_proofs.rs` to express the buffer-to-spec relationship.
- Loops in the kernel that use `gpu_workgroup_barrier()` may need extra
  invariants about which thread wrote what to shared memory.

**Definition of done**: The perturbation while loop has a value-tracking
invariant. After the loop, we can assert `delta_buffers_match_spec(..., delta_spec_final, ...)`
where `delta_spec_final == spec_pert_step` applied N times.

---

### Task 3: Bridge to `theorem_perturbation_n_steps`

**Status**: Pending (`#79`)
**Effort**: Medium (depends on Task 2)
**Depends on**: Task 2

**What it is**:

`theorem_perturbation_n_steps` says: given `z_orbit: Seq<SpecComplex>` and
`delta_orbit: Seq<SpecComplex>` satisfying the per-step recurrences, the
N-step perturbation correctness holds:

```
forall k in [0, N): perturbation_step_correct(z_orbit, delta_orbit, c_ref, dc, k)
```

where `perturbation_step_correct(...)` says
`spec_full_orbit(z_orbit[k+1], delta_orbit[k+1]) == spec_ref_step(spec_full_orbit(z_orbit[k], delta_orbit[k]), c_pixel)`.

In English: tracking δ relative to Z gives the same result as computing
the full orbit at C_pixel directly. This is the core of perturbation theory.

**Approach**:

1. With Task 2's loop invariant, we have a ghost `delta_spec` and a sequence
   `z_spec_seq` after the loop.

2. Collect them into proper `Seq<SpecComplex>` arrays:
   ```rust
   let ghost z_orbit: Seq<SpecComplex> = z_spec_seq;  // already a Seq
   let ghost delta_orbit: Seq<SpecComplex> = ...;     // need to track this in the loop
   ```

3. Apply `theorem_perturbation_n_steps`:
   ```rust
   theorem_perturbation_n_steps(z_orbit, delta_orbit, c_ref_spec, dc_spec, max_iters as nat);
   ```

4. The conclusion gives correctness of the perturbation orbit for all k.

**Background needed**:
- `theorem_perturbation_n_steps` signature in `gpu_mandelbrot_kernel.rs`
- `perturbation_step_correct`, `spec_full_orbit`, `spec_ref_step`
- How `spec_pert_step` relates to `spec_full_orbit`

**Pitfalls**:
- The `delta_orbit` ghost sequence needs to be tracked throughout Task 2's
  loop invariant, not just `delta_spec`. Plan for it from the start.
- The application of `theorem_perturbation_n_steps` requires all the
  recurrences in its `requires` clause. The loop invariant must establish
  these.

**Definition of done**: After the perturbation while loop, the kernel can
assert `perturbation_step_correct` for all completed iterations, meaning the
buffer-level computation provably implements perturbation theory.

---

### Task 4: Refine the glitch detection criterion

**Status**: Pending (`#80`)
**Effort**: Medium (math-heavy; the right criterion is the hard part)
**Independent** of Tasks 1–3.

**What it is**:

The kernel checks `delta_re[n-1] > 3 || delta_im[n-1] > 3` and marks the
pixel as glitched. We've proved that this fires when `vec_val(δ) >= 4 * BASE^(n-1)`,
which is a *limb-level* statement. But the *true* glitch criterion in
perturbation theory is a *relative* one: when `|δ|/|Z|` grows enough that
the linearization `(Z+δ)² ≈ Z² + 2Zδ` becomes inaccurate.

We want to:
1. Define a mathematical criterion `is_glitch(z_spec, delta_spec)` that
   captures "the linearization is invalid here"
2. Prove the kernel's `δ[n-1] > 3` check is **sound** w.r.t. this criterion:
   when the check fires, `is_glitch(z_k, delta_k)` actually holds
3. Prove **completeness** w.r.t. this criterion: when `is_glitch` holds,
   the check (eventually) fires

**Approach**:

The right criterion is debatable. Two reasonable options:

**Option A — Relative magnitude**: `|delta| > some_factor * |Z|`. This is
simple but may be too coarse.

**Option B — Linearization error bound**: The next perturbation step's
contribution from the `δ²` term should be small relative to the `2*Z*δ`
term. Formally: `|δ²| < tolerance * |2*Z*δ|`, equivalent to
`|δ| < tolerance * 2 * |Z|`.

Option B is closer to the actual perturbation theory math. Let's go with it.

**Sub-steps**:

1. **Define the criterion**:
   ```rust
   spec fn is_glitch(z: SpecComplex, delta: SpecComplex, tolerance: int) -> bool {
       let z_mag_sq = z.re * z.re + z.im * z.im;
       let delta_mag_sq = delta.re * delta.re + delta.im * delta.im;
       // delta_mag_sq * 4 >= tolerance * z_mag_sq  (i.e., |δ|² ≥ tol * |Z|²)
       4 * delta_mag_sq >= tolerance * z_mag_sq
   }
   ```

2. **Soundness**: Prove that when `δ[n-1] > 3` fires, `is_glitch(z, delta, T)`
   holds for some chosen `T` consistent with the buffer threshold.

3. **Completeness**: Prove the converse — if the kernel state has
   `is_glitch(z_k, delta_k, T)`, then within at most 1 (or some bounded
   number of) iterations, the kernel's check will fire.

**Background needed**:
- `theorem_glitch_detection_soundness` in `gpu_mandelbrot_kernel.rs` (line ~1516)
  — already proves a related bound
- `corollary_mandelbrot_no_overflow` (line ~1591)
- Perturbation theory background (any Mandelbrot perturbation paper)

**Pitfalls**:
- The "right" criterion is subjective. Document the choice and why.
- Soundness and completeness may not both be tight — the kernel's coarse
  check may catch some non-glitches (false positives, but harmless) or miss
  some real glitches (false negatives, which would be bad). Aim for
  completeness (no false negatives) at the cost of some false positives.
- This task can be done independently of Tasks 1–3, but is much more
  *useful* in conjunction with Task 2 (where the kernel actually has
  access to the spec values).

**Definition of done**: The kernel has a defined `is_glitch` predicate
with proven soundness/completeness w.r.t. the kernel's check.

---

## Recommended Order

1. **Task 1** first — it's mostly mechanical, unblocks Task 2's reference
   orbit verification, and is the easiest to verify in isolation.

2. **Task 2** second — the meat of the work. Plan for it to take longer
   than expected; expect multiple iterations of refining the loop invariant.

3. **Task 3** third — a relatively short capstone once Task 2 lands.

4. **Task 4** can be done at any point but is most useful AFTER Task 2
   (when the kernel has spec values to talk about).

---

## Tools and Workflow Reminders

- **Use `verus_check` per-module** for fast iteration. Don't rebuild the
  whole crate after every change.
- **Profile rlimit** with `verus_profile` when something gets slow. The
  top function in `limb_ops.rs` is `mul2` at ~32M — keep an eye on it.
- **Extract heavy proofs** to focused helper lemmas. Per the rlimit tips,
  this is the highest-leverage optimization.
- **Commit incrementally** — checkpoint after each function/lemma verifies.
- **The `feedback_no_cache_issue` memory** — verification is deterministic.
  If something fails, diagnose, don't retry.

## Risk: Complexity Budget

Tasks 2 and 3 together are likely larger than the entire #68–#76 sequence
that we just did. Be prepared for:
- Multiple rlimit regressions requiring helper extractions
- Loop invariant clauses that don't auto-instantiate triggers
- Ghost variable scoping issues (let-bindings stripped at loop boundaries)
- Subtle off-by-one in iteration index tracking

Pace yourself; verify each piece before adding the next.
