# Loop Body Extraction Plan (Task #81)

**Status**: Open
**Prerequisite for**: #78 (perturbation loop value invariants), #79
**Effort estimate**: Medium-High (~200-400 lines including parameter plumbing)
**Discovered**: 2026-04-10 while attempting #78 in-place

---

## Why This Is Needed

The perturbation while loop in `gpu_perturbation_entry.rs` is too monolithic
to add value-tracking ghost invariants in-place. We tried adding two simple
ghost-int invariants (`delta_re_int`, `delta_im_int`) for tracking the
signed-magnitude values of `delta_re` and `delta_im` across iterations.
With `rlimit(200)` (already 4× the default), the loop's Z3 context exceeded
its budget.

The root cause: the kernel function `mandelbrot_perturbation` is one giant
function containing:
- The reference orbit `for iter in 0..max_iters` loop
- The perturbation `while iter < max_iters` loop
- ~30 buffer ops per perturbation iteration
- Many local variables (`delta_re`, `delta_im`, `dc_re`, `dc_im`, `t1`-`t5`,
  `lprod`, `ls1`, `ls2`, `ref_a`, `ref_b`)
- Multiple nested if/else branches for sign validation and glitch checks

Adding any new invariants forces Z3 to track them through every iteration's
worth of buffer ops. The strengthened `*_to_buf` postconditions (#77) already
contributed enough facts that we had to bump rlimit to 100. Adding more
pushes it over.

**The fix**: extract the per-iteration body into a focused helper function
with explicit requires/ensures. The helper has its own clean Z3 context.

---

## What to Extract

The target is the perturbation iteration body — specifically the ~30 buffer
ops that compute `δ' = 2*Z*δ + δ² + Δc`. This is currently inlined in
`gpu_perturbation_entry.rs` around lines 895-928.

### Inputs (read-only)

- `z_re_slice: &[u32]` — `Z_k.re` from shared memory (`vslice(wg_mem, zn_re)`)
- `z_re_sign: u32`
- `z_im_slice: &[u32]` — `Z_k.im` from shared memory
- `z_im_sign: u32`
- `dc_re: &Vec<u32>` — Δc.re (constant across iterations)
- `dc_re_sign: u32`
- `dc_im: &Vec<u32>` — Δc.im
- `dc_im_sign: u32`
- `n: u32` — number of limbs
- `frac_limbs: u32` — fractional limb count

### In-out (read AND write — these are the perturbation state)

- `delta_re: &mut Vec<u32>`
- `delta_im: &mut Vec<u32>`
- (Their signs are returned from the function, so no `&mut` for those)

### Scratch (write-only on entry, read-write internally)

- `t1, t2, t3, t4, t5: &mut Vec<u32>`
- `lprod: &mut Vec<u32>` — 2n-limb product buffer
- `ls1, ls2: &mut Vec<u32>` — local signed scratch

### Returns

- `(new_delta_re_sign: u32, new_delta_im_sign: u32)`

---

## Helper Function Skeleton

```rust
fn perturbation_iteration_step(
    z_re_slice: &[u32], z_re_sign: u32,
    z_im_slice: &[u32], z_im_sign: u32,
    delta_re: &mut Vec<u32>, delta_re_sign_in: u32,
    delta_im: &mut Vec<u32>, delta_im_sign_in: u32,
    dc_re: &Vec<u32>, dc_re_sign: u32,
    dc_im: &Vec<u32>, dc_im_sign: u32,
    t1: &mut Vec<u32>, t2: &mut Vec<u32>,
    t3: &mut Vec<u32>, t4: &mut Vec<u32>, t5: &mut Vec<u32>,
    lprod: &mut Vec<u32>,
    ls1: &mut Vec<u32>, ls2: &mut Vec<u32>,
    n: u32, frac_limbs: u32,
) -> (out: (u32, u32))  // (new_delta_re_sign, new_delta_im_sign)
    requires
        // Sizes
        old(delta_re)@.len() == n as int,
        old(delta_im)@.len() == n as int,
        dc_re@.len() == n as int,
        dc_im@.len() == n as int,
        old(t1)@.len() == n as int,
        old(t2)@.len() == n as int,
        old(t3)@.len() == n as int,
        old(t4)@.len() == n as int,
        old(t5)@.len() == n as int,
        old(lprod)@.len() == 2 * n as int,
        old(ls1)@.len() == n as int,
        old(ls2)@.len() == n as int,
        z_re_slice@.len() >= n as int,
        z_im_slice@.len() >= n as int,
        // Bounds
        n >= 1, n <= 8, n as int <= 0x1FFF_FFFF,
        frac_limbs <= n, frac_limbs + n <= 2 * n,
        // Sign validity
        z_re_sign == 0u32 || z_re_sign == 1u32,
        z_im_sign == 0u32 || z_im_sign == 1u32,
        delta_re_sign_in == 0u32 || delta_re_sign_in == 1u32,
        delta_im_sign_in == 0u32 || delta_im_sign_in == 1u32,
        dc_re_sign == 0u32 || dc_re_sign == 1u32,
        dc_im_sign == 0u32 || dc_im_sign == 1u32,
        // Valid limbs
        valid_limbs(z_re_slice@.subrange(0, n as int)),
        valid_limbs(z_im_slice@.subrange(0, n as int)),
        valid_limbs(old(delta_re)@), valid_limbs(old(delta_im)@),
        valid_limbs(dc_re@), valid_limbs(dc_im@),
    ensures
        // Sizes preserved
        delta_re@.len() == n as int,
        delta_im@.len() == n as int,
        t1@.len() == n as int,
        t2@.len() == n as int,
        t3@.len() == n as int,
        t4@.len() == n as int,
        t5@.len() == n as int,
        lprod@.len() == 2 * n as int,
        ls1@.len() == n as int,
        ls2@.len() == n as int,
        // Sign validity
        out.0 == 0u32 || out.0 == 1u32,
        out.1 == 0u32 || out.1 == 1u32,
        // Valid limbs preserved
        valid_limbs(delta_re@), valid_limbs(delta_im@),
        // (Future) Value equation: connecting to spec_pert_step
        // For now, just provide the bounds. Add value equation in #78.
{
    // Move the ~30 buffer ops here
    // ...
    (new_dr_s, new_di_s)
}
```

---

## Step-by-Step Plan

### Stage A: Extract with weak postcondition (no value equation)

1. **Copy the iteration body** (lines ~895-928 of `gpu_perturbation_entry.rs`)
   into a new top-level `perturbation_iteration_step` function.
2. **Set up requires/ensures** with just the structural bounds (sizes, sign
   validity, valid_limbs). No value equation yet.
3. **Replace the inline body** with a call to the helper.
4. **Verify**. The kernel function's rlimit should drop dramatically because
   the heavy proof obligations move into the helper.
5. **Commit checkpoint**.

### Stage B: Add value-tracking postcondition

6. **Define a spec function** capturing the kernel's per-iteration computation:
   ```rust
   spec fn perturbation_step_buffer_value(
       z_re_v: int, z_re_s: u32,
       z_im_v: int, z_im_s: u32,
       delta_re_v_in: int, delta_re_s_in: u32,
       delta_im_v_in: int, delta_im_s_in: u32,
       dc_re_v: int, dc_re_s: u32,
       dc_im_v: int, dc_im_s: u32,
       n: nat, frac_limbs: nat,
   ) -> (int, int) {
       // The truncated/wrapped result of one perturbation step
       // (using signed_val_of for sign-magnitude → signed integer)
       ...
   }
   ```
   This function describes what one iteration computes at the value level,
   accounting for truncation and the sign-magnitude encoding.

7. **Add the value equation to the helper's ensures**:
   ```rust
   ensures
       ...
       (vec_val(delta_re@), vec_val(delta_im@)) == perturbation_step_buffer_value(...)
   ```

8. **Prove it inside the helper** by chaining the strengthened buffer op
   postconditions. This is the longest part of Stage B.

9. **Verify**. The helper's Z3 context is focused, so it should fit in budget.

### Stage C: Connect to perturbation theory in the kernel loop

10. **Add ghost variables** at the kernel's perturbation loop entry:
    ```rust
    let ghost mut delta_spec: SpecComplex = SpecComplex { re: 0, im: 0 };
    ```

11. **Add a loop invariant** relating `delta_spec` to the buffer state via
    `signed_val_of`.

12. **After each iteration**, update `delta_spec` to match the helper's
    output via `proof { delta_spec = ...; }`.

13. **Verify**. The kernel's Z3 context now only handles the loop invariant
    bookkeeping, not the iteration body details.

### Stage D: Bridge to spec_pert_step (#78 + #79)

14. **Show that `perturbation_step_buffer_value` matches `spec_pert_step`**
    when no overflow occurs. This is a separate lemma:
    ```rust
    proof fn lemma_buffer_step_matches_spec(
        z: SpecComplex, delta: SpecComplex, dc: SpecComplex,
        ...
    )
        requires
            // Bounds preventing overflow
        ensures
            perturbation_step_buffer_value(...) == 
                signed_components_of(spec_pert_step(z, delta, dc))
    ```

15. **Track the spec sequence** in the kernel loop:
    ```rust
    let ghost mut z_orbit: Seq<SpecComplex> = ...;
    let ghost mut delta_orbit: Seq<SpecComplex> = ...;
    ```

16. **Apply `theorem_perturbation_n_steps`** after the loop.

---

## What the Helper Body Looks Like

The body is a copy of the existing iteration body. Here's the structure
(simplified — see lines ~895-928 for the actual code):

```rust
// Part A: 2*Z*δ
let s1 = signed_mul_to(z_re_slice, &z_re_sign, &delta_re_view, &delta_re_sign_in,
                       t1, 0, lprod, 0, n_us, frac_us);
let s2 = signed_mul_to(z_im_slice, &z_im_sign, &delta_im_view, &delta_im_sign_in,
                       t2, 0, lprod, 0, n_us, frac_us);
let s3 = signed_mul_to(z_re_slice, &z_re_sign, &delta_im_view, &delta_im_sign_in,
                       t3, 0, lprod, 0, n_us, frac_us);
let s4 = signed_mul_to(z_im_slice, &z_im_sign, &delta_re_view, &delta_re_sign_in,
                       t4, 0, lprod, 0, n_us, frac_us);

// 2*Z*δ real = 2*(Z_re*δ_re - Z_im*δ_im)
let d1_s = signed_sub_to(t1, &s1, t2, &s2, t5, 0, ls1, 0, ls2, 0, n_us);
let tzd_re_s = signed_add_to(t5, &d1_s, t5, &d1_s, t1, 0, ls1, 0, ls2, 0, n_us);
// (etc. — see existing inline code)

// Part B: δ²
// Part C: Combine — δ' = (2Zδ) + δ² + Δc

// Return new signs
(new_dr_s, new_di_s)
```

The challenge is that **`delta_re` and `delta_im` are passed as `&mut`** but
also **read** by some of the early ops. The Rust borrow checker may complain.
Workarounds:
- Read into local Vec snapshots first (e.g., `let delta_re_snap: Vec<u32> = clone`)
- Reorder operations so reads complete before writes begin
- Use ghost views

The existing inline code passes `&delta_re` (immutable) AND uses `delta_re` later
because they're in different scopes. The extracted function will need careful
borrow management.

---

## Pitfalls and Things to Watch For

### Pitfall 1: Borrow checker on `&mut` Vec parameters

The 12+ `&mut Vec<u32>` parameters might trip up Rust's borrow checker. Verus
inherits Rust's borrow rules. If multiple `&mut` references exist, they must
not alias.

**Workaround**: pass Vecs by value when possible, or use ghost-tracked indices
into a single combined buffer.

### Pitfall 2: Many parameters → many trigger candidates

Verus quantifier triggers on parameters can multiply. Use specific `#[trigger]`
annotations on the postconditions to control them.

### Pitfall 3: Length-preservation invariants

Each `*_to`/`*_to_buf` call preserves the sizes of its `&mut` arguments. The
helper's ensures must list ALL of these explicitly. Missing one will cause
the kernel's loop invariant to fail (e.g., `t1@.len() == n as int`).

### Pitfall 4: Frame conditions for the kernel's untouched buffers

The helper modifies many buffers but the kernel's loop invariant might also
care about buffers the helper doesn't touch (e.g., `dc_re`, `dc_im`, the ref
orbit area in `wg_mem`). Make sure the helper's ensures don't accidentally
imply these are modified.

### Pitfall 5: Ghost reasoning across the helper boundary

In the loop body, after `let (new_dr_s, new_di_s) = perturbation_iteration_step(...);`,
the kernel needs to know things about `delta_re` and `delta_im` that the helper
just modified. These come from the helper's ensures clauses. Plan for what
ghost values the loop invariant needs to carry.

### Pitfall 6: Different rlimit budgets

The helper has its own rlimit (default ~30M). With ~30 buffer ops each
producing facts, the helper itself may need a bumped rlimit. This is fine
because the kernel function's budget is freed up.

### Pitfall 7: The helper isn't a transpilation target

The transpiler walks through inline ops and generates WGSL. If the helper
becomes its own function, the transpiler may not know to inline it. **Check**
that the existing transpiler handles the helper, OR mark it
`#[verifier::external_body]` for transpilation purposes (and verify the body
in Verus separately).

Alternatively: keep the helper inline in the kernel, but use Verus's
`assert by(...)` blocks with focused proof contexts instead of full extraction.
This is harder because the Z3 context for the surrounding code still pollutes.

---

## Key Files

| File | What |
|------|------|
| `verus-mandelbrot/src/gpu_perturbation_entry.rs` | Where the kernel + helper live |
| `verus-fixed-point/src/fixed_point/limb_ops.rs` | The strengthened `*_to`/`*_to_buf` ops |
| `verus-fixed-point/src/fixed_point/limb_ops_proofs.rs` | Helper lemmas (signed_val_of, etc.) |
| `verus-mandelbrot/src/gpu_mandelbrot_kernel.rs` | FpComplex-level math, spec_pert_step, theorems |
| `verus-mandelbrot/docs/exec-verification-roadmap.md` | The full roadmap (Task list 1-4) |
| `verus-mandelbrot/docs/session-2026-04-10-summary.md` | Chronological session record |

---

## What's Already Verified (As of 2026-04-10)

| # | What | Status |
|---|------|--------|
| #68 | `add_limbs_to` value equation | ✅ |
| #69 | `sub_limbs_to` value equation | ✅ |
| #70 | `signed_mul_to` truncated product equation | ✅ |
| #71 | `signed_add_to` 3-way modular sum equation | ✅ |
| #72 | Escape check polarity (per-iteration) | ✅ |
| #73 | Magnitude full equation (per-iteration) | ✅ |
| #74 | Signed-input chain via signed_val_of (per-iteration) | ✅ |
| #75 | Reference orbit error accumulation (standalone math) | ✅ |
| #76 | Glitch detection completeness (limb level) | ✅ |
| #77 | `*_to_buf` value equations | ✅ |
| #80 | Glitch criterion soundness (math level) | ✅ |
| #78 | Perturbation loop value invariants | 🛑 Blocked on #81 |
| #79 | Bridge to `theorem_perturbation_n_steps` | 🛑 Blocked on #78 |
| #81 | **Loop body extraction** | 📝 **THIS DOC** |

---

## Definition of Done for #81

- [ ] `perturbation_iteration_step` exists as a top-level function in
      `gpu_perturbation_entry.rs`
- [ ] The kernel's perturbation while loop calls it instead of inlining
- [ ] Both functions verify (with possibly bumped per-function rlimit)
- [ ] Kernel function's rlimit is at or below where it was before #77
      (since the heavy work moved to the helper)
- [ ] No new TODOs or `external_body` annotations introduced
- [ ] Existing kernel proofs (#72, #73, #74, #76) still hold

After #81 lands, #78 becomes attempt-able.

---

## Estimated Effort

- **Stage A** (extract with weak postconditions): ~half a day
  - Mostly mechanical copy + parameter plumbing
  - Borrow checker fights are the main risk
- **Stage B** (add value equation to helper): ~1-2 days
  - Define `perturbation_step_buffer_value` spec fn
  - Chain through ~30 buffer ops in the helper proof
- **Stage C** (kernel loop invariants using helper): ~half a day
  - Add ghost variables and update them across iterations
- **Stage D** (bridge to `spec_pert_step`): ~1 day
  - Define and prove `lemma_buffer_step_matches_spec`
  - Apply `theorem_perturbation_n_steps`

**Total estimate**: 3-4 days of focused work for the full chain (#81 → #78 → #79).

The doc you're reading is a handover prepared after the 2026-04-10 session,
which completed the foundation work but discovered the extraction prerequisite.
