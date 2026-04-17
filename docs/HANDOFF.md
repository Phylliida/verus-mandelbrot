# Karatsuba One-Level: Handoff Notes

## What Was Done

### The Proof (COMPLETE)

`mul_karatsuba_one_level_to` in `verus-fixed-point/src/fixed_point/limb_ops.rs` is **fully verified**: 281 verified functions, 0 errors across `limb_ops.rs` and `limb_ops_proofs.rs`.

**Postconditions proven:**
- `vec_val(output) == vec_val(a) * vec_val(b)` (value equation)
- Valid limbs on all 2n output positions
- Frame: elements outside `[out_off, out_off+2n)` unchanged
- Buffer lengths preserved

### The Bug Fix

Found and fixed a critical carry bug: step 4's half x half schoolbook dropped `asum_carry` and `bsum_carry` from the step 3 addition. Added step 4b with branchless carry correction using `select_limb`. Without this fix, the multiplication was silently wrong whenever `a_lo + a_hi` or `b_lo + b_hi` carried past the half-limb boundary.

### Integration (PARTIAL)

`signed_mul_to` now has a `scratch` parameter and uses Karatsuba for `n >= 8` (n even), falling back to schoolbook otherwise. `signed_mul_to_buf` (the single-buffer GPU variant) was left on schoolbook — it needs the same scratch plumbing.

---

## Architecture

### Proof Helpers (in `limb_ops_proofs.rs`)

The Karatsuba proof is split across 7 functions in the proofs module. Each has a clean Z3 context (the #1 lesson from this work — see below).

| Function | Purpose | Rlimit |
|----------|---------|--------|
| `add_inplace_propagate` | Add n limbs in-place + propagate carry through tail positions. Value equation via `lemma_vec_val_set_one`. | 3.5M |
| `karatsuba_carry_correct` | Step 4b carry correction. Two add-loops with branchless `select_limb`. Value equation tracking. | 42.4M |
| `karatsuba_combine` | Steps 5+6 extracted from main function. Sub_borrow loops + `add_inplace_propagate` call + value equation proof. | 17M |
| `lemma_karatsuba_z1_full_bounds` | Proves `z1_full = (a_lo+a_hi)(b_lo+b_hi)` and bounds from step 3/4/4b value equations. Two-step distributive expansion for nonlinear arithmetic. | ~1M |
| `lemma_karatsuba_z1_overflow_bound` | Proves `z1_overflow - bw1 - bw2` is 0 or 1 from algebraic bounds on cross terms. | <1M |
| `lemma_karatsuba_overflow_chain` | Combines z1_full_bounds + z1_overflow_bound + sub_borrow unwrapping in one clean context. | ~1M |
| `lemma_vec_val_set_one` | (Pre-existing) Single-element vec_val change. The workhorse for all value equation proofs. | <1M |

### Main Function Structure

```
mul_karatsuba_one_level_to:
  Step 1: mul_schoolbook_to(a_lo, b_lo) -> out[0..n]     (z0)
  Step 2: mul_schoolbook_to(a_hi, b_hi) -> out[n..2n]    (z2)
  Step 3: add_limbs_to(a_lo, a_hi) -> scratch[n..n+half]  (a_sum + carry)
          add_limbs_to(b_lo, b_hi) -> scratch[n+half..2n]  (b_sum + carry)
  Step 4: Vec copy + mul_schoolbook_to(a_sum_vec, b_sum_vec) -> scratch[0..n]
  Step 4b: karatsuba_carry_correct(scratch, a_sum_vec, b_sum_vec, carries) -> z1_overflow
  Step 5+6: karatsuba_combine(out, scratch, z1_overflow, ghost_values...)
    - Sub_borrow loops: z1 = z1_full - z0 - z2
    - add_inplace_propagate: out[half..2n] += z1
    - Karatsuba identity: vec_val(output) == a * b
```

### Ghost Value Chain

The proof uses "ghost bool capture" to preserve facts through Z3 context pollution:

```rust
// Capture a fact while it's fresh (right after establishing it)
let ghost step3_a_eq: bool = vec_val(a_sum_seq) + asum_carry.sem() * B
    == vec_val(a_lo_seq) + vec_val(a_hi_seq);
proof { assert(step3_a_eq); }

// ... many operations later, Z3 has forgotten the original fact ...

// Re-establish it from the ghost bool
proof { assert(step3_a_eq); }
```

Similarly, ghost snapshots chain frame conditions across `out@` versions:
```rust
let ghost out_post_step1 = out@;  // capture after step 1
// ... step 2 modifies out[n..2n] ...
// Later: prove out[0..n] unchanged via frame chain
assert(out@.subrange(0, n) =~= out_post_step1.subrange(0, n));
```

---

## Lessons Learned (Critical for Future Work)

### 1. Z3 Context Pollution is the #1 Enemy

Functions with >50 assertions consistently fail even with high rlimit. The SMT solver response time is **superlinear** in proof size. The solution: extract subproofs into separate functions in a `_proofs.rs` module.

**Before (failed at rlimit 300):** Everything inline in `mul_karatsuba_one_level_to` (~500 lines).
**After (works at rlimit 300):** Main function ~150 lines, heavy proofs in 7 helpers in `limb_ops_proofs.rs`.

### 2. Syntactic Trigger Matching

Z3 trigger matching is **syntactic**, not semantic. This is the most common source of "obvious" facts that Z3 can't prove:

```rust
// BAD: (scratch_off + half + k) as int doesn't match scratch_off as int + j
let ghost sv = scratch@[(scratch_off + half + k) as int].sem();
// invariant: forall |j| 0 <= j < n ==> scratch@[(scratch_off as int + j)].sem() < LIMB_BASE()
assert(sv < LIMB_BASE());  // FAILS — trigger doesn't match!

// GOOD: define ghost with matching index expression
let ghost hk = (half + k) as int;
let ghost sv = scratch@[(scratch_off as int + hk) as int].sem();
assert(0 <= hk && hk < n as int);  // triggers the forall
// sv < LIMB_BASE() now provable
```

### 3. `lemma_vec_val_set_one` Over `sem_seq`/`limbs_val_subrange_extend`

For tracking value equations through `out.set(idx, val)`, use `lemma_vec_val_set_one(pre_subrange, post_subrange, idx)` instead of the `sem_seq` + `limbs_val_subrange_extend` pattern. The `sem_seq` unfolding fails in complex contexts because `Seq::new` indexing doesn't auto-simplify.

### 4. Ghost Bool Capture for Cross-Mutation Facts

Facts about `out@` established before mutations (like `mul_schoolbook_to` calls) get lost because Z3 creates new array versions. Capture them immediately as `let ghost eq: bool = fact; proof { assert(eq); }`. The ghost bool persists through any number of mutations.

### 5. Use Existing Verified Functions

Instead of re-proving carry chains inline, call `add_limbs_to` (has value equation postcondition), `mul_schoolbook_to` (has value equation), etc. This is why step 3 was changed from a manual loop to `add_limbs_to` calls — zero proof effort.

### 6. Nonlinear Arithmetic: Break Into 2-Term Steps

Z3's `by(nonlinear_arith)` can handle `(A)(B) = A*b_sum + A*cb*B` (2-term distributive law) but times out on 4-term expansions. Break `(a+c*B)(b+d*B)` into:
```rust
assert(A * C == a * C + c * B * C) by(nonlinear_arith) requires A == a + c * B;
assert(a * C == a * b + a * d * B) by(nonlinear_arith) requires C == b + d * B;
// etc.
```

### 7. `by(nonlinear_arith)` Requires Are Checked Against Ambient Context

The `requires` clause of `assert(P) by(nonlinear_arith) requires R;` means: "prove R from ambient facts, then prove P using ONLY R and nonlinear arithmetic." This means R must be provable from the current context, and P is proved in isolation with only R.

### 8. LIMB_BASE() > N Needs Explicit Proof

`LIMB_BASE() = 2^32` is a constant, but Z3 doesn't auto-evaluate it. Use:
```rust
assert(LIMB_BASE() > 3) by {
    reveal_with_fuel(limb_power, 2);
    use crate::fixed_point::limbs::limb_base;
}
```

---

## What Remains to Get Karatsuba on GPU

### Step 1: Thread `kscratch` Through the Call Chain

`signed_mul_to` now takes a `scratch: &mut Vec<T>` parameter. Need to:

1. **Add `kscratch` parameter** to these functions (they call `signed_mul_to`):
   - `perturbation_iteration_step` in `gpu_perturbation_entry.rs`
   - `direct_computation_fallback` in `gpu_perturbation_entry.rs`
   - `gpu_mandelbrot_kernel` in `gpu_mandelbrot_entry.rs`
   - Any wrapper functions in the call chain

2. **Add `kscratch` as a thread-local 2n-limb array** in the GPU entry points. The transpiler converts `#[gpu_local(N)]` Vec parameters to WGSL `var<private>` arrays.

3. **Update all ~19 call sites** of `signed_mul_to` to pass `&mut kscratch, 0usize`. Pattern:
   ```rust
   // Before:
   signed_mul_to(&t1, &s1, &t2, &s2, &mut t3, 0, &mut lprod, 0, n, frac);
   // After:
   signed_mul_to(&t1, &s1, &t2, &s2, &mut t3, 0, &mut lprod, 0, &mut kscratch, 0, n, frac);
   ```

4. **Do the same for `signed_mul_to_buf`** — add scratch parameter, update its ~3 call sites.

### Step 2: Regenerate WGSL Shaders

```bash
cd verus-mandelbrot/web && bash generate_shaders.sh
```

This transpiles the Verus source to WGSL for n=4,8,16,32,64.

### Step 3: Rebuild and Run Profiler

```bash
# Build
cd verus-cad
verus-dev/source/target-verus/release/cargo-verus build \
  --manifest-path Cargo.toml -p verus-mandelbrot \
  --features profiler --release --no-verify --bin profile_shader

# Run (NixOS)
LD_LIBRARY_PATH=/nix/store/HASH-vulkan-loader-VERSION/lib \
VK_ICD_FILENAMES=/run/opengl-driver/share/vulkan/icd.d/nvidia_icd.x86_64.json \
./verus-mandelbrot/target/release/profile_shader --limbs 4,8,16,32 --res 256 --iters 500 --runs 5
```

Or via MCP:
```
mcp__verus__compile(crate_name="verus-mandelbrot", features="profiler", release=true, extra_args="--bin profile_shader")
```

### Expected Results

| N limbs | Schoolbook (baseline) | Karatsuba (expected) | Savings |
|---------|----------------------|---------------------|---------|
| 4       | 10ms                 | 10ms (fallback)     | 0%      |
| 8       | 30ms                 | ~25ms               | ~17%    |
| 16      | 113ms                | ~85ms               | ~25%    |
| 32      | 915ms                | ~690ms              | ~25%    |

The Karatsuba does 3 half-size schoolbooks instead of 1 full-size. For n=16: 3 x schoolbook(8) = 3 x 64 = 192 ops vs schoolbook(16) = 256 ops.

### Potential Issues

1. **Transpiler bare blocks**: The `{ use ...; expr }` pattern confuses the transpiler. Already fixed by hoisting `use` statements to function level. If new block expressions appear, hoist them similarly.

2. **Vec allocation in transpiled code**: Any `Vec::new()` + `push()` in code that gets transpiled to WGSL will fail. The scratch parameter approach avoids this — the caller provides a pre-allocated buffer.

3. **GPU register pressure**: Adding a 2n-limb `kscratch` array increases per-thread register usage. For n=32, that's 64 extra u32 registers. Monitor for occupancy regressions on the RTX 3090.

4. **The `n <= 6` fallback**: Inside `mul_karatsuba_one_level_to`, the `n <= 6` case falls back to schoolbook. The transpiler will emit both branches. Since n is a compile-time constant in each generated shader, the dead branch should be optimized away by the WGSL compiler.

---

## File Summary

### Modified
- `verus-fixed-point/src/fixed_point/limb_ops.rs` — `mul_karatsuba_one_level_to` (exec + proof), `signed_mul_to` (Karatsuba wiring), `add_limbs_to` / `mul_schoolbook_to` (used by Karatsuba)
- `verus-fixed-point/src/fixed_point/limb_ops_proofs.rs` — 7 new proof helpers (add_inplace_propagate, karatsuba_carry_correct, karatsuba_combine, 3 lemmas, 1 chain helper)

### Not Yet Modified (need scratch plumbing)
- `verus-mandelbrot/src/gpu_perturbation_entry.rs` — ~15 `signed_mul_to` call sites
- `verus-mandelbrot/src/gpu_mandelbrot_entry.rs` — ~5 `signed_mul_to` call sites
- `verus-mandelbrot/web/generate_shaders.sh` — may need adjustment if new gpu_local arrays change the sed patterns
