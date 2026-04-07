# Session Summary: Verified GPU Mandelbrot with Perturbation Theory

**Date:** 2026-04-06 (second session)
**Scope:** GPU profiling, 72x speedup, perturbation theory, 249+ formal proofs, verified GPU kernel

---

## What We Built

### GPU Performance
- **GPU profiler** (`mandelbrot-profiler/`): headless wgpu tool with timestamp queries, parameter sweeps, CSV output
- **`#[gpu_local(N)]` annotation**: transpiler emits thread-local `array<u32, N>` instead of global scratch buffer offsets. **72x speedup** (355ms to 5ms at 256x256 on RTX 3090)
- **`#[gpu_skip]`**: suppresses scratch offset computation for scalar variables (sign values)
- **`#[gpu_shared(SIZE)]`**: workgroup shared memory via `var<workgroup>`
- **Unused buffer elimination**: emitter skips buffer declarations with zero references

### Perturbation Theory Kernel
- **Reference orbit** computed by thread 0 in workgroup shared memory
- **Perturbation iteration** by all 256 threads using local arrays
- **Glitch detection**: overflow-only (integer limb > 3), not float-style |delta|>|Z| (wrong for fixed-point)
- **Iterative refinement**: up to 5 rounds of re-referencing within each workgroup
- **BigInt deep zoom** in browser via JavaScript BigInt center coordinates
- **Bug found and fixed**: reference orbit escape wasn't marking pixels as glitched

### Formal Verification (249+ verified, 0 errors)

#### Arithmetic Layer (verus-fixed-point: 191 verified)
| Function | Postcondition | Bug it catches |
|----------|--------------|----------------|
| `signed_add` | out = a+b (mod P), with overflow conditions | select_limb swaps, wrong branch logic |
| `signed_sub` | out = a-b (mod P) | inherits from neg+add |
| `signed_mul` | sign XOR + `floor(a*b/scale) % P` | wrong product, wrong truncation offset |
| `neg` | out = -a (exact) | sign flip errors |
| `generic_add_limbs` | carry <= 1 | simplifies downstream proofs |
| `lemma_signed_add_exact` | |a+b| < P implies exact result | bridges modular to exact |
| `lemma_truncated_product` | out = floor(a*b/scale) % P via decomposition | wrong slice offset |

#### Perturbation Theory Layer (verus-mandelbrot: 58 verified)
| Theorem | What it proves |
|---------|---------------|
| `theorem_perturbation_correctness` | (Z+delta)' = (Z+delta)^2 + c_pixel (algebraic identity) |
| `theorem_perturbation_n_steps` | Correct for all N iterations (induction) |
| `theorem_glitch_detection_soundness` | |delta'| <= 4RT + 2T^2 + eps (no overflow) |
| `corollary_mandelbrot_no_overflow` | R=2, T=3, eps=1: |delta'| <= 43 < 2^32 |
| `theorem_escape_check_polarity` | borrow==0 iff magnitude >= threshold |
| `theorem_complex_square_error` | re error [0,1] ulps, im error [0,2] ulps |
| `theorem_complex_mul_error` | same bounds as squaring |
| `theorem_perturbation_step_error` | re <= 2, im <= 4 ulps per step |
| `theorem_n_step_error` | N*K ulps after N iterations |
| `corollary_escape_practically_exact` | escape detection accurate to ~10^-26 |
| `complex_add` | modular postcondition on both components |

---

## Key Technical Decisions

### Why overflow-only glitch detection works for fixed-point
Float-style `|delta| > |Z|` triggers whenever Z passes near zero (every orbit). With multi-precision fixed-point, there's no mantissa truncation, so `2*Z*delta + delta^2` stays accurate even when |delta| >> |Z|. Only actual fixed-point overflow (integer limb > 3) needs detection. This was discovered after blocky 16x16 artifacts appeared with aggressive glitch detection.

### Why `&[T]` slices instead of `&Vec<T>` for _to functions
Verus supports `&[T]` slices with the `@` operator (gives `Seq<T>`). GPU kernels need to pass sub-ranges of buffers (`&wg_mem[offset..]`). With `&Vec<T>`, this requires creating new Vecs (allocation, forbidden on GPU). With `&[T]`, `vslice(wg_mem, offset)` returns a slice reference naturally. `&Vec<T>` auto-derefs to `&[T]` so existing callers are unaffected.

### Why `(&mut Vec<T>, offset)` for mutable _to params
Verus doesn't support `&mut [T]` return types. Can't create mutable sub-slices. Solution: pass the full Vec plus an offset. Functions access `buf.set(offset + i, val)` internally. This matches the GPU model (buffer + offset) and Verus's type system.

### Why `_buf` variants for shared memory operations
Rust's borrow checker prevents passing `&mut wg_mem` three times to `signed_add_to(a, b, out, tmp1, tmp2)`. Solution: `signed_add_to_buf` takes a single `&mut Vec<T>` with three offsets. Bodies marked `external_body` pending non-overlap preconditions.

### Why GPU annotations as comments
Verus rejects unknown attributes (`#[gpu_kernel]`, `#[gpu_buffer]`). Moving them to comments (`// #[gpu_kernel(...)]`) lets Verus ignore them while the transpiler still reads them. The transpiler was updated to parse both `attribute_item` nodes and `line_comment` nodes for GPU annotations.

---

## What Remains (Ordered by Impact)

### 1. Non-vacuous kernel invariants (HIGH IMPACT)
**Status:** The kernel compiles in Verus with loop invariants, but assertions are vacuously true because internal function call preconditions (`valid_limbs`, buffer size bounds) aren't satisfied from the kernel's weak `requires`.

**What's needed:**
- Encode the shared memory layout as preconditions: orbit region size, ref_c position, tmp region bounds, vote buffer position
- Express `c_data` layout: stride per pixel, offset computations
- Add `valid_limbs` propagation: show that buffer regions written by `_to` functions maintain valid limb bounds
- Add offset non-overlap preconditions to `_buf` functions (currently `external_body`)

**How to do it:**
- Define spec functions for layout: `orbit_offset(iter, z_stride)`, `ref_c_offset(max_iters, z_stride)`, etc.
- Add these as `requires` on the kernel function
- Add `valid_limbs` to loop invariants (carried forward from function postconditions)
- For `_buf` non-overlap: add `requires out_off + n <= tmp1_off || tmp1_off + n <= out_off` (and all pairs)

**Expected result:** The post-loop assertion `escaped_iter < max_iters || is_glitched == 1u32` would fail if the `is_glitched = 1u32` line is removed (catching the actual bug).

### 2. Make _buf function bodies verified (MEDIUM)
**Status:** `signed_add_to_buf`, `signed_sub_to_buf`, `signed_mul_to_buf` are `#[verifier::external_body]` (trusted).

**What's needed:**
- Non-overlap preconditions on offset regions
- `valid_limbs` invariant across interleaved writes (buf[out_off+i] write doesn't affect buf[tmp1_off+j] validity when regions don't overlap)
- Frame reasoning: writing to one offset region preserves reads from another

**How to do it:**
- Add `requires` for non-overlap of all offset regions
- Use `assert forall` with triggers on `buf@[k]` to maintain valid_limbs across set() calls
- The proof structure mirrors `signed_add_to` (already proven for separate Vecs)

### 3. Transpiler compatibility for new interfaces (MEDIUM)
**Status:** The `_buf` functions and `(&mut Vec<T>, offset)` pattern aren't recognized by the transpiler yet.

**What's needed:**
- Transpiler should recognize `signed_add_to_buf(vslice(wg_mem, X), &sign, vslice(wg_mem, Y), &sign, wg_mem, off1, off2, off3, n)` and emit the correct WGSL with buffer offsets
- The `vget`/`vset`/`vslice` helpers should be transparent to the transpiler (emit as direct indexing)

**How to do it:**
- Add `vget`/`vset`/`vslice` to the transpiler's known function list (emit as `buf[i]`, `buf[i]=val`, `&buf[offset..]`)
- Add `_buf` variants to the transpiler's function resolution (map to the same WGSL as the non-buf versions with appropriate buffer monomorphization)

### 4. Complex operation exec-to-spec with truncation (LOW, nice-to-have)
**Status:** We proved truncation error bounds at the spec level. The gap: connecting the exec `signed_mul` output (via `truncated_product_spec`) through `complex_square` to `spec_complex_square` requires bounded-input reasoning.

**What's needed:**
- `lemma_signed_add_exact` and `lemma_signed_sub_exact` applied in `complex_square` context
- Mandelbrot escape radius bounds on inputs: `|Z| < 2` ensures all intermediate values < P
- Chain: bounded inputs -> exact add/sub -> truncated mul -> complex_square error bound -> perturbation step error

**How to do it:**
- Add `requires |z.re.signed_val()| < P/2, |z.im.signed_val()| < P/2` to `complex_square`
- Call `lemma_signed_add_exact` after each `signed_add`/`signed_sub` call
- The truncation error bounds (already proven) give the final error

---

## Lessons Learned

### 1. Proofs at the wrong level don't catch bugs
We had 249 verified proofs (arithmetic correctness, perturbation theory, truncation bounds, escape detection) but the GPU kernel still had a rendering bug. The proofs verified individual functions and mathematical identities, but NOT the kernel orchestration (buffer offsets, iteration logic, glitch marking). The bug was in the composition — the `break` on reference escape that forgot to set `is_glitched`.

**Takeaway:** Verify the SAME code that runs on the GPU. Spec-level proofs are necessary but not sufficient.

### 2. Verus limitations for GPU code
- `&mut [T]` return types unsupported -> can't create mutable sub-slices -> need `(&mut Vec<T>, offset)` pattern
- `&v[offset..]` range indexing unsupported in exec mode -> need `vstd::slice::slice_subrange` wrapper
- Multiple `&mut` borrows of same Vec -> need single-buffer `_buf` variants
- Weak `requires` make assertions vacuously true -> need comprehensive buffer layout specs

**Takeaway:** Making GPU kernels Verus-verifiable is possible but requires specific patterns (`vget`/`vset`/`vslice`, `_buf` variants, comment-based annotations). These could be abstracted into a "Verus GPU library."

### 3. Rlimit tips matter
- Proofs with >50 assertions in one function body timeout
- Extract to helper proof functions (own Z3 context)
- Use `assert(F) by(nonlinear_arith) requires ...;` to scope facts
- `lemma_vec_val_bounded` + `nonlinear_arith` for carry/overflow bounds
- `lemma_mod_multiples_vanish` + `lemma_small_mod` for division/modulo

### 4. Fixed-point perturbation is different from floating-point
- No mantissa truncation -> glitch detection should be overflow-only
- Multi-precision carries are exact -> the modular reduction `(a+b) % P` rarely triggers for bounded Mandelbrot values
- Truncation error is bounded and accumulates linearly (400 ulps after 200 iterations with 96 fractional bits = ~10^-27)

### 5. The proof chain architecture
```
Limb arithmetic (exact) -> Signed ops (modular/exact) -> Complex ops (truncated)
    -> Perturbation theory (spec identity) -> N-step error (linear accumulation)
        -> Escape detection (practically exact)
```
Each layer builds on the one below. Breaking the chain at any point (e.g., wrong truncation offset in signed_mul) would propagate errors upward.

---

## File Changes Summary

### verus-fixed-point/src/fixed_point/limb_ops.rs
- `&Vec<T>` -> `&[T]` for immutable params of all _to functions
- `&mut [T]` -> `(&mut Vec<T>, offset: usize)` for mutable params
- Added `_buf` variants for single-buffer multi-offset operations
- Added `use vstd::slice::SliceAdditionalExecFns` for `.set()` on slices
- Relaxed `a@.len() == n` to `>= n` for sub_limbs_to, mul_schoolbook_to
- Added overflow bounds (`out_off + n < usize::MAX`) to requires and invariants
- Added `lemma_vec_val_eq_from_sem_eq`, `lemma_truncated_product`, `lemma_signed_add_exact`, `lemma_signed_sub_exact`
- Strengthened `signed_add` postcondition with overflow conditions

### verus-fixed-point/src/runtime_fixed_point.rs
- Added `signed_val()` postconditions to `neg`, `signed_add`, `signed_sub`, `signed_mul`
- Extracted `lemma_signed_add_correct` proof helper (rlimit optimization)
- Added `truncated_product_spec` spec function

### verus-mandelbrot/src/gpu_mandelbrot_kernel.rs
- Added `SpecComplex`, `spec_complex_square`, `spec_pert_step`, `spec_ref_step`
- 10+ proof theorems (perturbation correctness, truncation error, escape detection, glitch soundness)
- `FpComplex::to_spec()` and `modulus()` helper specs

### verus-mandelbrot/src/gpu_perturbation_entry.rs
- Wrapped in `verus!` block
- GPU annotations moved to comments
- Local arrays: `Vec<u32>` via `generic_zero_vec`
- `vget`/`vset`/`vslice` helpers for u32-indexed access
- `_buf` function calls for shared memory operations
- Loop invariants (currently vacuous pending comprehensive requires)
- Post-loop assertion for valid pixel state

### verus-gpu-parser/src/{parse,emit,types}.rs
- Comment-based GPU annotation parsing
- `#[gpu_local(N)]`, `#[gpu_skip]`, `#[gpu_shared(SIZE)]`
- `local_invocation_id`, `workgroup_id`, `num_workgroups` builtins
- `__local_N`/`__klocal_N`/`__kscalar` buffer name conventions
- Unused buffer declaration elimination
- Mixed storage monomorphization (shared + local + storage)

### mandelbrot-profiler/
- Standalone wgpu profiler crate
- GPU timestamp queries, parameter sweeps, CSV output
- Headless (no browser needed)

### verus-mandelbrot/web/
- `mandelbrot_perturbation.wgsl`: 1087 lines auto-transpiled
- BigInt center coordinates in JavaScript
- No scratch buffer (all local arrays)
