# Session Summary: Full Verification + Transpiler + Exec-to-Spec Chain (2026-04-07b)

## Goal
Complete the GPU Mandelbrot perturbation kernel verification (0 errors), fix the transpiler to produce valid WGSL from the verified kernel inside `verus!{}`, add exec-to-spec bridge lemmas, and plan the remaining exec-to-spec connection work.

## What We Accomplished

### 1. GPU Kernel Fully Verified: 27 verified, 4 errors → 43 verified, 0 errors

**No `external_body`, no `admit`, no trusted code** (except `gpu_workgroup_barrier` which is a GPU primitive).

#### New proof lemmas:
- `lemma_orbit_access_safe`: proves `(iter+1)*z_stride < 8192` for orbit slot access
- `lemma_colorize_safe`: proves `escaped_iter * 255 / max_iters ≤ 254` and `half_t ≤ 127` for `255 - half_t` safety

#### Comprehensive shared memory layout invariants:
- All 9 offset relationships (`t0_im2 == t0_re2 + n`, ..., `ref_escape_addr == t0_re2 + 10*n`) propagated through outer while loop AND ref orbit for loop
- `t0_re2 == (max_iters+2)*z_stride` for orbit-to-temp non-overlap
- Explicit non-overlap proof for `signed_add_to_buf(... zn ..., t0_stmp1 ..., t0_stmp2 ...)`: proved `zn + z_stride < t0_re2` via `(iter+2)*z_stride ≤ (max_iters+1)*z_stride < (max_iters+2)*z_stride = t0_re2`

#### Runtime sign validation (defensive, no assumes):
- Reference orbit signs (`zk_re_s`, `zk_im_s`): validated before use, break as glitch if > 1
- Reference point signs (`ref_c_re_s`, `ref_c_im_s`): validated before orbit loop, skip orbit if invalid
- Perturbation orbit signs (`zn_re_s`, `zn_im_s`): validated before use, break as glitch if > 1
- c_data signs (`cre_s`, `cim_s`, `refre_s`, `refim_s`): validated before perturbation, skip if invalid
- All sign validation uses `if sign > 1u32 { treat_as_glitch/skip }` pattern — no content invariants needed

#### Invariant simplifications:
- `wg_mem@.len() >= 8192` instead of `wg_mem@.len() == old(wg_mem)@.len()` — avoids long equality chains through 30+ buffer modifications
- Weakened post-loop assertion to `assert(escaped_iter <= max_iters)` — the original `escaped_iter < max_iters || is_glitched == 1` was too strong (excluded valid "completed all iterations" case)

#### Key Verus patterns used:
- Extract nonlinear arithmetic into `proof fn` lemmas called from `proof { }` blocks
- Ghost variables not needed — all bounds carried as loop invariants on u32 let bindings
- `as int` in invariants needs explicit parenthesization: `(x as int) + (y as int)` not `x as int + y as int`
- `invariant_except_break` for while loops (tree-sitter-verus grammar needed fix for this)

#### Bugs found by formal verification:
- lprod buffer half the required size (`n` → `2*n`)
- Border workgroup out-of-bounds for edge workgroups
- Reference orbit escape without glitch flag

### 2. Transpiler: Verified Kernel → Valid WGSL

Made the transpiler handle kernels written inside `verus!{}` with full verification annotations.

#### Root causes found and fixed:

**tree-sitter-verus grammar** (grammar.js):
- `invariant_clause` only matched `'invariant'`, not `'invariant_except_break'`
- Fix: `choice('invariant', 'invariant_except_break')` in the while_expression rule

**parse_expr_stmt** (parse.rs):
- `while_expression` not handled as a child of `expression_statement`
- Tree-sitter wraps `while` in `expression_statement` nodes; the parser only handled `if_expression` and `for_expression` there
- Fix: add `"while_expression" => return parse_while(&child, ctx)`

**Source preprocessor** (parse.rs → `preprocess_verus_source`):
- Strips proof/spec fn declarations (they break verus block parsing due to `assert by(nonlinear_arith) requires`)
- Strips `#[inline]` and `#[verifier::external_body]` function definitions (transparent helpers)
- Strips `as usize` casts (WGSL uses u32 directly)
- Converts `&Vec<u32>` → `&[u32]`, `&mut Vec<u32>` → `&mut [u32]`
- Uncomments `// #[gpu_...]` → `#[gpu_...]`
- Keeps `verus!{}` wrapper (tree-sitter-verus needs it for proper parsing context)
- Keeps exec fn definitions like `copy_limbs` (they're called by the kernel)

**vget/vset/vslice transparent parsing** (parse.rs):
- `vget(v, i)` → `ArrayRead(buf, i)` for storage/shared buffers, `VecIndex(var, i)` for local arrays
- `vset(v, i, val)` → `BufWrite` for buffers, `ScratchWrite` for local arrays
- `vslice(v, off)` → `BufSlice(buf, off)` for buffers, `Var + off` for local arrays

**Param type detection** (parse.rs → `parse_typed_parameters`):
- Added `&[T]` and `&mut [T]` as `ParamType::VecU32` (not just `Vec<T>`)

**Monomorphization buffer arg matching** (parse.rs):
- `scan_expr_for_mappings`: match args to params positionally (not by filter order)
- Thread `var_names` and `local_arrays` through for `Var(id)` → buffer name resolution
- `Var(delta_re)` → look up in `local_arrays` → `__local_4`

**Shared memory arg emission** (emit.rs):
- When a Vec arg is a shared memory buffer (binding >= 1000), replace with `0u` (base offset) instead of passing the array
- Applied to both `Expr::Call` and `Stmt::CallStmt` handlers

**Dead code filtering** (emit.rs):
- Unused helper functions (like `generic_zero_vec_scratch`) filtered by transitive call reachability from kernel body

**Method call transparency** (parse.rs):
- `as_slice()`, `clone_limb()`, `clone()` → return receiver unchanged (identity methods)

#### Result:
- 1153 lines WGSL, 39 loops, 4 buffer bindings
- Passes `naga` validation (structural + type checking)
- Deployed to web viewer at `verus-mandelbrot/web/`

### 3. Exec-to-Spec Bridge Lemmas: 63 verified, 0 errors

Added bridge lemmas connecting exec fixed-point arithmetic to mathematical spec:

- `bridge_complex_square_error(re, im, scale)`: re error ≤ 1 ULP, im error ≤ 2 ULPs
- `bridge_complex_mul_error(a_re, a_im, b_re, b_im, scale)`: re ≤ 1, im ≤ 2 ULPs
- `bridge_perturbation_step_error(z_re, z_im, d_re, d_im, scale)`: component errors bounded independently
- `bridge_n_step_accumulated_error(n)`: N iterations → N*(2,4) ULP total
- `bridge_escape_detection_sound(computed_mag, true_mag, threshold, n_iters)`: escape correct to ~26 decimal digits

These bridge lemmas call the existing standalone theorems (`theorem_complex_square_error`, etc.) and repackage them in a form suitable for the exec-to-spec connection.

## Current Verification Status

| Component | Status | Count |
|-----------|--------|-------|
| verus-fixed-point limb_ops | ✅ Fully verified | 966 verified, 0 errors |
| gpu_perturbation_entry.rs | ✅ Fully verified | 43 verified, 0 errors |
| gpu_mandelbrot_kernel.rs | ✅ Fully verified | 63 verified, 0 errors |
| **Total** | | **1072 verified, 0 errors** |

## What's Proved vs What's Not

### Fully Proved (zero trust)
- Every buffer access in bounds
- Every u32 operation overflow-free
- Loop termination
- Perturbation formula algebraically correct (over abstract Ring)
- Per-operation truncation error bounded
- N-step error accumulation bounded
- Escape detection correct within tolerance

### NOT Proved (gaps in the chain)
1. **Exec functions lack spec-connection postconditions**: `complex_square`, `complex_mul`, `perturbation_step` only ensure format correctness, not spec equivalence with error bound
2. **No error accumulation invariant in kernel loop**: the perturbation while loop doesn't track `|computed - exact| ≤ iter * K`
3. **signed_val² == unsigned_val² not proved**: needed to connect unsigned truncation theorems to signed spec functions
4. **signed_add no-wrapping for bounded inputs not proved**: needed to eliminate the disjunctive modular postcondition
5. **Escape detection not connected to kernel**: `theorem_escape_with_tolerance` exists but isn't invoked from the kernel's escape check code

## Remaining Work: Exec-to-Spec Connection

### Task Dependency Chain

```
#60 signed_val² == unsigned_val²  ─┐
                                   ├→ #57 complex_square ensures ─┐
#61 signed_add no-wrapping ────────┤                              ├→ #59 perturbation_step ensures
                                   └→ #58 complex_mul ensures ───┘           │
                                                                             ▼
                                                                  #62 kernel loop error invariant
                                                                             │
                                                                             ▼
                                                                  #63 escape detection end-to-end
```

### Task Details

**#60: Prove signed_val² == unsigned_val²** (foundation, no blockers)
- Lemma: `x.signed_val() * x.signed_val() == x.unsigned_val() * x.unsigned_val()`
- Proof: `signed_val = if sign==0 { uval } else { -uval }`. Either way, `sv² = uval²`.
- Location: `verus-fixed-point/src/runtime_fixed_point.rs`
- Difficulty: Low

**#61: Prove signed_add no-wrapping for bounded inputs** (foundation, no blockers)
- Lemma: if `|a.sv| + |b.sv| < P/2` then `signed_add(a,b).sv == a.sv + b.sv` (exact)
- This eliminates the 3-way disjunctive postcondition for bounded inputs
- Location: `verus-fixed-point/src/runtime_fixed_point.rs`
- Difficulty: Medium — need to reason about the select_limb branching in signed_add

**#57: Add spec-connection ensures to complex_square** (blocked by #60, #61)
- Postcondition: `out.to_spec().re ∈ [spec_re/S, spec_re/S + 1]` where `spec_re = z.re.sv² - z.im.sv²`, `S = limb_power(frac_limbs)`
- Uses #60 to connect `unsigned_val²` in truncation theorem to `signed_val²` in spec
- Uses #61 to prove `signed_sub(re2, im2)` gives exact difference (re2, im2 are positive)
- Location: `verus-mandelbrot/src/gpu_mandelbrot_kernel.rs`
- Difficulty: Medium-High — chain through 3 multiplications + 3 subtractions

**#58: Add spec-connection ensures to complex_mul** (blocked by #60, #61)
- Same structure as #57 but for multiplication
- Location: `verus-mandelbrot/src/gpu_mandelbrot_kernel.rs`
- Difficulty: Medium-High

**#59: Add spec-connection ensures to perturbation_step** (blocked by #57, #58)
- Postcondition: `out.to_spec() ≈ spec_pert_step(z.to_spec(), delta.to_spec(), dc.to_spec())` with error ≤ (2, 4) ULPs
- Chains through complex_mul (for 2Zδ) and complex_square (for δ²) postconditions
- Location: `verus-mandelbrot/src/gpu_mandelbrot_kernel.rs`
- Difficulty: High — combines multiple operations

**#62: Add error accumulation invariant to kernel loop** (blocked by #59)
- Ghost variable `ghost_error_re: int`, `ghost_error_im: int` in perturbation while loop
- Invariant: `ghost_error_re <= iter * 2, ghost_error_im <= iter * 4`
- Each iteration calls perturbation_step and adds its error to the accumulator
- Location: `verus-mandelbrot/src/gpu_perturbation_entry.rs`
- Difficulty: High — the kernel uses `_buf` functions directly, not `FpComplex` wrappers. Need to bridge between buffer-based ops and `FpComplex.to_spec()`.

**#63: Prove escape detection end-to-end** (blocked by #62)
- After the perturbation loop: `|computed_mag - true_mag| ≤ accumulated_error`
- Invoke `theorem_escape_with_tolerance` with the accumulated error bound
- Prove: `borrow == 0` at the kernel's `sub_limbs_to` call implies `true |Z+δ|² ≥ threshold - error`
- Location: `verus-mandelbrot/src/gpu_perturbation_entry.rs`
- Difficulty: Medium — just connecting existing theorems

### Key Technical Challenges

**Challenge 1: Buffer-based ops vs FpComplex**
The kernel uses `signed_mul_to_buf(&ref_a, &sign, &ref_b, &sign, wg_mem, offset, ...)` but the spec functions use `FpComplex<T>` with `to_spec()`. Need a bridge that interprets buffer regions as fixed-point values and connects to the spec.

Possible approach: ghost spec function `wg_mem_to_spec(wg_mem@, offset, n, frac_limbs) → SpecComplex` that reads a complex value from shared memory at the given offset. Then prove that after `signed_mul_to_buf`, the output region satisfies the truncation error bound.

**Challenge 2: Sign-magnitude ↔ signed value**
The truncation theorems work on unsigned magnitudes (≥ 0). The spec uses signed values. Need to prove:
- `trunc(|a|²/S) == trunc(a²/S)` (squaring removes sign)
- `|trunc(a*b/S) * sign_xor - exact/S| ≤ 1` (signed truncation error)

**Challenge 3: Modular wrapping**
`signed_add` gives `a + b (mod P)` with 3-way disjunction. For bounded inputs, only one branch is taken. Need to prove the bounds hold throughout the iteration:
- Reference orbit: `|Z| < escape_radius ≈ 4` (otherwise escaped)
- Perturbation: `|δ| < escape_radius` (otherwise glitched)
- These give `unsigned_val < 8 * scale`, so `|sv| < 8 * scale << P/2`

## Files Modified This Session

### verus-mandelbrot/src/gpu_perturbation_entry.rs
- Added `lemma_orbit_access_safe`, `lemma_colorize_safe`
- Added comprehensive layout invariants (offset relationships, c_data bounds)
- Added runtime sign validation guards
- Simplified wg_mem length tracking
- Fixed post-loop assertion
- **43 verified, 0 errors**

### verus-mandelbrot/src/gpu_mandelbrot_kernel.rs
- Added 5 bridge lemmas (`bridge_complex_square_error`, etc.)
- **63 verified, 0 errors**

### tree-sitter-verus/grammar.js
- Added `invariant_except_break` to `invariant_clause` rule

### verus-gpu-parser/src/parse.rs
- Added `preprocess_verus_source` for verus!{} kernel preprocessing
- Added vget/vset/vslice transparent parsing
- Fixed `parse_expr_stmt` to handle `while_expression`
- Fixed param type detection for `&[T]` and `&mut [T]`
- Fixed monomorphization positional matching
- Threaded `var_names` and `local_arrays` through call mapping
- Added `as_slice`/`clone_limb` as transparent identity methods
- Added `attribute_item` handling for gpu_local/gpu_skip

### verus-gpu-parser/src/emit.rs
- Added shared memory arg replacement (`wg_mem` → `0u` offset)
- Added dead function filtering by transitive reachability
- Fixed ArrayRead for buffer vget

### verus-mandelbrot/web/mandelbrot_perturbation.wgsl
- Regenerated from verified kernel, passes naga validation
- 1153 lines, 39 loops, 4 buffer bindings
