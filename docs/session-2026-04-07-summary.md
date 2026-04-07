# Session Summary: Full GPU Kernel Verification (2026-04-07)

## Goal
Make the GPU Mandelbrot perturbation kernel fully verified by Verus — no `external_body`, no `admit`, no trusted code. Every u32 overflow, buffer access, and loop invariant formally proved.

## What We Accomplished

### Task 1: Verify `_buf` function bodies (COMPLETE)
**verus-fixed-point: 966 verified, 0 errors**

Removed `#[verifier::external_body]` from `signed_add_to_buf`, `signed_sub_to_buf`, `signed_mul_to_buf` and fully verified their implementations.

Key changes:
- **Frame postconditions** added to `add_limbs_to`, `sub_limbs_to`, `mul_schoolbook_to` — "indices outside the written region are unchanged"
- **Valid limbs postconditions** added to `mul_schoolbook_to` — output has valid limbs
- **Non-overlap preconditions** on all `_buf` functions — `out_off`, `tmp1_off`, `tmp2_off` regions must not overlap
- **Valid limbs + frame ensures** on all `_buf` functions
- **mul2 rlimit fix** — split nonlinear_arith proof into two steps to stay within rlimit after added module complexity

### Task 2: Non-vacuous kernel invariants (IN PROGRESS — 27 verified, 4 errors)
**Removed `external_body` from the 759-line GPU kernel function.** No trusted code remains.

Key structural changes:
- **Fixed lprod size bug**: `generic_zero_vec(n)` → `generic_zero_vec(2*n)` — formal verification caught a real bug where the product buffer was half the required size
- **Fixed aliasing**: Reference orbit now uses `copy_limbs` helper to copy data from `wg_mem` to local temps before calling `_buf` functions, avoiding `&[T]` + `&mut Vec<T>` aliasing
- **Fixed border workgroup bug**: Added bounds clamping for `best_gx`/`best_gy` — formal verification caught a real out-of-bounds access for edge workgroups
- **Converted for-break loops to while loops**: Verus `for` loops don't support `break` well (iterator ghost invariant fails); `while` loops with `decreases` work correctly
- **Added `invariant_except_break`** for the outer refinement loop

#### Overflow proof infrastructure:
- `lemma_mul_u32_safe`: proves `a*b < 2^32` for bounded inputs
- `lemma_tid_safe`: proves `gy*w + gx < 2^32` and `< w*h` with tight bounds
- `lemma_tid_cstride_safe`: proves `tid*cs < u32_max` given `tid < w*h`
- `lemma_cdata_offset_safe`: proves `tid*cs + cs <= cdata_len` for buffer access
- `lemma_iter_stride_safe`: proves `iter*stride < max*stride` for orbit loop
- Shared memory layout chain: 10-addition chain through `t0_re2..t0_stmp3` → `ref_escape_addr` → `best_ref_addr < 8192` proved via int arithmetic

#### Comprehensive requires on the kernel:
- Param bounds: width/height ≤ 65535, max_iters ≤ 4096, n ∈ [1,8], frac_limbs ≤ n
- Thread coords: lid_x/y < 16, gid_x/y ≤ 65535, gid ≥ lid
- Shared memory layout: `(max_iters+2)*(2n+2) + 10n + 259 ≤ 8192`
- c_data: `len ≥ w*h*(2n+2)`, `w*h*(2n+2) < u32_max`
- iter_counts: `len ≥ w*h`, `w*h < u32_max`
- Escape threshold: `params.len ≥ 5 + n`

#### What remains (4 errors):
1. **Orbit data access bounds** (ref orbit loop): `copy_limbs(wg_mem, zk_re, ...)` needs `zk_re + n ≤ wg_mem.len()` — provable from stride invariant but Z3 needs the chain `zk + n < zk + z_stride ≤ (max_iters+1)*z_stride < 8192`
2. **c_data access bounds** (perturbation Δc): `vslice(c_data, c_re_off)` needs `c_re_off ≤ c_data.len()` — provable from `lemma_cdata_offset_safe` but the perturbation loop invariant doesn't carry the bound
3. **Perturbation orbit access**: `vslice(wg_mem, zn_re)` needs `zn_re ≤ wg_mem.len()` — same as #1 but in the perturbation loop
4. **Colorize underflow**: `255 - half_t` needs `half_t ≤ 127` — provable from `t_col < 255` but Z3 needs nonlinear division help

### Foundation work completed for tasks 3-4:
- `signed_add_to` / `signed_sub_to` / `signed_mul_to`: relaxed `a@.len() == n` to `>= n` (needed for `vslice` compatibility)
- `signed_add_to` / `signed_sub_to` / `signed_mul_to`: added `valid_limbs` postconditions on output
- `slice_vec_to`: added values-match + frame postconditions
- `copy_limbs`: new verified helper for copying data between buffers

## Bugs Found by Formal Verification

1. **lprod size bug**: Product buffer was `generic_zero_vec(n)` but `signed_mul_to` requires `prod.len() ≥ 2*n`. With n=4, lprod had 4 elements but needed 8. The GPU annotation `#[gpu_local(8)]` masked this in transpiled code.

2. **Border workgroup out-of-bounds**: `best_gx = gid_x - lid_x + best_idx%16` can exceed `width` for workgroups at the grid edge. The code accessed `c_data[best_tid * c_stride_px]` with an invalid `best_tid`. Fixed by adding bounds clamping.

3. **Reference orbit escape without glitch flag** (from previous session): `break` on reference orbit escape left `is_glitched==0` and `escaped_iter==max_iters` — an invalid state. This is the bug the post-loop assertion `assert(escaped_iter < max_iters || is_glitched == 1u32)` is designed to catch non-vacuously.

## Key Verus Lessons Learned

### Parser quirks (Verus version-specific)
- **`assert by(nonlinear_arith) requires`** only works inside `proof { }` blocks, NOT in exec mode
- **`as int` in invariant clauses** can confuse the parser — use explicit parenthesization: `(x as int) * (y as int)` not `x as int * y as int`
- **Hex literals** (`0xFFFF_FFFF`) in invariant/requires contexts may be parsed as u32 instead of int — use spec helper functions like `u32_max()` or decimal literals
- **`invariant_except_break`** works for `while` loops but NOT for `for` loops
- **`for` loops with `break`** fail with "For-loop iterator invariant failed" — convert to `while` loops with `decreases` instead

### Overflow proof strategy
- Extract nonlinear arithmetic into **separate `proof fn` lemmas** — avoids all parser issues
- Call lemmas from `proof { lemma_name(...); }` blocks in exec code
- For **shared memory layout chains** (10+ chained additions), assert intermediate equalities in int arithmetic: `assert(t0_prod as int == (t0_tmp_base as int) + 5 * (n as int))`
- The **layout constraint** `(max_iters+2)*(2n+2) + 10n + 259 ≤ 8192` is the single source of truth for all shared memory bounds

### Verification architecture
- **Frame postconditions** are essential for single-buffer operations — without "writes to region A don't affect region B", Z3 can't chain operations
- **valid_limbs propagation** through loop invariants is the key to non-vacuous verification — every `signed_mul_to`/`signed_add_to` call needs its inputs to have valid limbs
- **Ghost variables** (`let ghost wh_cs_bound = ...`) are useful for carrying computed bounds through loop invariants when the direct expressions cause parser issues

## Files Modified

### verus-fixed-point/src/fixed_point/limb_ops.rs
- Frame postconditions on `add_limbs_to`, `sub_limbs_to`, `mul_schoolbook_to`, `slice_vec_to`
- Valid limbs postconditions on `mul_schoolbook_to`, `signed_add_to`, `signed_sub_to`, `signed_mul_to`
- Values-match postcondition on `slice_vec_to`
- Relaxed `a@.len() == n` to `>= n` on `signed_add_to`, `signed_sub_to`, `signed_mul_to`
- Removed `external_body` from `signed_add_to_buf`, `signed_sub_to_buf`, `signed_mul_to_buf`
- Added non-overlap requires + valid_limbs/frame ensures to `_buf` functions
- Fixed `mul2` rlimit by splitting nonlinear_arith

### verus-mandelbrot/src/gpu_perturbation_entry.rs
- Removed `#[verifier::external_body]` from kernel function
- Added `copy_limbs` helper function (verified)
- Added `ref_a`, `ref_b` local arrays for reference orbit aliasing fix
- Fixed `lprod` size: `n` → `2*n`
- Added bounds clamping for `best_gx`/`best_gy`
- Converted `for`-break loops to `while` loops with `decreases`
- Added 6 overflow proof lemmas
- Added comprehensive `requires` clause
- Added outer loop invariants (40+ clauses)
- Added perturbation loop invariants (30+ clauses)
- Added orbit inner loop invariants
- Added shared memory layout chain proof

## Remaining Work

### To finish Task 2 (4 errors remaining):
1. Add orbit access bounds to reference orbit + perturbation loop invariants
2. Add c_data offset bounds to perturbation invariant
3. Fix colorize division/subtraction overflow proof
4. These are all the same pattern — adding the right bounds to the right loop invariants

### Task 3: Transpiler compatibility (NOT STARTED)
- Update `verus-gpu-parser` to recognize `vget`/`vset`/`vslice` as transparent helpers
- Handle `copy_limbs` in WGSL emission
- Handle `while` loops (converted from `for` loops with break)
- Handle `_buf` function call patterns

### Task 4: Complex exec-to-spec chain (NOT STARTED)
- Foundation work done (valid_limbs postconditions)
- Need: bounded-input requires on `complex_square`/`complex_mul`
- Chain: bounded inputs → exact add/sub → truncated mul → complex operation error → perturbation step error
