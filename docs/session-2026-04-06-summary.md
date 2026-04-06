# Session Summary: Verified Mandelbrot on GPU — 2026-04-06

## What We Built

Starting from `RuntimePrimeField<u32>` (914 verified), we built a complete pipeline:
**Verified Verus arithmetic → auto-transpiled WGSL → WebGPU Mandelbrot in browser.**

### Final Architecture

```
verus-fixed-point (944 verified, 0 errors)
  ├── LimbOps trait: add3, sub_borrow, mul2, select_limb, is_zero_limb, or_limb
  ├── Multi-limb ops: add_limbs_to, sub_limbs_to, mul_schoolbook_to, slice_vec_to
  ├── Signed ops: signed_add_to, signed_sub_to, signed_mul_to
  ├── GenericFixedPoint<T>: sign as T limb, branchless select
  └── All for loops (no while — GPU compatible)
       ↓
verus-gpu-parser (transpiler)
  ├── Import resolution: use → Cargo.toml → source files
  ├── Reachability walk from #[gpu_kernel]
  ├── Buffer monomorphization: per-call-site dispatch
  ├── Call rewriting: Phase 10 resolves each Call to correct variant
  ├── Recursion unrolling: #[gpu_base_case] annotation
  ├── Vec operations: .set() → buffer write, no Vec::new allowed
  ├── Trait methods: self→self_val, *deref→identity, &ref→stripped
  ├── if-as-value → select(), tuple returns → struct R2{f0,f1}
  └── WGSL reserved word sanitization
       ↓
verus-mandelbrot
  ├── gpu_mandelbrot_kernel.rs: 7 verified complex arithmetic functions
  │   complex_square, complex_mul, complex_add, complex_double,
  │   magnitude_squared, ref_orbit_step, perturbation_step
  ├── gpu_mandelbrot_entry.rs: transpiler entry with #[gpu_kernel]
  └── web/: HTML + JS + auto-generated WGSL (539 lines)
       ↓
  Browser: WebGPU compute shader → canvas → Mandelbrot set ✓
```

## Key Design Decisions

### 1. Fixed-Point Instead of Prime Field
Originally planned prime field (mod p) arithmetic for GPU. Realized that with
bounds constraints (values never overflow), modular reduction is unnecessary.
Switched to sign-magnitude fixed-point: simpler, faster, no Mersenne reduction.

### 2. Output Parameters Instead of Vec::new
GPU has no dynamic allocation. Converted from `fn f(a, b) -> Vec<T>` to
`fn f(a, b, out: &mut Vec<T>)`. The caller provides the output buffer.
Key functions: `add_limbs_to`, `sub_limbs_to`, `mul_schoolbook_to`,
`signed_add_to`, `signed_sub_to`, `signed_mul_to`.

### 3. Sign as T Limb, Not bool
For GPU compatibility, the sign field is `T` (0 or 1) not `bool`.
All sign operations use `select_limb` — fully branchless, no bool→T conversion.

### 4. Per-Call-Site Buffer Monomorphization
Each unique `(function, buffer_combination)` at a call site generates a separate
WGSL function. Example: `sub_limbs_to` called with `(scratch,scratch,scratch)` AND
`(scratch,params,scratch)` produces two variants. Call rewriting (Phase 10) ensures
each Call points to the correct variant based on its actual buffer arguments.

### 5. #[gpu_base_case] Annotation for Recursion
`generic_mul_karatsuba` is recursive. The transpiler unrolls it into depth-stratified
copies (d0 through d6). The `#[gpu_base_case(generic_mul_schoolbook)]` annotation
tells the transpiler what to call at depth 0 instead of self-recursion.

## Bugs Found and Fixed

### Critical: select_limb Arguments Swapped in signed_add
**Bug**: `select_limb(same_sign, sum, diff)` was backwards — when `same_sign=1`
(signs match), it returned `diff` instead of `sum`.

**Impact**: `0 + (-0.5)` returned `+0.5` instead of `-0.5`. Every negative c value
was inverted, producing garbage fractals.

**Root cause**: `select_limb(cond, if_zero, if_nonzero)` — the convention is
`cond=0→if_zero, cond=1→if_nonzero`. The code had the args in the wrong order
for the `same_sign` selector.

**Affected**: `GenericFixedPoint::signed_add`, `signed_add_to`, `signed_lt_indicator`.

**How proof should have caught it**: The postcondition only stated structural
properties (`wf_spec`, format preservation), not semantic correctness. Adding:
```
ensures out.signed_val() == self.signed_val() + other.signed_val()
```
would have immediately caught the swap because the wrong branch produces
`a - b` instead of `a + b`.

### Buffer Monomorphization: Wrong Variant at Call Sites
**Bug**: The escape check called `sub_limbs_to_c_data_scratch_scratch` (reading
threshold from c_data buffer) instead of `sub_limbs_to_scratch_params_scratch`.

**Root cause**: The call rewriting used the kernel's `buf_decls` for ALL function
bodies. Functions inside the call chain need to use their OWN `vec_buffer_map`.

**Fix**: Phase 10 now builds `caller_bufs` from each function's `vec_buffer_map`,
not the kernel's global `buf_decls`.

### WGSL Compliance Issues (8 fixes)
1. `__ret` → `_ret` (double underscore forbidden)
2. `_` → `_unused_N` (bare underscore forbidden)
3. `self` → `self_val` (reserved keyword)
4. `target` → `target_v` (reserved keyword)
5. `_0`, `_1` → `f0`, `f1` (underscore-prefixed fields forbidden)
6. Parameter redefinition (skip var decl for params)
7. `_call_tmp` not declared (was in skip list)
8. `.set()` → buffer write (was parsed as function call)

## Verification Stats

| Component | Verified | Errors |
|-----------|----------|--------|
| verus-fixed-point | 944 | 0 |
| verus-mandelbrot (gpu_kernel) | 7 | 0 |
| **Total** | **951** | **0** |

New functions added this session:
- `is_zero_limb`, `or_limb` (LimbOps trait)
- `add_limbs_to`, `sub_limbs_to`, `select_vec_to`, `slice_vec_to`
- `mul_schoolbook_to`, `mul_to`
- `signed_add_to`, `signed_sub_to`, `signed_mul_to`
- `GenericFixedPoint`: `signed_add`, `signed_sub`, `signed_mul`, `neg`, `is_zero_indicator`, `unsigned_lt_indicator`, `signed_lt_indicator`
- `signed_val()` spec function

## What Remains

### 1. Semantic Postconditions (Priority: HIGH)
Add `ensures out.signed_val() == a + b` to `signed_add`, `signed_sub`, `signed_mul`.
This would have caught the select_limb swap bug. Requires:
- `signed_val()` spec function (already added)
- Proving the select logic produces the correct mathematical result
- Handling the modular case (when values overflow n limbs)
- Ideally: bounds preconditions that guarantee no overflow

### 2. In-Place Karatsuba (Priority: MEDIUM)
Currently `mul_to` delegates to the allocating `generic_mul_karatsuba` for n > 4,
then copies to output. A proper in-place Karatsuba with workspace management
would eliminate all Vec::new from the multiply path.

### 3. Perturbation Kernel (Priority: MEDIUM)
The `perturbation_step` is verified but not yet in the GPU entry point.
For deep zoom, need: reference orbit on GPU + per-pixel perturbation.

### 4. Color Palette (Priority: LOW)
Current coloring is a simple blue gradient. Could add smooth iteration count,
HSV palette, or distance estimation for better visuals.

### 5. Zoom/Pan in Browser (Priority: LOW)
Click-to-zoom is implemented but the N=4 precision limits zoom depth.
Need to test with higher N (8, 16, 32) and verify the slider works.

### 6. Transpiler Robustness (Priority: MEDIUM)
- Handle more Rust patterns (match expressions, closures, etc.)
- Better error messages when transpilation fails
- Validate generated WGSL before serving

### 7. Performance
- Profile GPU execution time vs hand-written shader
- Optimize schoolbook multiply (currently O(n²), could use Karatsuba on GPU
  via recursion unrolling)
- Workgroup shared memory for scratch instead of global storage

## Files Modified

### verus-fixed-point
- `src/fixed_point/limb_ops.rs`: +108 lines (output-param variants, signed ops, LimbOps additions)
- `src/runtime_fixed_point.rs`: +136 lines (GenericFixedPoint signed ops, sign as T)

### verus-gpu-parser
- `src/parse.rs`: Major rewrite (monomorphization, call rewriting, Vec handling)
- `src/emit.rs`: f0/f1 fields, _call_tmp, select_limb, recursion unrolling
- `src/imports.rs`: Attribute detection via tree-sitter sibling walking
- `src/types.rs`: ParamType, ReturnType, base_case field

### verus-mandelbrot
- `src/gpu_mandelbrot_kernel.rs`: Verified complex arithmetic (7 functions)
- `src/gpu_mandelbrot_entry.rs`: Transpiler entry with signed ops
- `web/index.html`, `web/mandelbrot.js`: WebGPU viewer
- `web/mandelbrot_verified.wgsl`: 539 lines auto-generated

### tree-sitter-verus
- `grammar.js`: function_item includes preceding attribute_items
