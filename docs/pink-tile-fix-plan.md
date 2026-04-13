# Pink Tile Fix: Direct Computation Fallback — IMPLEMENTED

## Bug
Entire 16x16 workgroup tiles appear solid pink at the Mandelbrot boundary.
Increasing max_rounds doesn't help — the tiles persist.

## Status: COMPLETE
Implemented in commit 192b9fe. Verified: 100 functions, 0 errors. WGSL regenerated.

## Root Cause
When ALL pixels in a workgroup glitch early, the refinement loop picks a
local pixel as the new reference. But that pixel also glitches quickly,
so the cycle repeats for all rounds without resolving. Unresolved pixels
get `escaped_iter == max_iters` and are colored with t_col=255 → pink.

## Fix: Direct Computation Fallback
After all refinement rounds, any pixel with `is_glitched == 1` and
`escaped_iter == max_iters` should fall back to direct (non-perturbation)
Mandelbrot iteration: Z_{k+1} = Z_k^2 + c_pixel (no reference orbit).

This is slower (no perturbation speedup) but always correct. Production
viewers (Kalles Fraktaler, etc.) do this as their final fallback.

## Implementation

### Location
After the refinement while loop ends (line ~3230), before the coloring code:

```rust
// Fallback: direct computation for unresolved glitched pixels
if is_glitched == 1u32 && escaped_iter == max_iters {
    // Direct iteration: Z_{k+1} = Z_k^2 + c_pixel
    // Use the same fixed-point arithmetic but with c_pixel directly
    // (no perturbation, no reference orbit)
    
    // Zero Z_0
    for i in 0..n { ref_a[i] = 0; ref_b[i] = 0; }
    let mut z_re_s = 0u32;
    let mut z_im_s = 0u32;
    
    // Read c_pixel from c_data
    // c_re at c_data[c_re_off..c_re_off+n], sign at c_data[c_re_sign_off]
    // c_im at c_data[c_im_off..c_im_off+n], sign at c_data[c_im_sign_off]
    
    for iter in 0..max_iters {
        // Z_{k+1} = Z_k^2 + c_pixel
        // Use ref_orbit_iteration_step or inline the Karatsuba squaring
        // with c_pixel instead of c_ref
        
        // Escape check: |Z|^2 >= 4
        // If escaped, set escaped_iter = iter and break
    }
}
```

### Key Considerations
1. The direct computation uses the SAME fixed-point arithmetic (already verified)
2. c_pixel is read from c_data (same buffer, same offset as Δc computation)
3. The escape check is the same as the reference orbit's
4. No shared memory needed — all computation is thread-local
5. This code only runs for pixels that failed ALL refinement rounds

### Verification
- The direct computation follows the same `ref_step_buf_int` pattern
- Escape check correctness already proved
- No new shared memory writes → no race conditions
- The fallback is purely local (no barriers needed)

### Files to Modify
- `gpu_perturbation_entry.rs`: Add fallback after refinement loop
- `gpu_perturbation_proofs.rs`: Prove fallback correctness (same chain)
- Regenerate WGSL after changes
