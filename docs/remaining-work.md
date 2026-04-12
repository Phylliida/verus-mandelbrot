# Remaining Verification Work: GPU Mandelbrot Kernel

**Status**: 2026-04-12 (updated 2026-04-12 session 2, items #1-#4 complete).

**Crate state**: verus-mandelbrot 90 verified in `gpu_perturbation_entry`, 336 in `gpu_perturbation_proofs`, 0 errors crate-wide (337 cached). verus-fixed-point 991 verified, 0 errors.

---

## What's Done (complete chain)

### Buffer-level correctness (unconditional)
- **perturbation_iteration_step** (Stage A/B): extracted helper with full value postcondition — the 19-op body provably computes `pert_step_buf_int` on its signed-int inputs. Uses 19 bridge lemma calls (`lemma_signed_{mul,add,sub}_postcond_to_buf`).
- **#78 loop invariants**: ghost `delta_re_int`/`delta_im_int` track `pert_step_buf_int` across perturbation loop iterations.

### Spec-level bridge (conditional on bounds)
- **Stage E (frac_limbs=0 + scaled)**: `lemma_pert_step_buf_matches_spec` and `lemma_pert_step_buf_matches_spec_scaled` — buffer step equals `spec_pert_step` when no overflow.
- **Stage F**: `spec_ref_orbit`, `spec_pert_orbit`, orbit Seq constructors, `lemma_spec_orbit_end_to_end_correct` — applies `theorem_perturbation_n_steps`.
- **Stage G**: `lemma_kernel_end_to_end_under_bounds` — conditional end-to-end: under `spec_orbit_bounded`, buffer matches spec AND `perturbation_step_correct` holds for all iterations.

### Glitch detection
- **Soundness**: `lemma_glitch_check_implies_is_glitch` — kernel check fires ⇒ `is_glitch(z, δ, T)` for T·|Z|² ≤ 64·P^(2(n-1)).
- **Completeness (conditional)**: `lemma_glitch_is_glitch_implies_check` — `is_glitch` + T·|Z|² ≥ 128·P^(2(n-1)) ⇒ kernel check fires.

### Reference orbit
- **Phase A**: `ref_step_buf_int` + `lemma_ref_step_buf_matches_spec` — standalone proof that the 9-op Karatsuba reference step matches `spec_ref_step` under bounds.
- **Phase B Stage 1+2**: `ref_orbit_iteration_step` with full value postcondition — split into 3 sub-helpers (Part A/B/C, 3 ops each) + chain lemma call. Proves output equals `ref_step_buf_int` on inputs.
- **Chain lemma**: `lemma_ref_orbit_chain` — chains all 9 bridge lemmas, wired into the main helper.

### Coloring / output
- RGB channel bounds, monotonicity, alpha-constant validity, bit-packing safety.
- tid row-major injectivity.
- escaped_iter semantic invariant.
- Vote scan count + best_idx correctness.
- Refinement loop termination post-condition.
- best_gx/gy overflow safety.

### Infrastructure
- `signed_sub_to` strengthened with 3-way difference equation.
- 3 pre-existing verus-fixed-point errors fixed.
- Transpiler slice-alias tracking bug fixed.
- Web demo WGSL regenerated.

---

## What Remains

### 1. ~~Reference orbit value postcondition (Phase B Stage 2)~~ ✅ DONE

Completed 2026-04-12. Split into 3 sub-helpers (Part A/B/C) with value equation postconditions + frame assertions. Main helper calls A→B→C + `lemma_ref_orbit_chain` in assert-by scope. 90 verified, 0 errors.

### 2. Ghost Z tracking in the reference orbit loop

**What**: Add ghost `z_re_int`/`z_im_int` loop invariants to the reference orbit `for` loop, analogous to #78's delta tracking in the perturbation loop.

**Depends on**: ~~#1~~ (done).

**How**: After each call to `ref_orbit_iteration_step`, in a proof block:
```rust
proof {
    let z_re_int_new = ref_step_buf_int(z_re_int, z_im_int, c_re_int, c_im_int, n, frac_limbs).0;
    let z_im_int_new = ref_step_buf_int(z_re_int, z_im_int, c_re_int, c_im_int, n, frac_limbs).1;
    // helper postcondition gives:
    // signed_val_of(wg_mem[zn..], new_re_s) == z_re_int_new
    z_re_int = z_re_int_new;
    z_im_int = z_im_int_new;
}
```

**Effort**: ~30 minutes once #1 is done (direct analog of #78).

### 3. ~~Perturbation-theory dynamics bounds~~ ✅ DONE

Completed 2026-04-12. Triangle inequality + escape bounds give r_u = 4, e_u = 1; 12·16+1 = 193 < 2³². `lemma_no_escape_end_to_end` composes with Stage G for full correctness.

### ~~3 (original)~~. Perturbation-theory dynamics bounds

**What**: Prove that `spec_orbit_bounded(z0, c_ref, d0, dc, r_u, e_u, n, frac_limbs, n_steps)` holds for realistic Mandelbrot parameters — i.e., that the spec perturbation orbit stays within the no-overflow regime throughout `max_iters` iterations.

**Why it matters**: This is the precondition for `lemma_kernel_end_to_end_under_bounds` (Stage G). Without it, the end-to-end correctness is conditional.

**Status**: This is genuine mathematical content, not verification infrastructure. The kernel's runtime glitch detection is the practical substitute — it handles the cases where the bound fails. Formally proving the bound requires reasoning about Mandelbrot escape dynamics (when does |δ_k| grow? how fast?).

**Approach options**:
- **Option A (cleanest)**: Prove that if the kernel's glitch check DIDN'T fire for iterations 0..k, then the buffer values at step k satisfy Stage E's overflow bound. This ties the runtime check to the formal guarantee: "non-glitched iterations are provably correct."
- **Option B (simpler)**: Prove the bound for a SPECIFIC regime (e.g., |Z| < 2, |δ| < 1, |Δc| < 0.001) that covers "typical deep zoom" use cases. This gives a conditional theorem with concrete constants.
- **Option C (weakest)**: Leave the bound as an external assumption. The rest of the chain is proven; the assumption is clearly documented.

**Key numbers** (for calibrating bounds):
- Stage E's overflow bound: `12·r_u² + e_u < limb_power(n - frac_limbs)`
- Reference step's overflow bound: `6·r_u² + r_u < limb_power(n)`
- Kernel's glitch threshold: `vec_val(δ) ≥ 4·limb_power(n-1)` i.e. `|δ_u| < 4·limb_power(n-1-frac_limbs)` (unscaled)
- Escape radius: |Z| ≤ 2 (real value), |Z_buf| ≤ 2·limb_power(frac_limbs)

**Effort**: 1-3 days depending on the approach.

### 4. ~~Reference orbit buffer↔spec bridge~~ ✅ DONE

Completed 2026-04-12. Scaled bridge + inductive orbit proof. `lemma_ref_orbit_buf_matches_spec` proves ghost z_int = spec_ref_orbit * pf for all non-escaped iterations.

### ~~4 (original)~~. Reference orbit buffer↔spec bridge

**What**: Prove that thread 0's reference orbit computation (in `wg_mem`) matches `spec_ref_orbit(z0, c_ref, k)` at every iteration k.

**Depends on**: #1 and #2.

**Approach**: Once #2's ghost Z tracking is in place, the loop invariant says `signed_val_of(wg_mem[zk..], sign) == z_re_int` where `z_re_int` was updated via `ref_step_buf_int`. Combined with the Phase A bridge `lemma_ref_step_buf_matches_spec_scaled`, this gives `z_re_int == spec_ref_step(prev_z, c_ref).re * pf` (under bounds). With Stage G's conditional correctness, the full chain is:

```
buffer ops → ref_step_buf_int (Phase B)
ref_step_buf_int → spec_ref_step (Phase A + scaling)
spec_ref_step → spec_ref_orbit (Stage F constructors)
spec_ref_orbit + spec_pert_orbit → perturbation_step_correct (Stage F + theorem)
```

**Effort**: ~1 day once #1-#2 are done.

### 5. WGSL transpilation semantics

**What**: Prove the emitted WGSL shader computes the same as the verified Rust code.

**Status**: The transpiler (`verus-gpu-parser`) handles function extraction and monomorphization correctly (including the slice-alias fix from this session). But the transpiler itself is NOT verified — its output is trusted.

**Approach**: The `verus-gpu-transpiler` crate has `wgsl_semantics.rs` and `emit_proof.rs` which define the formal WGSL semantics and a proof that the emitted WGSL matches the GPU IR. This is a separate verification project from the Mandelbrot kernel.

**Effort**: Large (multiple sessions).

### 6. GPU workgroup barrier memory model

**What**: `gpu_workgroup_barrier()` is `#[verifier::external_body]`. It models the GPU's workgroup-level synchronization: after the barrier, all threads see the writes that all other threads performed before the barrier.

**Status**: The kernel uses barriers between:
- Thread 0's reference orbit writes → all threads' perturbation reads
- All threads' glitch votes → thread 0's vote scan
- Thread 0's new ref_c writes → all threads' next-round perturbation

Without a formal memory model, we can't prove that thread 0's writes to `wg_mem` are visible to other threads.

**Approach**: Define a spec-level memory model with per-thread views and barrier-synchronized merges. This is a research-level task.

**Effort**: Large (research-level).

---

## Priority Order

1. ~~**#1 (ref orbit value postcondition)**~~ ✅ DONE.
2. ~~**#2 (ghost Z tracking)**~~ ✅ DONE.
3. ~~**#3 (dynamics bounds)**~~ ✅ DONE.
4. ~~**#4 (ref orbit buffer↔spec bridge)**~~ ✅ DONE.
5. **#5 and #6** — research-level, not blocking any kernel-level guarantees.

After #1-#4, the kernel has: "for every non-glitched iteration, the buffer state equals the scaled spec orbit value, and `perturbation_step_correct` holds." That's the strongest statement possible without modeling the GPU memory semantics (#6).
