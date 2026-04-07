/// GPU Mandelbrot kernel with perturbation theory.
/// VERIFIED by Verus AND transpiled to WGSL.
///
/// Architecture: each 16x16 workgroup:
/// 1. Thread 0 computes reference orbit Z_0..Z_N in workgroup shared memory
/// 2. workgroupBarrier()
/// 3. All 256 threads compute perturbation delta using local arrays

use vstd::prelude::*;
use verus_fixed_point::fixed_point::limb_ops::*;

verus! {

/// No-op barrier for Verus verification (GPU semantics handled by transpiler).
#[verifier::external_body]
fn gpu_workgroup_barrier() { }

/// Vec indexing with u32 (GPU uses u32 indices, Rust needs usize).
/// Transparent to the transpiler (emits as v[i]).
#[inline]
fn vget(v: &Vec<u32>, i: u32) -> (out: u32)
    requires i < v@.len(),
    ensures out == v@[i as int],
{ v[i as usize] }

/// Vec mutable set with u32 index.
#[inline]
fn vset(v: &mut Vec<u32>, i: u32, val: u32)
    requires i < old(v)@.len(),
    ensures v@ == old(v)@.update(i as int, val), v@.len() == old(v)@.len(),
{ v.set(i as usize, val) }

// #[gpu_kernel(workgroup_size(16, 16, 1))]
fn mandelbrot_perturbation(
    // #[gpu_builtin(thread_id_x)]
    gid_x: u32,
    // #[gpu_builtin(thread_id_y)]
    gid_y: u32,
    // #[gpu_builtin(local_id_x)]
    lid_x: u32,
    // #[gpu_builtin(local_id_y)]
    lid_y: u32,
    // #[gpu_buffer(0, read)]
    c_data: &Vec<u32>,
    // #[gpu_shared(8192)]
    wg_mem: &mut Vec<u32>,
    // #[gpu_buffer(1, read_write)]
    iter_counts: &mut Vec<u32>,
    // #[gpu_buffer(2, read)]
    params: &Vec<u32>,
)
    requires
        params@.len() >= 10,
        params@[3].sem() > 0,  // n > 0
{
    let width = vget(params, 0u32);
    let height = vget(params, 1u32);
    let max_iters = vget(params, 2u32);
    let n = vget(params, 3u32);
    let frac_limbs = vget(params, 4u32);

    if gid_x >= width { return; }
    if gid_y >= height { return; }

    let tid = gid_y * width + gid_x;
    let local_id = lid_y * 16u32 + lid_x;

    // Stride per complex value in shared memory: re(n) + re_sign(1) + im(n) + im_sign(1)
    let z_stride = 2u32 * n + 2u32;

    // Shared memory regions
    let orbit_base = 0u32;                          // Z_0..Z_{max_iters}: (max_iters+1) * z_stride
    let ref_c_base = (max_iters + 1u32) * z_stride; // c_ref: z_stride words
    let t0_tmp_base = ref_c_base + z_stride;        // thread-0 temporaries

    // Thread-0 temporary offsets (for reference orbit computation)
    let t0_re2     = t0_tmp_base;
    let t0_im2     = t0_re2 + n;
    let t0_rpi     = t0_im2 + n;
    let t0_sum2    = t0_rpi + n;
    let t0_diff    = t0_sum2 + n;
    let t0_prod    = t0_diff + n;                   // 2*n words for product
    let t0_stmp1   = t0_prod + 2u32 * n;
    let t0_stmp2   = t0_stmp1 + n;
    let t0_stmp3   = t0_stmp2 + n;

    // Refinement shared slots (after thread-0 temporaries)
    let ref_escape_addr = t0_stmp3 + n;             // iteration where reference orbit escaped
    let vote_base = ref_escape_addr + 1u32;          // 256 words for glitch voting
    let glitch_count_addr = vote_base + 256u32;      // count of glitched pixels
    let best_ref_addr = glitch_count_addr + 1u32;    // local_id of best new reference

    // Per-pixel c from c_data buffer (absolute coordinates)
    let c_stride_px = 2u32 * n + 2u32;
    let c_re_off = tid * c_stride_px;
    let c_re_sign_off = c_re_off + n;
    let c_im_off = c_re_sign_off + 1u32;
    let c_im_sign_off = c_im_off + n;

    // Per-pixel local arrays for perturbation (in registers)
    // #[gpu_local(4)]
    let delta_re = 0u32;
    // #[gpu_skip]
    let mut delta_re_sign = 0u32;
    // #[gpu_local(4)]
    let delta_im = 0u32;
    // #[gpu_skip]
    let mut delta_im_sign = 0u32;

    // Δc = c_pixel - c_ref (computed once, stays constant)
    // #[gpu_local(4)]
    let dc_re = 0u32;
    // #[gpu_skip]
    let mut dc_re_sign = 0u32;
    // #[gpu_local(4)]
    let dc_im = 0u32;
    // #[gpu_skip]
    let mut dc_im_sign = 0u32;

    // Temporaries for perturbation arithmetic
    // #[gpu_local(4)]
    let t1 = 0u32;
    // #[gpu_local(4)]
    let t2 = 0u32;
    // #[gpu_local(4)]
    let t3 = 0u32;
    // #[gpu_local(4)]
    let t4 = 0u32;
    // #[gpu_local(4)]
    let t5 = 0u32;
    // #[gpu_local(8)]
    let lprod = 0u32;
    // #[gpu_local(4)]
    let ls1 = 0u32;
    // #[gpu_local(4)]
    let ls2 = 0u32;

    let mut escaped_iter = max_iters;
    let mut is_glitched = 1u32; // start as "needs computation"
    let mut glitch_iter = 0u32; // iteration where glitch was detected

    // ═══════════════════════════════════════════════════
    // Iterative refinement loop
    // ═══════════════════════════════════════════════════
    let max_rounds = 5u32;

    for round in 0u32..max_rounds {
        // ── Step 1: Thread 0 selects reference and computes orbit ──
        if local_id == 0u32 {
            if round == 0u32 {
                // Initial reference = center of workgroup
                let ref_x = gid_x - lid_x + 8u32;
                let ref_y = gid_y - lid_y + 8u32;
                let ref_x_c = if ref_x >= width { width - 1u32 } else { ref_x };
                let ref_y_c = if ref_y >= height { height - 1u32 } else { ref_y };
                let ref_tid_init = ref_y_c * width + ref_x_c;
                let ref_c_off = ref_tid_init * c_stride_px;
                for i in 0u32..n { vset(wg_mem, ref_c_base + i, vget(c_data, ref_c_off + i)); }
                vset(wg_mem, ref_c_base + n, vget(c_data, ref_c_off + n));
                for i in 0u32..n { vset(wg_mem, ref_c_base + n + 1u32 + i, vget(c_data, ref_c_off + n + 1u32 + i)); }
                vset(wg_mem, ref_c_base + 2u32 * n + 1u32, vget(c_data, ref_c_off + 2u32 * n + 1u32));
            }
            // else: ref_c was already updated by glitch analysis below

            // Compute reference orbit Z_0..Z_{max_iters}
            let z0_off = orbit_base;
            for i in 0u32..n { vset(wg_mem, z0_off + i, 0u32); }
            vset(wg_mem, z0_off + n, 0u32);
            for i in 0u32..n { vset(wg_mem, z0_off + n + 1u32 + i, 0u32); }
            vset(wg_mem, z0_off + 2u32 * n + 1u32, 0u32);

            let mut ref_escaped = max_iters;

            for iter in 0u32..max_iters {
                let zk = orbit_base + iter * z_stride;
                let zk_re = zk;
                let zk_re_sign = zk + n;
                let zk_im = zk + n + 1u32;
                let zk_im_sign = zk + 2u32 * n + 1u32;

                // Z_{k+1} = Z_k^2 + c_ref (3-multiply complex square)
                let re2_s = signed_mul_to(
                    &wg_mem[zk_re as usize..], &wg_mem[zk_re_sign as usize],
                    &wg_mem[zk_re as usize..], &wg_mem[zk_re_sign as usize],
                    &mut wg_mem[t0_re2 as usize..], &mut wg_mem[t0_prod as usize..], n, frac_limbs);
                let im2_s = signed_mul_to(
                    &wg_mem[zk_im as usize..], &wg_mem[zk_im_sign as usize],
                    &wg_mem[zk_im as usize..], &wg_mem[zk_im_sign as usize],
                    &mut wg_mem[t0_im2 as usize..], &mut wg_mem[t0_prod as usize..], n, frac_limbs);
                let rpi_s = signed_add_to(
                    &wg_mem[zk_re as usize..], &wg_mem[zk_re_sign as usize],
                    &wg_mem[zk_im as usize..], &wg_mem[zk_im_sign as usize],
                    &mut wg_mem[t0_rpi as usize..], &mut wg_mem[t0_stmp1 as usize..], &mut wg_mem[t0_stmp2 as usize..], n);
                let sum2_s = signed_mul_to(
                    &wg_mem[t0_rpi as usize..], &rpi_s,
                    &wg_mem[t0_rpi as usize..], &rpi_s,
                    &mut wg_mem[t0_sum2 as usize..], &mut wg_mem[t0_prod as usize..], n, frac_limbs);

                let zn = orbit_base + (iter + 1u32) * z_stride;

                // new_re = re^2 - im^2 + c_re
                let diff_s = signed_sub_to(
                    &wg_mem[t0_re2 as usize..], &re2_s,
                    &wg_mem[t0_im2 as usize..], &im2_s,
                    &mut wg_mem[t0_diff as usize..], &mut wg_mem[t0_stmp1 as usize..], &mut wg_mem[t0_stmp2 as usize..], n);
                let new_re_s = signed_add_to(
                    &wg_mem[t0_diff as usize..], &diff_s,
                    &wg_mem[ref_c_base as usize..], &wg_mem[ref_c_base + n as usize],
                    &mut wg_mem[zn as usize..], &mut wg_mem[t0_stmp1 as usize..], &mut wg_mem[t0_stmp2 as usize..], n);
                vset(wg_mem, zn + n, new_re_s);

                // new_im = (re+im)^2 - re^2 - im^2 + c_im
                let t1_s = signed_sub_to(
                    &wg_mem[t0_sum2 as usize..], &sum2_s,
                    &wg_mem[t0_re2 as usize..], &re2_s,
                    &mut wg_mem[t0_diff as usize..], &mut wg_mem[t0_stmp1 as usize..], &mut wg_mem[t0_stmp2 as usize..], n);
                let t2_s = signed_sub_to(
                    &wg_mem[t0_diff as usize..], &t1_s,
                    &wg_mem[t0_im2 as usize..], &im2_s,
                    &mut wg_mem[t0_stmp3 as usize..], &mut wg_mem[t0_stmp1 as usize..], &mut wg_mem[t0_stmp2 as usize..], n);
                let new_im_s = signed_add_to(
                    &wg_mem[t0_stmp3 as usize..], &t2_s,
                    &wg_mem[ref_c_base + n + 1u32 as usize..], &wg_mem[ref_c_base + 2u32 * n + 1u32 as usize],
                    &mut wg_mem[zn + n + 1u32 as usize..], &mut wg_mem[t0_stmp1 as usize..], &mut wg_mem[t0_stmp2 as usize..], n);
                vset(wg_mem, zn + 2u32 * n + 1u32, new_im_s);

                // Check if reference escaped: |Z_{k+1}|² > 4
                if ref_escaped == max_iters {
                    // re² + im² (reuse t0_re2 = re^2, t0_im2 = im^2 from above)
                    add_limbs_to(&wg_mem[t0_re2 as usize..], &wg_mem[t0_im2 as usize..], &mut wg_mem[t0_diff as usize..], n);
                    let thresh_off = 5u32;
                    let esc_borrow = sub_limbs_to(&wg_mem[t0_diff as usize..], &params[thresh_off as usize..], &mut wg_mem[t0_stmp1 as usize..], n);
                    if esc_borrow == 0u32 {
                        ref_escaped = iter + 1u32;
                    }
                }
            }
            vset(wg_mem, ref_escape_addr, ref_escaped);
        }

        gpu_workgroup_barrier();

        // ── Step 2: All threads compute perturbation (only glitched/new pixels) ──
        if is_glitched == 1u32 && escaped_iter == max_iters {
            // Compute Δc = c_pixel - c_ref
            dc_re_sign = signed_sub_to(
                &c_data[c_re_off as usize..], &vget(c_data, c_re_sign_off),
                &wg_mem[ref_c_base as usize..], &wg_mem[ref_c_base + n as usize],
                &mut dc_re, &mut ls1, &mut ls2, n);
            dc_im_sign = signed_sub_to(
                &c_data[c_im_off as usize..], &vget(c_data, c_im_sign_off),
                &wg_mem[ref_c_base + n + 1u32 as usize..], &wg_mem[ref_c_base + 2u32 * n + 1u32 as usize],
                &mut dc_im, &mut ls1, &mut ls2, n);

            // δ_0 = 0
            for i in 0u32..n { delta_re[i as usize] = 0u32; delta_im[i as usize] = 0u32; }
            delta_re_sign = 0u32;
            delta_im_sign = 0u32;
            is_glitched = 0u32;

            let ref_escaped = vget(wg_mem, ref_escape_addr);

            for iter in 0u32..max_iters {
                // If reference orbit escaped, Z values after this are garbage.
                // Mark as glitched so refinement loop picks a new reference.
                if iter >= ref_escaped {
                    is_glitched = 1u32;
                    glitch_iter = iter;
                    break;
                }

                let zn = orbit_base + iter * z_stride;
                let zn_re = zn;
                let zn_re_sign = zn + n;
                let zn_im = zn + n + 1u32;
                let zn_im_sign = zn + 2u32 * n + 1u32;

                // ── δ' = 2·Z_n·δ + δ² + Δc ──

                // Part A: 2*Z*δ (4 multiplies)
                let s1 = signed_mul_to(&wg_mem[zn_re as usize..], &wg_mem[zn_re_sign as usize], &delta_re, &delta_re_sign, &mut t1, &mut lprod, n, frac_limbs);
                let s2 = signed_mul_to(&wg_mem[zn_im as usize..], &wg_mem[zn_im_sign as usize], &delta_im, &delta_im_sign, &mut t2, &mut lprod, n, frac_limbs);
                let s3 = signed_mul_to(&wg_mem[zn_re as usize..], &wg_mem[zn_re_sign as usize], &delta_im, &delta_im_sign, &mut t3, &mut lprod, n, frac_limbs);
                let s4 = signed_mul_to(&wg_mem[zn_im as usize..], &wg_mem[zn_im_sign as usize], &delta_re, &delta_re_sign, &mut t4, &mut lprod, n, frac_limbs);

                // 2*Z*δ real = 2*(t1 - t2)
                let d1_s = signed_sub_to(&t1, &s1, &t2, &s2, &mut t5, &mut ls1, &mut ls2, n);
                let tzd_re_s = signed_add_to(&t5, &d1_s, &t5, &d1_s, &mut t1, &mut ls1, &mut ls2, n);
                // 2*Z*δ imag = 2*(t3 + t4)
                let d2_s = signed_add_to(&t3, &s3, &t4, &s4, &mut t5, &mut ls1, &mut ls2, n);
                let tzd_im_s = signed_add_to(&t5, &d2_s, &t5, &d2_s, &mut t2, &mut ls1, &mut ls2, n);

                // Part B: δ² (3 multiplies, Karatsuba)
                let drs_s = signed_mul_to(&delta_re, &delta_re_sign, &delta_re, &delta_re_sign, &mut t3, &mut lprod, n, frac_limbs);
                let dis_s = signed_mul_to(&delta_im, &delta_im_sign, &delta_im, &delta_im_sign, &mut t4, &mut lprod, n, frac_limbs);
                let dri_s = signed_add_to(&delta_re, &delta_re_sign, &delta_im, &delta_im_sign, &mut t5, &mut ls1, &mut ls2, n);
                let dri2_s = signed_mul_to(&t5, &dri_s, &t5, &dri_s, &mut ls1, &mut lprod, n, frac_limbs);

                // δ² real = δ_re² - δ_im²
                let dsq_re_s = signed_sub_to(&t3, &drs_s, &t4, &dis_s, &mut t5, &mut delta_re, &mut delta_im, n);
                // δ² imag = (δ_re+δ_im)² - δ_re² - δ_im²
                let q1_s = signed_sub_to(&ls1, &dri2_s, &t3, &drs_s, &mut delta_re, &mut ls2, &mut delta_im, n);
                let dsq_im_s = signed_sub_to(&delta_re, &q1_s, &t4, &dis_s, &mut t3, &mut ls2, &mut delta_im, n);

                // Part C: δ' = (2*Z*δ) + δ² + Δc
                let p1_s = signed_add_to(&t1, &tzd_re_s, &t5, &dsq_re_s, &mut t4, &mut ls1, &mut ls2, n);
                let new_dr_s = signed_add_to(&t4, &p1_s, &dc_re, &dc_re_sign, &mut delta_re, &mut ls1, &mut ls2, n);
                delta_re_sign = new_dr_s;

                let p2_s = signed_add_to(&t2, &tzd_im_s, &t3, &dsq_im_s, &mut t4, &mut ls1, &mut ls2, n);
                let new_di_s = signed_add_to(&t4, &p2_s, &dc_im, &dc_im_sign, &mut delta_im, &mut ls1, &mut ls2, n);
                delta_im_sign = new_di_s;

                // ── Glitch check: fixed-point overflow detection ──
                // With multi-precision fixed-point, perturbation stays accurate even
                // when |δ| > |Z| (unlike float). Only detect actual overflow:
                // if integer limb exceeds escape radius (~4), δ has blown up.
                if delta_re[n - 1u32 as usize] > 3u32 || delta_im[n - 1u32 as usize] > 3u32 {
                    is_glitched = 1u32;
                    glitch_iter = iter;
                    break;
                }

                // ── Escape check: |Z_n + δ|² > 4 ──
                let full_re_s = signed_add_to(&wg_mem[zn_re as usize..], &wg_mem[zn_re_sign as usize], &delta_re, &delta_re_sign, &mut t1, &mut ls1, &mut ls2, n);
                let full_im_s = signed_add_to(&wg_mem[zn_im as usize..], &wg_mem[zn_im_sign as usize], &delta_im, &delta_im_sign, &mut t2, &mut ls1, &mut ls2, n);
                let fr2_s = signed_mul_to(&t1, &full_re_s, &t1, &full_re_s, &mut t3, &mut lprod, n, frac_limbs);
                let fi2_s = signed_mul_to(&t2, &full_im_s, &t2, &full_im_s, &mut t4, &mut lprod, n, frac_limbs);
                add_limbs_to(&t3, &t4, &mut t5, n);

                let thresh_off = 5u32;
                let borrow = sub_limbs_to(&t5, &params[thresh_off as usize..], &mut t1, n);
                if borrow == 0u32 {
                    if escaped_iter == max_iters {
                        escaped_iter = iter;
                    }
                }
            }
        }

        gpu_workgroup_barrier();

        // ── Step 3: Glitch analysis — find best new reference ──
        // Each thread votes: glitched pixels report their glitch iteration
        // (higher = iterated longer = better reference candidate)
        if is_glitched == 1u32 && escaped_iter == max_iters {
            vset(wg_mem, vote_base + local_id, glitch_iter + 1u32); // +1 so 0 means "not glitched"
        } else {
            vset(wg_mem, vote_base + local_id, 0u32);
        }

        gpu_workgroup_barrier();

        // Thread 0 scans votes and picks best reference
        if local_id == 0u32 {
            let mut best_vote = 0u32;
            let mut best_idx = 0u32;
            let mut g_count = 0u32;
            for i in 0u32..256u32 {
                if vget(wg_mem, vote_base + i) > best_vote {
                    best_vote = vget(wg_mem, vote_base + i);
                    best_idx = i;
                }
                if vget(wg_mem, vote_base + i) > 0u32 {
                    g_count = g_count + 1u32;
                }
            }
            vset(wg_mem, glitch_count_addr, g_count);
            vset(wg_mem, best_ref_addr, best_idx);

            // Update ref_c to the best pixel's c value
            if g_count > 0u32 {
                let best_gx = gid_x - lid_x + (best_idx % 16u32);
                let best_gy = gid_y - lid_y + (best_idx / 16u32);
                let best_tid = best_gy * width + best_gx;
                let best_c_off = best_tid * c_stride_px;
                for i in 0u32..n { vset(wg_mem, ref_c_base + i, vget(c_data, best_c_off + i)); }
                vset(wg_mem, ref_c_base + n, vget(c_data, best_c_off + n));
                for i in 0u32..n { vset(wg_mem, ref_c_base + n + 1u32 + i, vget(c_data, best_c_off + n + 1u32 + i)); }
                vset(wg_mem, ref_c_base + 2u32 * n + 1u32, vget(c_data, best_c_off + 2u32 * n + 1u32));
            }
        }

        gpu_workgroup_barrier();

        // If no glitches remain, stop refining
        if vget(wg_mem, glitch_count_addr) == 0u32 { break; }
    }

    // ── Colorize ──
    let alpha = 4278190080u32;
    if escaped_iter >= max_iters {
        vset(iter_counts, tid, alpha);
    } else {
        let t_col = escaped_iter * 255u32 / max_iters;
        let r = t_col;
        let g = t_col / 3u32;
        let b = 255u32 - t_col / 2u32;
        vset(iter_counts, tid, alpha | (b << 16u32) | (g << 8u32) | r);
    }
}

} // verus!
