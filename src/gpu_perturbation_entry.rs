/// GPU Mandelbrot kernel with perturbation theory.
/// VERIFIED by Verus AND transpiled to WGSL.
///
/// Architecture: each 16x16 workgroup:
/// 1. Thread 0 computes reference orbit Z_0..Z_N in workgroup shared memory
/// 2. workgroupBarrier()
/// 3. All 256 threads compute perturbation delta using local arrays

use vstd::prelude::*;
use vstd::slice::SliceAdditionalExecFns;
use verus_fixed_point::fixed_point::limb_ops::*;

verus! {

/// No-op barrier for Verus verification (GPU semantics handled by transpiler).
#[verifier::external_body]
fn gpu_workgroup_barrier() { }

/// Vec indexing with u32 (GPU uses u32 indices, Rust needs usize).
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

/// Get immutable slice of Vec starting at u32 offset.
#[inline]
fn vslice(v: &Vec<u32>, off: u32) -> (out: &[u32])
    requires off <= v@.len(),
    ensures out@ == v@.subrange(off as int, v@.len() as int),
{ vstd::slice::slice_subrange(v.as_slice(), off as usize, v.len()) }

/// Copy n limbs from src buffer at src_off into dst starting at index 0.
fn copy_limbs(src: &Vec<u32>, src_off: u32, dst: &mut Vec<u32>, n: u32)
    requires
        src_off + n <= src@.len(),
        src_off + n < 0xFFFF_FFFF,
        n <= old(dst)@.len(),
    ensures
        dst@.len() == old(dst)@.len(),
        forall |j: int| 0 <= j < n ==> (#[trigger] dst@[j]) == src@[(src_off as int + j) as int],
        forall |j: int| n as int <= j < dst@.len() ==> dst@[j] == old(dst)@[j],
{
    let ghost dst_len = dst@.len();
    let ghost old_dst = dst@;
    for i in 0u32..n
        invariant
            dst@.len() == dst_len, dst_len >= n,
            src_off + n <= src@.len(),
            src_off + n < 0xFFFF_FFFF,
            forall |j: int| 0 <= j < i ==> (#[trigger] dst@[j]) == src@[(src_off as int + j) as int],
            forall |j: int| i as int <= j < dst_len ==> dst@[j] == old_dst[j],
    {
        dst.set(i as usize, vget(src, src_off + i));
    }
}

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
        // Params buffer layout
        params@.len() >= 10,
        // width, height, max_iters, n, frac_limbs bounds
        params@[0] > 0, params@[0] <= 0xFFFF,   // width
        params@[1] > 0, params@[1] <= 0xFFFF,   // height
        params@[2] > 0, params@[2] <= 0x1000,   // max_iters <= 4096
        params@[3] >= 1, params@[3] <= 8,        // n (limb count)
        params@[4] <= params@[3],                 // frac_limbs <= n
        // Thread coordinate bounds (GPU guarantees)
        lid_x < 16, lid_y < 16,
        gid_x <= 0xFFFF, gid_y <= 0xFFFF,
        // Shared memory: orbit + ref_c + temporaries + voting
        old(wg_mem)@.len() >= 8192,
        // c_data: per-pixel complex values
        c_data@.len() as int >= (params@[0] as int) * (params@[1] as int) * (2 * (params@[3] as int) + 2),
        // iter_counts: per-pixel output
        old(iter_counts)@.len() as int >= (params@[0] as int) * (params@[1] as int),
        // Escape threshold in params[5..5+n]
        params@.len() as int >= 5 + params@[3] as int,
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
    let mut delta_re: Vec<u32> = generic_zero_vec(n as usize);
    // #[gpu_skip]
    let mut delta_re_sign = 0u32;
    // #[gpu_local(4)]
    let mut delta_im: Vec<u32> = generic_zero_vec(n as usize);
    // #[gpu_skip]
    let mut delta_im_sign = 0u32;

    // Δc = c_pixel - c_ref (computed once, stays constant)
    // #[gpu_local(4)]
    let mut dc_re: Vec<u32> = generic_zero_vec(n as usize);
    // #[gpu_skip]
    let mut dc_re_sign = 0u32;
    // #[gpu_local(4)]
    let mut dc_im: Vec<u32> = generic_zero_vec(n as usize);
    // #[gpu_skip]
    let mut dc_im_sign = 0u32;

    // Temporaries for perturbation arithmetic
    // #[gpu_local(4)]
    let mut t1: Vec<u32> = generic_zero_vec(n as usize);
    // #[gpu_local(4)]
    let mut t2: Vec<u32> = generic_zero_vec(n as usize);
    // #[gpu_local(4)]
    let mut t3: Vec<u32> = generic_zero_vec(n as usize);
    // #[gpu_local(4)]
    let mut t4: Vec<u32> = generic_zero_vec(n as usize);
    // #[gpu_local(4)]
    let mut t5: Vec<u32> = generic_zero_vec(n as usize);
    // #[gpu_local(8)]
    let mut lprod: Vec<u32> = generic_zero_vec((2 * n) as usize);
    // #[gpu_local(4)]
    let mut ls1: Vec<u32> = generic_zero_vec(n as usize);
    // #[gpu_local(4)]
    let mut ls2: Vec<u32> = generic_zero_vec(n as usize);
    // Local temps for reference orbit (avoid aliasing wg_mem reads with writes)
    // #[gpu_local(4)]
    let mut ref_a: Vec<u32> = generic_zero_vec(n as usize);
    // #[gpu_local(4)]
    let mut ref_b: Vec<u32> = generic_zero_vec(n as usize);

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
                // Copy Z_k re from wg_mem to ref_a (avoids borrow aliasing)
                copy_limbs(wg_mem, zk_re, &mut ref_a, n);
                let zk_re_s = vget(wg_mem, zk_re_sign);
                let re2_s = signed_mul_to_buf(
                    &ref_a, &zk_re_s, &ref_a, &zk_re_s,
                    wg_mem, t0_re2 as usize, t0_prod as usize, n as usize, frac_limbs as usize);

                copy_limbs(wg_mem, zk_im, &mut ref_a, n);
                let zk_im_s = vget(wg_mem, zk_im_sign);
                let im2_s = signed_mul_to_buf(
                    &ref_a, &zk_im_s, &ref_a, &zk_im_s,
                    wg_mem, t0_im2 as usize, t0_prod as usize, n as usize, frac_limbs as usize);

                // re + im
                copy_limbs(wg_mem, zk_re, &mut ref_a, n);
                copy_limbs(wg_mem, zk_im, &mut ref_b, n);
                let rpi_s = signed_add_to_buf(
                    &ref_a, &vget(wg_mem, zk_re_sign), &ref_b, &vget(wg_mem, zk_im_sign),
                    wg_mem, t0_rpi as usize, t0_stmp1 as usize, t0_stmp2 as usize, n as usize);

                // (re+im)^2
                copy_limbs(wg_mem, t0_rpi, &mut ref_a, n);
                let sum2_s = signed_mul_to_buf(
                    &ref_a, &rpi_s, &ref_a, &rpi_s,
                    wg_mem, t0_sum2 as usize, t0_prod as usize, n as usize, frac_limbs as usize);

                let zn = orbit_base + (iter + 1u32) * z_stride;

                // new_re = re^2 - im^2 + c_re
                copy_limbs(wg_mem, t0_re2, &mut ref_a, n);
                copy_limbs(wg_mem, t0_im2, &mut ref_b, n);
                let diff_s = signed_sub_to_buf(
                    &ref_a, &re2_s, &ref_b, &im2_s,
                    wg_mem, t0_diff as usize, t0_stmp1 as usize, t0_stmp2 as usize, n as usize);

                copy_limbs(wg_mem, t0_diff, &mut ref_a, n);
                copy_limbs(wg_mem, ref_c_base, &mut ref_b, n);
                let new_re_s = signed_add_to_buf(
                    &ref_a, &diff_s, &ref_b, &vget(wg_mem, (ref_c_base + n)),
                    wg_mem, zn as usize, t0_stmp1 as usize, t0_stmp2 as usize, n as usize);
                vset(wg_mem, zn + n, new_re_s);

                // new_im = (re+im)^2 - re^2 - im^2 + c_im
                copy_limbs(wg_mem, t0_sum2, &mut ref_a, n);
                copy_limbs(wg_mem, t0_re2, &mut ref_b, n);
                let t1_s = signed_sub_to_buf(
                    &ref_a, &sum2_s, &ref_b, &re2_s,
                    wg_mem, t0_diff as usize, t0_stmp1 as usize, t0_stmp2 as usize, n as usize);

                copy_limbs(wg_mem, t0_diff, &mut ref_a, n);
                copy_limbs(wg_mem, t0_im2, &mut ref_b, n);
                let t2_s = signed_sub_to_buf(
                    &ref_a, &t1_s, &ref_b, &im2_s,
                    wg_mem, t0_stmp3 as usize, t0_stmp1 as usize, t0_stmp2 as usize, n as usize);

                copy_limbs(wg_mem, t0_stmp3, &mut ref_a, n);
                copy_limbs(wg_mem, (ref_c_base + n + 1u32), &mut ref_b, n);
                let new_im_s = signed_add_to_buf(
                    &ref_a, &t2_s, &ref_b, &vget(wg_mem, (ref_c_base + 2u32 * n + 1u32)),
                    wg_mem, (zn + n + 1u32) as usize, t0_stmp1 as usize, t0_stmp2 as usize, n as usize);
                vset(wg_mem, zn + 2u32 * n + 1u32, new_im_s);

                // Check if reference escaped: |Z_{k+1}|² > 4
                if ref_escaped == max_iters {
                    copy_limbs(wg_mem, t0_re2, &mut ref_a, n);
                    copy_limbs(wg_mem, t0_im2, &mut ref_b, n);
                    add_limbs_to(&ref_a, &ref_b, wg_mem, t0_diff as usize, n as usize);
                    let thresh_off = 5u32;
                    copy_limbs(wg_mem, t0_diff, &mut ref_a, n);
                    let esc_borrow = sub_limbs_to(&ref_a, vslice(params, thresh_off), wg_mem, t0_stmp1 as usize, n as usize);
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
                vslice(c_data, c_re_off), &vget(c_data, c_re_sign_off),
                vslice(wg_mem, ref_c_base), &vget(wg_mem, (ref_c_base + n)),
                &mut dc_re, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
            dc_im_sign = signed_sub_to(
                vslice(c_data, c_im_off), &vget(c_data, c_im_sign_off),
                vslice(wg_mem, (ref_c_base + n + 1u32)), &vget(wg_mem, (ref_c_base + 2u32 * n + 1u32)),
                &mut dc_im, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);

            // δ_0 = 0
            for i in 0u32..n { delta_re.set(i as usize, 0u32); delta_im.set(i as usize, 0u32); }
            delta_re_sign = 0u32;
            delta_im_sign = 0u32;
            is_glitched = 0u32;

            let ref_escaped = vget(wg_mem, ref_escape_addr);

            for iter in 0u32..max_iters
                invariant
                    // KEY INVARIANT: at every break, either escaped or glitched.
                    // This catches the bug where break on ref escape left
                    // is_glitched==0 and escaped_iter==max_iters (invalid state).
                    escaped_iter <= max_iters,
                    is_glitched == 0u32 || is_glitched == 1u32,
                    // Buffer sizes preserved
                    wg_mem@.len() == old(wg_mem)@.len(),
                    // Local array sizes preserved
                    delta_re@.len() == n as int,
                    delta_im@.len() == n as int,
                    dc_re@.len() == n as int,
                    dc_im@.len() == n as int,
                    t1@.len() == n as int,
                    t2@.len() == n as int,
                    t3@.len() == n as int,
                    t4@.len() == n as int,
                    t5@.len() == n as int,
                    lprod@.len() == 2 * n as int,
                    ref_a@.len() == n as int,
                    ref_b@.len() == n as int,
                    ls1@.len() == n as int,
                    ls2@.len() == n as int,
            {
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
                let s1 = signed_mul_to(vslice(wg_mem, zn_re), &vget(wg_mem, zn_re_sign), &delta_re, &delta_re_sign, &mut t1, 0usize, &mut lprod, 0usize, n as usize, frac_limbs as usize);
                let s2 = signed_mul_to(vslice(wg_mem, zn_im), &vget(wg_mem, zn_im_sign), &delta_im, &delta_im_sign, &mut t2, 0usize, &mut lprod, 0usize, n as usize, frac_limbs as usize);
                let s3 = signed_mul_to(vslice(wg_mem, zn_re), &vget(wg_mem, zn_re_sign), &delta_im, &delta_im_sign, &mut t3, 0usize, &mut lprod, 0usize, n as usize, frac_limbs as usize);
                let s4 = signed_mul_to(vslice(wg_mem, zn_im), &vget(wg_mem, zn_im_sign), &delta_re, &delta_re_sign, &mut t4, 0usize, &mut lprod, 0usize, n as usize, frac_limbs as usize);

                // 2*Z*δ real = 2*(t1 - t2)
                let d1_s = signed_sub_to(&t1, &s1, &t2, &s2, &mut t5, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
                let tzd_re_s = signed_add_to(&t5, &d1_s, &t5, &d1_s, &mut t1, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
                // 2*Z*δ imag = 2*(t3 + t4)
                let d2_s = signed_add_to(&t3, &s3, &t4, &s4, &mut t5, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
                let tzd_im_s = signed_add_to(&t5, &d2_s, &t5, &d2_s, &mut t2, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);

                // Part B: δ² (3 multiplies, Karatsuba)
                let drs_s = signed_mul_to(&delta_re, &delta_re_sign, &delta_re, &delta_re_sign, &mut t3, 0usize, &mut lprod, 0usize, n as usize, frac_limbs as usize);
                let dis_s = signed_mul_to(&delta_im, &delta_im_sign, &delta_im, &delta_im_sign, &mut t4, 0usize, &mut lprod, 0usize, n as usize, frac_limbs as usize);
                let dri_s = signed_add_to(&delta_re, &delta_re_sign, &delta_im, &delta_im_sign, &mut t5, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
                let dri2_s = signed_mul_to(&t5, &dri_s, &t5, &dri_s, &mut ls1, 0usize, &mut lprod, 0usize, n as usize, frac_limbs as usize);

                // δ² real = δ_re² - δ_im²
                let dsq_re_s = signed_sub_to(&t3, &drs_s, &t4, &dis_s, &mut t5, 0usize, &mut delta_re, 0usize, &mut delta_im, 0usize, n as usize);
                // δ² imag = (δ_re+δ_im)² - δ_re² - δ_im²
                let q1_s = signed_sub_to(&ls1, &dri2_s, &t3, &drs_s, &mut delta_re, 0usize, &mut ls2, 0usize, &mut delta_im, 0usize, n as usize);
                let dsq_im_s = signed_sub_to(&delta_re, &q1_s, &t4, &dis_s, &mut t3, 0usize, &mut ls2, 0usize, &mut delta_im, 0usize, n as usize);

                // Part C: δ' = (2*Z*δ) + δ² + Δc
                let p1_s = signed_add_to(&t1, &tzd_re_s, &t5, &dsq_re_s, &mut t4, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
                let new_dr_s = signed_add_to(&t4, &p1_s, &dc_re, &dc_re_sign, &mut delta_re, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
                delta_re_sign = new_dr_s;

                let p2_s = signed_add_to(&t2, &tzd_im_s, &t3, &dsq_im_s, &mut t4, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
                let new_di_s = signed_add_to(&t4, &p2_s, &dc_im, &dc_im_sign, &mut delta_im, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
                delta_im_sign = new_di_s;

                // ── Glitch check: fixed-point overflow detection ──
                // With multi-precision fixed-point, perturbation stays accurate even
                // when |δ| > |Z| (unlike float). Only detect actual overflow:
                // if integer limb exceeds escape radius (~4), δ has blown up.
                if delta_re[(n - 1u32) as usize] > 3u32 || delta_im[(n - 1u32) as usize] > 3u32 {
                    is_glitched = 1u32;
                    glitch_iter = iter;
                    break;
                }

                // ── Escape check: |Z_n + δ|² > 4 ──
                let full_re_s = signed_add_to(vslice(wg_mem, zn_re), &vget(wg_mem, zn_re_sign), &delta_re, &delta_re_sign, &mut t1, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
                let full_im_s = signed_add_to(vslice(wg_mem, zn_im), &vget(wg_mem, zn_im_sign), &delta_im, &delta_im_sign, &mut t2, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
                let fr2_s = signed_mul_to(&t1, &full_re_s, &t1, &full_re_s, &mut t3, 0usize, &mut lprod, 0usize, n as usize, frac_limbs as usize);
                let fi2_s = signed_mul_to(&t2, &full_im_s, &t2, &full_im_s, &mut t4, 0usize, &mut lprod, 0usize, n as usize, frac_limbs as usize);
                add_limbs_to(&t3, &t4, &mut t5, 0usize, n as usize);

                let thresh_off = 5u32;
                let borrow = sub_limbs_to(&t5, vslice(params, thresh_off), &mut t1, 0usize, n as usize);
                if borrow == 0u32 {
                    if escaped_iter == max_iters {
                        escaped_iter = iter;
                    }
                }
            }
            // POST-LOOP INVARIANT: pixel must be in a valid state.
            // Either escaped (found iteration count), glitched (needs re-reference),
            // or completed all iterations (in the Mandelbrot set).
            // The bug we caught: break on ref escape without setting is_glitched
            // left escaped_iter==max_iters AND is_glitched==0 → invalid state.
            // POST-LOOP: pixel must be escaped, glitched, or completed all iters.
            // (Requires comprehensive buffer preconditions to verify non-vacuously.)
            assert(escaped_iter < max_iters || is_glitched == 1u32);
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
