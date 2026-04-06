/// GPU Mandelbrot kernel with perturbation theory.
///
/// Architecture: each 16×16 workgroup:
/// 1. Thread 0 computes reference orbit Z_0..Z_N → workgroup shared memory
/// 2. workgroupBarrier()
/// 3. All 256 threads compute perturbation δ using local arrays
///
/// Reference orbit uses shared memory (fast on-chip SRAM).
/// Per-pixel δ uses thread-local arrays (registers via #[gpu_local]).
/// Δc = c_pixel - c_ref computed once per pixel.
///
/// All arithmetic from verified verus-fixed-point (944 verified, 0 errors).

use verus_fixed_point::fixed_point::limb_ops::*;

// Shared memory layout (for N=4, max_iters=200):
//   orbit: max_iters * (2*N+2) = 200*10 = 2000 words (8KB)
//   ref_c: 2*N+2 = 10 words
//   tmp region for thread 0: ~50 words
//   Total: ~2100 words ≈ 8.5KB (well within 16-48KB limit)
//
// We allocate 4096 words = 16KB to be safe.
#[gpu_kernel(workgroup_size(16, 16, 1))]
fn mandelbrot_perturbation(
    #[gpu_builtin(thread_id_x)] gid_x: u32,
    #[gpu_builtin(thread_id_y)] gid_y: u32,
    #[gpu_builtin(local_id_x)] lid_x: u32,
    #[gpu_builtin(local_id_y)] lid_y: u32,
    #[gpu_buffer(0, read)] c_data: &[u32],
    #[gpu_shared(4096)] wg_mem: &mut [u32],
    #[gpu_buffer(1, read_write)] iter_counts: &mut [u32],
    #[gpu_buffer(2, read)] params: &[u32],
) {
    let width = params[0u32];
    let height = params[1u32];
    let max_iters = params[2u32];
    let n = params[3u32];
    let frac_limbs = params[4u32];

    if gid_x >= width { return; }
    if gid_y >= height { return; }

    let tid = gid_y * width + gid_x;
    let local_id = lid_y * 16u32 + lid_x;

    // Stride per complex value in shared memory: re(n) + re_sign(1) + im(n) + im_sign(1)
    let z_stride = 2u32 * n + 2u32;

    // Shared memory regions
    let orbit_base = 0u32;                          // Z_0..Z_{max_iters}: max_iters * z_stride
    let ref_c_base = max_iters * z_stride;          // c_ref: z_stride words
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

    // ═══════════════════════════════════════════════════
    // Phase 1: Thread 0 computes reference orbit
    // ═══════════════════════════════════════════════════
    // Reference point = center of workgroup
    let ref_x = gid_x - lid_x + 8u32;
    let ref_y = gid_y - lid_y + 8u32;
    // Clamp to image bounds
    let ref_x_c = if ref_x >= width { width - 1u32 } else { ref_x };
    let ref_y_c = if ref_y >= height { height - 1u32 } else { ref_y };
    let ref_tid = ref_y_c * width + ref_x_c;

    if local_id == 0u32 {
        // Load c_ref into shared memory
        let ref_c_off = ref_tid * c_stride_px;
        for i in 0u32..n {
            wg_mem[ref_c_base + i] = c_data[ref_c_off + i];
        }
        wg_mem[ref_c_base + n] = c_data[ref_c_off + n];
        for i in 0u32..n {
            wg_mem[ref_c_base + n + 1u32 + i] = c_data[ref_c_off + n + 1u32 + i];
        }
        wg_mem[ref_c_base + 2u32 * n + 1u32] = c_data[ref_c_off + 2u32 * n + 1u32];

        // Z_0 = 0
        let z0_off = orbit_base;
        for i in 0u32..n { wg_mem[z0_off + i] = 0u32; }
        wg_mem[z0_off + n] = 0u32;
        for i in 0u32..n { wg_mem[z0_off + n + 1u32 + i] = 0u32; }
        wg_mem[z0_off + 2u32 * n + 1u32] = 0u32;

        // Iterate: Z_{k+1} = Z_k^2 + c_ref
        for iter in 0u32..max_iters {
            let zk = orbit_base + iter * z_stride;
            let zk_re = zk;
            let zk_re_sign = zk + n;
            let zk_im = zk + n + 1u32;
            let zk_im_sign = zk + 2u32 * n + 1u32;

            // re^2 → t0_re2
            let re2_s = signed_mul_to(
                &wg_mem[zk_re..], &wg_mem[zk_re_sign],
                &wg_mem[zk_re..], &wg_mem[zk_re_sign],
                &mut wg_mem[t0_re2..], &mut wg_mem[t0_prod..], n, frac_limbs);
            // im^2 → t0_im2
            let im2_s = signed_mul_to(
                &wg_mem[zk_im..], &wg_mem[zk_im_sign],
                &wg_mem[zk_im..], &wg_mem[zk_im_sign],
                &mut wg_mem[t0_im2..], &mut wg_mem[t0_prod..], n, frac_limbs);
            // re+im → t0_rpi
            let rpi_s = signed_add_to(
                &wg_mem[zk_re..], &wg_mem[zk_re_sign],
                &wg_mem[zk_im..], &wg_mem[zk_im_sign],
                &mut wg_mem[t0_rpi..], &mut wg_mem[t0_stmp1..], &mut wg_mem[t0_stmp2..], n);
            // (re+im)^2 → t0_sum2
            let sum2_s = signed_mul_to(
                &wg_mem[t0_rpi..], &rpi_s,
                &wg_mem[t0_rpi..], &rpi_s,
                &mut wg_mem[t0_sum2..], &mut wg_mem[t0_prod..], n, frac_limbs);

            // Store Z_{k+1}
            let zn = orbit_base + (iter + 1u32) * z_stride;
            // Z_{k+1}.re = re^2 - im^2 + c_re
            let diff_s = signed_sub_to(
                &wg_mem[t0_re2..], &re2_s,
                &wg_mem[t0_im2..], &im2_s,
                &mut wg_mem[t0_diff..], &mut wg_mem[t0_stmp1..], &mut wg_mem[t0_stmp2..], n);
            let new_re_s = signed_add_to(
                &wg_mem[t0_diff..], &diff_s,
                &wg_mem[ref_c_base..], &wg_mem[ref_c_base + n],
                &mut wg_mem[zn..], &mut wg_mem[t0_stmp1..], &mut wg_mem[t0_stmp2..], n);
            wg_mem[zn + n] = new_re_s;

            // Z_{k+1}.im = (re+im)^2 - re^2 - im^2 + c_im
            let t1_s = signed_sub_to(
                &wg_mem[t0_sum2..], &sum2_s,
                &wg_mem[t0_re2..], &re2_s,
                &mut wg_mem[t0_diff..], &mut wg_mem[t0_stmp1..], &mut wg_mem[t0_stmp2..], n);
            let t2_s = signed_sub_to(
                &wg_mem[t0_diff..], &t1_s,
                &wg_mem[t0_im2..], &im2_s,
                &mut wg_mem[t0_stmp3..], &mut wg_mem[t0_stmp1..], &mut wg_mem[t0_stmp2..], n);
            let new_im_s = signed_add_to(
                &wg_mem[t0_stmp3..], &t2_s,
                &wg_mem[ref_c_base + n + 1u32..], &wg_mem[ref_c_base + 2u32 * n + 1u32],
                &mut wg_mem[zn + n + 1u32..], &mut wg_mem[t0_stmp1..], &mut wg_mem[t0_stmp2..], n);
            wg_mem[zn + 2u32 * n + 1u32] = new_im_s;
        }
    }

    gpu_workgroup_barrier();

    // ═══════════════════════════════════════════════════
    // Phase 2: All threads compute Δc and perturbation
    // ═══════════════════════════════════════════════════

    // Δc_re = c_pixel_re - c_ref_re
    dc_re_sign = signed_sub_to(
        &c_data[c_re_off..], &c_data[c_re_sign_off],
        &wg_mem[ref_c_base..], &wg_mem[ref_c_base + n],
        &mut dc_re, &mut ls1, &mut ls2, n);
    // Δc_im = c_pixel_im - c_ref_im
    dc_im_sign = signed_sub_to(
        &c_data[c_im_off..], &c_data[c_im_sign_off],
        &wg_mem[ref_c_base + n + 1u32..], &wg_mem[ref_c_base + 2u32 * n + 1u32],
        &mut dc_im, &mut ls1, &mut ls2, n);

    // δ_0 = 0 (Z_0 = 0 means first perturbation gives δ_1 = Δc)
    for i in 0u32..n { delta_re[i] = 0u32; delta_im[i] = 0u32; }
    delta_re_sign = 0u32;
    delta_im_sign = 0u32;

    let mut escaped_iter = max_iters;

    for iter in 0u32..max_iters {
        // Read Z_n from shared memory
        let zn = orbit_base + iter * z_stride;
        let zn_re = zn;
        let zn_re_sign = zn + n;
        let zn_im = zn + n + 1u32;
        let zn_im_sign = zn + 2u32 * n + 1u32;

        // ── Compute δ' = 2·Z_n·δ + δ² + Δc ──
        // Complex form:
        //   δ're = 2*(Z_re*δ_re - Z_im*δ_im) + (δ_re² - δ_im²) + Δc_re
        //   δ'im = 2*(Z_re*δ_im + Z_im*δ_re) + 2*δ_re*δ_im + Δc_im

        // ── Part A: 2*Z*δ (4 multiplies) ──
        // Z_re * δ_re → t1
        let s1 = signed_mul_to(
            &wg_mem[zn_re..], &wg_mem[zn_re_sign],
            &delta_re, &delta_re_sign,
            &mut t1, &mut lprod, n, frac_limbs);
        // Z_im * δ_im → t2
        let s2 = signed_mul_to(
            &wg_mem[zn_im..], &wg_mem[zn_im_sign],
            &delta_im, &delta_im_sign,
            &mut t2, &mut lprod, n, frac_limbs);
        // Z_re * δ_im → t3
        let s3 = signed_mul_to(
            &wg_mem[zn_re..], &wg_mem[zn_re_sign],
            &delta_im, &delta_im_sign,
            &mut t3, &mut lprod, n, frac_limbs);
        // Z_im * δ_re → t4
        let s4 = signed_mul_to(
            &wg_mem[zn_im..], &wg_mem[zn_im_sign],
            &delta_re, &delta_re_sign,
            &mut t4, &mut lprod, n, frac_limbs);

        // 2*Z*δ real = 2*(Z_re*δ_re - Z_im*δ_im) → t5
        let d1_s = signed_sub_to(
            &t1, &s1, &t2, &s2,
            &mut t5, &mut ls1, &mut ls2, n);
        let tzd_re_s = signed_add_to(
            &t5, &d1_s, &t5, &d1_s,
            &mut t1, &mut ls1, &mut ls2, n);
        // t1 now holds 2*Z*δ real part, sign = tzd_re_s

        // 2*Z*δ imag = 2*(Z_re*δ_im + Z_im*δ_re) → t5
        let d2_s = signed_add_to(
            &t3, &s3, &t4, &s4,
            &mut t5, &mut ls1, &mut ls2, n);
        let tzd_im_s = signed_add_to(
            &t5, &d2_s, &t5, &d2_s,
            &mut t2, &mut ls1, &mut ls2, n);
        // t2 now holds 2*Z*δ imag part, sign = tzd_im_s

        // ── Part B: δ² (3 multiplies using Karatsuba trick) ──
        // δ_re² → t3
        let drs_s = signed_mul_to(
            &delta_re, &delta_re_sign,
            &delta_re, &delta_re_sign,
            &mut t3, &mut lprod, n, frac_limbs);
        // δ_im² → t4
        let dis_s = signed_mul_to(
            &delta_im, &delta_im_sign,
            &delta_im, &delta_im_sign,
            &mut t4, &mut lprod, n, frac_limbs);
        // (δ_re + δ_im)² → t5
        let dri_s = signed_add_to(
            &delta_re, &delta_re_sign,
            &delta_im, &delta_im_sign,
            &mut t5, &mut ls1, &mut ls2, n);
        let dri2_s = signed_mul_to(
            &t5, &dri_s,
            &t5, &dri_s,
            &mut ls1, &mut lprod, n, frac_limbs);
        // ls1 now holds (δ_re+δ_im)²

        // δ² real = δ_re² - δ_im² → t5
        let dsq_re_s = signed_sub_to(
            &t3, &drs_s, &t4, &dis_s,
            &mut t5, &mut delta_re, &mut delta_im, n);
        // t5 = δ² real, sign = dsq_re_s
        // (delta_re/im used as tmp, will be overwritten below)

        // δ² imag = (δ_re+δ_im)² - δ_re² - δ_im² → delta_re (tmp)
        let q1_s = signed_sub_to(
            &ls1, &dri2_s, &t3, &drs_s,
            &mut delta_re, &mut ls2, &mut delta_im, n);
        let dsq_im_s = signed_sub_to(
            &delta_re, &q1_s, &t4, &dis_s,
            &mut t3, &mut ls2, &mut delta_im, n);
        // t3 = δ² imag, sign = dsq_im_s

        // ── Part C: Sum up: δ' = (2*Z*δ) + δ² + Δc ──
        // δ're = t1 + t5 + dc_re
        let p1_s = signed_add_to(
            &t1, &tzd_re_s, &t5, &dsq_re_s,
            &mut t4, &mut ls1, &mut ls2, n);
        let new_dr_s = signed_add_to(
            &t4, &p1_s, &dc_re, &dc_re_sign,
            &mut delta_re, &mut ls1, &mut ls2, n);
        delta_re_sign = new_dr_s;

        // δ'im = t2 + t3 + dc_im
        let p2_s = signed_add_to(
            &t2, &tzd_im_s, &t3, &dsq_im_s,
            &mut t4, &mut ls1, &mut ls2, n);
        let new_di_s = signed_add_to(
            &t4, &p2_s, &dc_im, &dc_im_sign,
            &mut delta_im, &mut ls1, &mut ls2, n);
        delta_im_sign = new_di_s;

        // ── Escape check: |Z_n + δ|² > 4 ──
        // Compute |Z+δ|² = (Z_re+δ_re)² + (Z_im+δ_im)²
        // Use t1, t2 as temporaries
        let full_re_s = signed_add_to(
            &wg_mem[zn_re..], &wg_mem[zn_re_sign],
            &delta_re, &delta_re_sign,
            &mut t1, &mut ls1, &mut ls2, n);
        let full_im_s = signed_add_to(
            &wg_mem[zn_im..], &wg_mem[zn_im_sign],
            &delta_im, &delta_im_sign,
            &mut t2, &mut ls1, &mut ls2, n);
        // |full_re|²
        let fr2_s = signed_mul_to(
            &t1, &full_re_s, &t1, &full_re_s,
            &mut t3, &mut lprod, n, frac_limbs);
        // |full_im|²
        let fi2_s = signed_mul_to(
            &t2, &full_im_s, &t2, &full_im_s,
            &mut t4, &mut lprod, n, frac_limbs);
        // |Z+δ|² = fr² + fi²
        add_limbs_to(&t3, &t4, &mut t5, n);

        // Compare against threshold at params[5..5+n]
        let thresh_off = 5u32;
        let borrow = sub_limbs_to(&t5, &params[thresh_off..], &mut t1, n);
        if borrow == 0u32 {
            if escaped_iter == max_iters {
                escaped_iter = iter;
            }
        }
    }

    // ── Colorize ──
    let alpha = 4278190080u32;
    if escaped_iter >= max_iters {
        iter_counts[tid] = alpha;
    } else {
        let t = escaped_iter * 255u32 / max_iters;
        let r = t;
        let g = t / 3u32;
        let b = 255u32 - t / 2u32;
        iter_counts[tid] = alpha | (b << 16u32) | (g << 8u32) | r;
    }
}
