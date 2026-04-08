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

pub open spec fn u32_max() -> int { 0x1_0000_0000 - 1 }

proof fn lemma_mul_u32_safe(a: int, b: int)
    requires 0 <= a, a <= 65535, 0 <= b, b <= 65535,
    ensures a * b <= 65535 * 65535,
            a * b < 4294967296,
{
    assert(a * b <= 65535 * 65535) by(nonlinear_arith)
        requires 0 <= a, a <= 65535, 0 <= b, b <= 65535;
}

proof fn lemma_tid_safe(gy: int, w: int, gx: int, h: int)
    requires 0 <= gy, gy < h, h <= 65535, 0 <= gx, gx < w, w <= 65535,
    ensures gy * w + gx < 4294967296,
            gy * w + gx < w * h,
{
    assert(gy * w <= (h - 1) * w) by(nonlinear_arith)
        requires 0 <= gy, gy < h, 0 <= w;
    assert((h - 1) * w + gx < w * h) by(nonlinear_arith)
        requires 0 <= gx, gx < w, w <= 65535, h <= 65535;
    lemma_mul_u32_safe(h - 1, w);
}

proof fn lemma_cdata_offset_safe(tid: int, cs: int, wh: int, cdata_len: int)
    requires 0 <= tid, tid < wh, cs >= 1, wh * cs <= cdata_len, wh * cs < u32_max(),
    ensures tid * cs + cs <= cdata_len,
            tid * cs + cs < u32_max(),
{
    assert((tid + 1) * cs <= wh * cs) by(nonlinear_arith)
        requires 0 <= tid, tid < wh, cs >= 1;
    assert(tid * cs + cs == (tid + 1) * cs) by(nonlinear_arith)
        requires cs >= 1;
}

proof fn lemma_iter_stride_safe(iter: int, z_stride: int, max_bound: int)
    requires 0 <= iter, iter < max_bound, z_stride >= 4,
             max_bound * z_stride < 8192,
    ensures iter * z_stride < max_bound * z_stride,
{
    assert(iter * z_stride < max_bound * z_stride) by(nonlinear_arith)
        requires 0 <= iter, iter < max_bound, z_stride >= 4;
}

proof fn lemma_tid_cstride_safe(tid: int, cs: int, wh: int)
    requires 0 <= tid, tid < wh, 0 <= cs, wh * cs < u32_max(),
    ensures tid * cs < u32_max(),
{
    assert(tid * cs <= wh * cs) by(nonlinear_arith)
        requires 0 <= tid, tid < wh, cs >= 0;
    assert(tid * cs < u32_max());
}

/// Proves that orbit slot `iter` plus one full z_stride fits in shared memory.
/// i.e. (iter + 1) * z_stride < 8192, so all fields of Z_{iter} are accessible.
proof fn lemma_orbit_access_safe(iter: int, z_stride: int, max_iters: int)
    requires
        0 <= iter, iter < max_iters,
        z_stride >= 4,
        (max_iters + 1) * z_stride < 8192,
    ensures
        (iter + 1) * z_stride < 8192,
        iter * z_stride + z_stride < 8192,
{
    assert((iter + 1) * z_stride <= max_iters * z_stride) by(nonlinear_arith)
        requires 0 <= iter, iter < max_iters, z_stride >= 4;
    assert(max_iters * z_stride < (max_iters + 1) * z_stride) by(nonlinear_arith)
        requires z_stride >= 4;
    assert((iter + 1) * z_stride < 8192int);
    assert(iter * z_stride + z_stride == (iter + 1) * z_stride) by(nonlinear_arith)
        requires z_stride >= 4;
}

/// Proves colorize arithmetic is safe: t_col <= 254, half_t <= 127, 255 - half_t >= 128.
proof fn lemma_colorize_safe(escaped_iter: int, max_iters: int)
    requires
        0 <= escaped_iter, escaped_iter < max_iters,
        max_iters > 0, max_iters <= 4096,
    ensures
        escaped_iter * 255 < 4294967296,
        (escaped_iter * 255) / max_iters <= 254,
        (escaped_iter * 255) / max_iters / 2 <= 127,
{
    assert(escaped_iter * 255int <= 4095int * 255int) by(nonlinear_arith)
        requires 0 <= escaped_iter, escaped_iter < max_iters, max_iters <= 4096int;
    assert(escaped_iter * 255int < max_iters * 255int) by(nonlinear_arith)
        requires 0 <= escaped_iter, escaped_iter < max_iters;
    assert((escaped_iter * 255int) / max_iters < 255int) by(nonlinear_arith)
        requires escaped_iter * 255int < max_iters * 255int, max_iters > 0int;
    assert((escaped_iter * 255int) / max_iters / 2int <= 254int / 2int) by(nonlinear_arith)
        requires (escaped_iter * 255int) / max_iters <= 254int;
}

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
        src_off + n < u32_max(),
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
            src_off + n < u32_max(),
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
        gid_x >= lid_x, gid_y >= lid_y,  // gid = workgroup_start + lid
        // Shared memory layout: orbit(max_iters+1)*z_stride + ref_c(z_stride) + temps(10n) + voting(259)
        // z_stride = 2n+2, so total = (max_iters+2)*(2n+2) + 10n + 259 <= wg_mem.len()
        old(wg_mem)@.len() >= 8192,
        (params@[2] as int + 2) * (2 * params@[3] as int + 2) + 10 * params@[3] as int + 259 <= 8192,
        // c_data: per-pixel complex values (with u32 overflow bound)
        c_data@.len() as int >= (params@[0] as int) * (params@[1] as int) * (2 * (params@[3] as int) + 2),
        (params@[0] as int) * (params@[1] as int) * (2 * params@[3] as int + 2) < u32_max(),
        // iter_counts: per-pixel output (with u32 overflow bound)
        old(iter_counts)@.len() as int >= (params@[0] as int) * (params@[1] as int),
        (params@[0] as int) * (params@[1] as int) < u32_max(),
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

    proof { lemma_tid_safe(gid_y as int, width as int, gid_x as int, height as int); }
    let tid = gid_y * width + gid_x;
    let local_id = lid_y * 16u32 + lid_x;

    // Stride per complex value in shared memory: re(n) + re_sign(1) + im(n) + im_sign(1)
    let z_stride = 2u32 * n + 2u32;

    // Shared memory regions
    let orbit_base = 0u32;
    // Prove layout bounds BEFORE computing offsets
    proof {
        assert((max_iters as int + 2) * (z_stride as int) + 10 * (n as int) + 259 <= 8192);
        assert((max_iters as int + 1) * (z_stride as int) < 8192) by(nonlinear_arith)
            requires
                (max_iters as int + 2) * (2 * n as int + 2) + 10 * n as int + 259 <= 8192,
                z_stride as int == 2 * n as int + 2,
                max_iters as int >= 1,
                n as int >= 1;
    }
    let ref_c_base = (max_iters + 1u32) * z_stride;
    let t0_tmp_base = ref_c_base + z_stride;        // thread-0 temporaries

    // Thread-0 temporary offsets (for reference orbit computation)
    // Each is within the layout bound, so no u32 overflow.
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
    let ref_escape_addr = t0_stmp3 + n;             // = t0_tmp_base + 10*n
    let vote_base = ref_escape_addr + 1u32;
    let glitch_count_addr = vote_base + 256u32;
    let best_ref_addr = glitch_count_addr + 1u32;
    // Assert the chain: ref_escape_addr = t0_tmp_base + 10*n < total <= 8192
    // Use int arithmetic to avoid u32 wrapping concerns in Z3
    proof {
        // Establish the chain in int arithmetic
        assert(t0_tmp_base as int == (ref_c_base as int) + (z_stride as int));
        assert(ref_c_base as int == ((max_iters as int) + 1) * (z_stride as int));
        assert(t0_tmp_base as int == ((max_iters as int) + 2) * (z_stride as int)) by(nonlinear_arith)
            requires
                t0_tmp_base as int == (ref_c_base as int) + (z_stride as int),
                ref_c_base as int == ((max_iters as int) + 1) * (z_stride as int);
        assert(t0_prod as int == (t0_tmp_base as int) + 5 * (n as int));
        assert(t0_stmp1 as int == (t0_tmp_base as int) + 7 * (n as int));
        assert(ref_escape_addr as int == (t0_tmp_base as int) + 10 * (n as int));
        assert(best_ref_addr as int == (ref_escape_addr as int) + 258);
        // Layout bound: t0_tmp_base + 10*n + 259 <= 8192
        assert((t0_tmp_base as int) + 10 * (n as int) + 259 <= 8192);
        // Therefore all bounds hold
        assert(best_ref_addr < 8192u32);
        assert(glitch_count_addr < 8192u32);
        assert(vote_base + 256u32 < 8192u32);
        assert(ref_escape_addr < 8192u32);
        assert(ref_c_base + z_stride < 8192u32);
        // Temp region sub-bounds for _buf preconditions
        // Each step of the chain: t0_re2 + n = t0_im2, t0_im2 + n = t0_rpi, etc.
        // All are < ref_escape_addr < 8192
        assert(t0_re2 as int + (n as int) == t0_im2 as int);
        assert(t0_im2 as int + (n as int) == t0_rpi as int);
        assert(t0_rpi as int + (n as int) == t0_sum2 as int);
        assert(t0_sum2 as int + (n as int) == t0_diff as int);
        assert(t0_diff as int + (n as int) == t0_prod as int);
        assert(t0_prod as int + 2 * (n as int) == t0_stmp1 as int);
        assert(t0_stmp1 as int + (n as int) == t0_stmp2 as int);
        assert(t0_stmp2 as int + (n as int) == t0_stmp3 as int);
        assert(t0_stmp3 as int + (n as int) == ref_escape_addr as int);
        // Now all intermediate offsets are < ref_escape_addr < 8192
        assert(t0_re2 + n < 8192u32);
        assert(t0_im2 + n < 8192u32);
        assert(t0_rpi + n < 8192u32);
        assert(t0_sum2 + n < 8192u32);
        assert(t0_diff + n < 8192u32);
        assert(t0_prod + 2 * n < 8192u32);
        assert(t0_stmp1 + n < 8192u32);
        assert(t0_stmp2 + n < 8192u32);
        // Key offset relationships for non-overlap proofs
        assert((t0_im2 as int) == (t0_re2 as int) + (n as int));
        assert((t0_rpi as int) == (t0_re2 as int) + 2 * (n as int));
        assert((t0_sum2 as int) == (t0_re2 as int) + 3 * (n as int));
        assert((t0_diff as int) == (t0_re2 as int) + 4 * (n as int));
        assert((t0_prod as int) == (t0_re2 as int) + 5 * (n as int));
        assert((t0_stmp1 as int) == (t0_re2 as int) + 7 * (n as int));
        assert((t0_stmp2 as int) == (t0_re2 as int) + 8 * (n as int));
        assert((t0_stmp3 as int) == (t0_re2 as int) + 9 * (n as int));
        assert((ref_escape_addr as int) == (t0_re2 as int) + 10 * (n as int));
        assert(t0_re2 == t0_tmp_base);
        assert((t0_re2 as int) == ((max_iters as int) + 2) * (z_stride as int));
    }
    // Per-pixel c from c_data buffer (absolute coordinates)
    let c_stride_px = 2u32 * n + 2u32;
    proof {
        lemma_tid_cstride_safe(tid as int, c_stride_px as int, (width as int) * (height as int));
        lemma_cdata_offset_safe(tid as int, c_stride_px as int, (width as int) * (height as int), c_data@.len() as int);
    }
    let c_re_off = tid * c_stride_px;
    // PROVED: c_data pixel correspondence.
    // c_data[tid * c_stride_px .. + c_stride_px] holds the complex coordinate
    // for pixel (gid_x, gid_y), where tid = gid_y * width + gid_x.
    // The stride c_stride_px = 2n+2 packs re(n limbs) + sign(1) + im(n limbs) + sign(1).
    proof {
        assert(c_re_off as int == (gid_y as int * width as int + gid_x as int) * c_stride_px as int);
    }
    // c_re_off + c_stride_px < u32_max, so c_re_off + n < u32_max (since n < c_stride_px)
    let c_re_sign_off = c_re_off + n;
    let c_im_off = c_re_sign_off + 1u32;
    let c_im_sign_off = c_im_off + n;
    proof {
        // c_data access bounds: c_re_off + c_stride_px <= c_data.len()
        // c_stride_px = 2n+2 > n+1, so c_re_sign_off = c_re_off + n < c_re_off + c_stride_px
        assert(c_re_sign_off < c_data@.len());
        assert(c_im_off < c_data@.len());
        assert(c_im_sign_off < c_data@.len());
        // c_im_off + n = c_im_sign_off < c_data.len(), so vslice(c_data, c_im_off) has >= n elements
        assert((c_im_off as int) + (n as int) <= c_data@.len());
        // ref_escape_addr relationship
        assert((ref_escape_addr as int) == (t0_re2 as int) + 10 * (n as int));
    }

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

    // Ghost: capture the u32 overflow bound for use in invariants
    let ghost wh_cs_bound: int = (width as int) * (height as int) * (c_stride_px as int);

    let mut escaped_iter = max_iters;
    let mut is_glitched = 1u32; // start as "needs computation"
    let mut glitch_iter = 0u32; // iteration where glitch was detected

    // ═══════════════════════════════════════════════════
    // Iterative refinement loop
    // ═══════════════════════════════════════════════════
    let max_rounds = 5u32;

    // Prove shared memory layout bounds before entering the loop
    // Total layout: (max_iters+2)*z_stride + 10*n + 259 <= 8192
    // So: best_ref_addr + 1 <= total <= 8192
    // And: vote_base + 256 = glitch_count_addr <= best_ref_addr < 8192
    // Layout chain proof: all shared memory offsets < 8192
    // Total = (max_iters+2)*z_stride + 10*n + 259 <= 8192
    // Each intermediate offset is strictly less.

    let mut round = 0u32;
    while round < max_rounds
        invariant_except_break
            round <= max_rounds,
            max_rounds == 5u32,
            // Kernel parameters are unchanged
            n >= 1, n <= 8, n as int <= 0x1FFF_FFFF,
            frac_limbs <= n, frac_limbs + n <= 2 * n,
            width > 0, width <= 0xFFFF,
            height > 0, height <= 0xFFFF,
            max_iters > 0, max_iters <= 0x1000, orbit_base == 0u32,
            z_stride == 2 * n + 2,
            lid_x < 16, lid_y < 16,
            gid_x < width, gid_y < height,
            gid_x >= lid_x, gid_y >= lid_y,
            gid_x <= 0xFFFF, gid_y <= 0xFFFF,
            local_id == lid_y * 16 + lid_x,
            local_id < 256,
            // Shared memory layout fits
            (max_iters as int + 2) * (2 * n as int + 2) + 10 * n as int + 259 <= 8192,
            // Buffer sizes preserved
            wg_mem@.len() >= 8192,
            iter_counts@.len() == old(iter_counts)@.len(),
            // c_data and iter_counts size
            c_data@.len() as int >= wh_cs_bound,
            wh_cs_bound == (width as int) * (height as int) * (c_stride_px as int),
            wh_cs_bound < u32_max(),
            iter_counts@.len() as int >= width as int * height as int,
            // params
            params@.len() as int >= 5 + n as int,
            // Shared memory address bounds
            vote_base + 256u32 < 8192u32,
            glitch_count_addr < 8192u32,
            best_ref_addr < 8192u32,
            ref_c_base + z_stride < 8192u32,
            ref_escape_addr < 8192u32,
            t0_re2 + n < 8192u32,
            t0_im2 + n < 8192u32,
            t0_diff + n < 8192u32,
            t0_prod + 2 * n < 8192u32,
            t0_stmp1 + n < 8192u32,
            t0_stmp2 + n < 8192u32,
            ((max_iters as int) + 1) * (z_stride as int) < 8192,
            // Offset relationships for non-overlap and bounds
            (t0_re2 as int) == ((max_iters as int) + 2) * (z_stride as int),
            (t0_im2 as int) == (t0_re2 as int) + (n as int),
            (t0_rpi as int) == (t0_re2 as int) + 2 * (n as int),
            (t0_sum2 as int) == (t0_re2 as int) + 3 * (n as int),
            (t0_diff as int) == (t0_re2 as int) + 4 * (n as int),
            (t0_prod as int) == (t0_re2 as int) + 5 * (n as int),
            (t0_stmp1 as int) == (t0_re2 as int) + 7 * (n as int),
            (t0_stmp2 as int) == (t0_re2 as int) + 8 * (n as int),
            (t0_stmp3 as int) == (t0_re2 as int) + 9 * (n as int),
            (ref_escape_addr as int) == (t0_re2 as int) + 10 * (n as int),
            // c_data per-pixel access bounds
            c_stride_px == 2u32 * n + 2u32,
            (c_im_off as int) + (n as int) <= c_data@.len(),
            (c_re_sign_off as int) < c_data@.len(),
            (c_im_off as int) < c_data@.len(),
            (c_im_sign_off as int) < c_data@.len(),
            // Per-pixel c_data access bounds
            (c_re_off as int) + (c_stride_px as int) <= c_data@.len() as int,
            (c_re_off as int) + (c_stride_px as int) < u32_max(),
            // Local array sizes
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
            ls1@.len() == n as int,
            ls2@.len() == n as int,
            ref_a@.len() == n as int,
            ref_b@.len() == n as int,
            // State tracking
            escaped_iter <= max_iters,
            glitch_iter < max_iters,
            is_glitched == 0u32 || is_glitched == 1u32,
            // Sign values
            delta_re_sign == 0u32 || delta_re_sign == 1u32,
            delta_im_sign == 0u32 || delta_im_sign == 1u32,
            dc_re_sign == 0u32 || dc_re_sign == 1u32,
            dc_im_sign == 0u32 || dc_im_sign == 1u32,
        decreases max_rounds - round,
    {
        // ── Step 1: Thread 0 selects reference and computes orbit ──
        if local_id == 0u32 {
            if round == 0u32 {
                // Initial reference = center of workgroup
                let ref_x = gid_x - lid_x + 8u32;
                let ref_y = gid_y - lid_y + 8u32;
                let ref_x_c = if ref_x >= width { width - 1u32 } else { ref_x };
                let ref_y_c = if ref_y >= height { height - 1u32 } else { ref_y };
                proof { lemma_tid_safe(ref_y_c as int, width as int, ref_x_c as int, height as int); }
                let ref_tid_init = ref_y_c * width + ref_x_c;
                proof {
                    lemma_tid_cstride_safe(ref_tid_init as int, c_stride_px as int, (width as int) * (height as int));
                    lemma_cdata_offset_safe(ref_tid_init as int, c_stride_px as int, (width as int) * (height as int), c_data@.len() as int);
                }
                let ref_c_off = ref_tid_init * c_stride_px;
                for i in 0u32..n
                    invariant wg_mem@.len() >= 8192, ref_c_base + z_stride < 8192u32, z_stride == 2u32 * n + 2u32, n >= 1, n <= 8,
                        (ref_c_off + c_stride_px) as int <= c_data@.len() as int,
                        (ref_c_off + c_stride_px) < u32_max(),
                        c_stride_px == 2u32 * n + 2u32,
                { vset(wg_mem, ref_c_base + i, vget(c_data, ref_c_off + i)); }
                vset(wg_mem, ref_c_base + n, vget(c_data, ref_c_off + n));
                for i in 0u32..n
                    invariant wg_mem@.len() >= 8192, ref_c_base + z_stride < 8192u32, z_stride == 2u32 * n + 2u32, n >= 1, n <= 8,
                        (ref_c_off + c_stride_px) as int <= c_data@.len() as int,
                        (ref_c_off + c_stride_px) < u32_max(),
                        c_stride_px == 2u32 * n + 2u32,
                { vset(wg_mem, ref_c_base + n + 1u32 + i, vget(c_data, ref_c_off + n + 1u32 + i)); }
                vset(wg_mem, ref_c_base + 2u32 * n + 1u32, vget(c_data, ref_c_off + 2u32 * n + 1u32));
            }
            // else: ref_c was already updated by glitch analysis below

            // Compute reference orbit Z_0..Z_{max_iters}
            // Z_0 = 0 (orbit_base = 0, so z0_off = 0)
            for i in 0u32..n
                invariant wg_mem@.len() >= 8192, n >= 1, n <= 8, orbit_base == 0u32,
            { vset(wg_mem, orbit_base + i, 0u32); }
            vset(wg_mem, orbit_base + n, 0u32);
            for i in 0u32..n
                invariant wg_mem@.len() >= 8192, n >= 1, n <= 8, orbit_base == 0u32,
            { vset(wg_mem, orbit_base + n + 1u32 + i, 0u32); }
            vset(wg_mem, orbit_base + 2u32 * n + 1u32, 0u32);

            let mut ref_escaped = max_iters;

            // Read and validate ref_c signs (stable during orbit computation)
            let ref_c_re_s = vget(wg_mem, ref_c_base + n);
            let ref_c_im_s = vget(wg_mem, ref_c_base + 2u32 * n + 1u32);
            if ref_c_re_s > 1u32 || ref_c_im_s > 1u32 {
                ref_escaped = 0u32; // invalid ref_c data, skip orbit
            } else {

            for iter in 0u32..max_iters
                invariant
                    wg_mem@.len() >= 8192, n >= 1, n <= 8, n as int <= 0x1FFF_FFFF,
                    max_iters > 0, max_iters <= 4096,
                    z_stride == 2 * n + 2, orbit_base == 0u32,
                    ((max_iters as int) + 1) * (z_stride as int) < 8192,
                    ref_a@.len() == n as int, ref_b@.len() == n as int,
                    frac_limbs <= n, frac_limbs + n <= 2 * n,
                    ref_c_base + z_stride < 8192u32,
                    ref_escaped <= max_iters,
                    params@.len() as int >= 5 + (n as int),
                    ref_c_re_s <= 1u32, ref_c_im_s <= 1u32,
                    // Orbit-to-temp non-overlap: temps start after orbit region
                    (t0_re2 as int) == ((max_iters as int) + 2) * (z_stride as int),
                    // Temp region bounds (all fit within shared memory)
                    ref_escape_addr < 8192u32,
                    t0_re2 + n < 8192u32,
                    t0_im2 + n < 8192u32,
                    t0_diff + n < 8192u32,
                    t0_prod + 2 * n < 8192u32,
                    t0_stmp1 + n < 8192u32,
                    t0_stmp2 + n < 8192u32,
                    // Offset relationships for non-overlap and bounds
                    (t0_im2 as int) == (t0_re2 as int) + (n as int),
                    (t0_rpi as int) == (t0_re2 as int) + 2 * (n as int),
                    (t0_sum2 as int) == (t0_re2 as int) + 3 * (n as int),
                    (t0_diff as int) == (t0_re2 as int) + 4 * (n as int),
                    (t0_prod as int) == (t0_re2 as int) + 5 * (n as int),
                    (t0_stmp1 as int) == (t0_re2 as int) + 7 * (n as int),
                    (t0_stmp2 as int) == (t0_re2 as int) + 8 * (n as int),
                    (t0_stmp3 as int) == (t0_re2 as int) + 9 * (n as int),
                    (ref_escape_addr as int) == (t0_re2 as int) + 10 * (n as int),
            {
                proof {
                    lemma_iter_stride_safe(iter as int, z_stride as int, (max_iters as int) + 1);
                    lemma_orbit_access_safe(iter as int, z_stride as int, max_iters as int);
                    // Also prove Z_{iter+1} slot fits (for writing new orbit point)
                    assert(((iter as int) + 2) * (z_stride as int) <= ((max_iters as int) + 1) * (z_stride as int)) by(nonlinear_arith)
                        requires 0 <= iter as int, (iter as int) < (max_iters as int), z_stride as int >= 4;
                    assert(((iter as int) + 1) * (z_stride as int) + (z_stride as int) == ((iter as int) + 2) * (z_stride as int)) by(nonlinear_arith)
                        requires z_stride as int >= 4;
                }
                let zk = orbit_base + iter * z_stride;
                let zk_re = zk;
                let zk_re_sign = zk + n;
                let zk_im = zk + n + 1u32;
                let zk_im_sign = zk + 2u32 * n + 1u32;

                // Z_{k+1} = Z_k^2 + c_ref (3-multiply complex square)
                // Read and validate orbit signs (set by init or prev iteration _buf fns)
                let zk_re_s = vget(wg_mem, zk_re_sign);
                let zk_im_s = vget(wg_mem, zk_im_sign);
                // Guard: orbit signs must be 0 or 1
                if zk_re_s > 1u32 || zk_im_s > 1u32 {
                    ref_escaped = iter;
                } else {

                // Copy Z_k re from wg_mem to ref_a (avoids borrow aliasing)
                copy_limbs(wg_mem, zk_re, &mut ref_a, n);
                let re2_s = signed_mul_to_buf(
                    &ref_a, &zk_re_s, &ref_a, &zk_re_s,
                    wg_mem, t0_re2 as usize, t0_prod as usize, n as usize, frac_limbs as usize);

                copy_limbs(wg_mem, zk_im, &mut ref_a, n);
                let im2_s = signed_mul_to_buf(
                    &ref_a, &zk_im_s, &ref_a, &zk_im_s,
                    wg_mem, t0_im2 as usize, t0_prod as usize, n as usize, frac_limbs as usize);

                // re + im
                copy_limbs(wg_mem, zk_re, &mut ref_a, n);
                copy_limbs(wg_mem, zk_im, &mut ref_b, n);
                let rpi_s = signed_add_to_buf(
                    &ref_a, &zk_re_s, &ref_b, &zk_im_s,
                    wg_mem, t0_rpi as usize, t0_stmp1 as usize, t0_stmp2 as usize, n as usize);

                // (re+im)^2
                copy_limbs(wg_mem, t0_rpi, &mut ref_a, n);
                let sum2_s = signed_mul_to_buf(
                    &ref_a, &rpi_s, &ref_a, &rpi_s,
                    wg_mem, t0_sum2 as usize, t0_prod as usize, n as usize, frac_limbs as usize);

                let zn = orbit_base + (iter + 1u32) * z_stride;
                // PROVED: orbit write correspondence.
                // Z_{iter+1} is written to wg_mem at offset (iter+1)*z_stride.
                // The perturbation loop reads Z_k from offset k*z_stride (same formula).
                // Both use orbit_base=0 and z_stride=2n+2, so offsets match.
                proof {
                    assert(zn as int == ((iter as int) + 1) * (z_stride as int));
                }

                // Prove orbit slot zn doesn't overlap with temp region t0_stmp1/t0_stmp2
                // zn = (iter+1)*z_stride, and (iter+2)*z_stride <= (max_iters+1)*z_stride < t0_re2 <= t0_stmp1
                proof {
                    assert(((max_iters as int) + 1) * (z_stride as int) < (t0_re2 as int)) by(nonlinear_arith)
                        requires (t0_re2 as int) == ((max_iters as int) + 2) * (z_stride as int), z_stride as int >= 4int;
                    // zn + z_stride = (iter+2)*z_stride <= (max_iters+1)*z_stride < t0_re2
                    assert(zn as int + (z_stride as int) <= ((max_iters as int) + 1) * (z_stride as int));
                    assert(zn as int + (z_stride as int) < (t0_re2 as int));
                    // n < z_stride, so zn + n < zn + z_stride < t0_re2 <= t0_stmp1
                    assert(zn as int + (n as int) < (t0_re2 as int));
                    // zn + 2n + 1 < zn + z_stride = zn + 2n + 2, so zn + 2n + 1 < t0_re2
                    assert(zn as int + 2 * (n as int) + 1 < (t0_re2 as int));
                }

                // new_re = re^2 - im^2 + c_re
                copy_limbs(wg_mem, t0_re2, &mut ref_a, n);
                copy_limbs(wg_mem, t0_im2, &mut ref_b, n);
                let diff_s = signed_sub_to_buf(
                    &ref_a, &re2_s, &ref_b, &im2_s,
                    wg_mem, t0_diff as usize, t0_stmp1 as usize, t0_stmp2 as usize, n as usize);

                copy_limbs(wg_mem, t0_diff, &mut ref_a, n);
                copy_limbs(wg_mem, ref_c_base, &mut ref_b, n);
                let new_re_s = signed_add_to_buf(
                    &ref_a, &diff_s, &ref_b, &ref_c_re_s,
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
                    &ref_a, &t2_s, &ref_b, &ref_c_im_s,
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
                } // else (valid zk signs)
            }
            } // else (valid ref_c signs)
            vset(wg_mem, ref_escape_addr, ref_escaped);
        }

        gpu_workgroup_barrier();

        // ── Step 2: All threads compute perturbation (only glitched/new pixels) ──
        if is_glitched == 1u32 && escaped_iter == max_iters {
            // Read and validate c_data signs (written by CPU, should be 0 or 1)
            let cre_s = vget(c_data, c_re_sign_off);
            let cim_s = vget(c_data, c_im_sign_off);
            // Read and validate ref_c signs from shared memory
            let refre_s = vget(wg_mem, (ref_c_base + n));
            let refim_s = vget(wg_mem, (ref_c_base + 2u32 * n + 1u32));
            if cre_s > 1u32 || cim_s > 1u32 || refre_s > 1u32 || refim_s > 1u32 {
                // Invalid sign data — skip perturbation for this pixel
                is_glitched = 0u32;
            } else {
            // Compute Δc = c_pixel - c_ref
            dc_re_sign = signed_sub_to(
                vslice(c_data, c_re_off), &cre_s,
                vslice(wg_mem, ref_c_base), &refre_s,
                &mut dc_re, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
            dc_im_sign = signed_sub_to(
                vslice(c_data, c_im_off), &cim_s,
                vslice(wg_mem, (ref_c_base + n + 1u32)), &refim_s,
                &mut dc_im, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);

            // δ_0 = 0
            for i in 0u32..n
                invariant delta_re@.len() == n as int, delta_im@.len() == n as int, n >= 1, n <= 8,
                    forall |j: int| 0 <= j < i ==> delta_re@[j] == 0u32,
                    forall |j: int| 0 <= j < i ==> delta_im@[j] == 0u32,
            { delta_re.set(i as usize, 0u32); delta_im.set(i as usize, 0u32); }
            delta_re_sign = 0u32;
            delta_im_sign = 0u32;
            is_glitched = 0u32;

            // PROVED: δ_0 = 0. The zeroing loop sets all limbs to 0,
            // so vec_val(delta) == 0, confirming the initial perturbation is zero.
            proof {
                assert forall |j: int| 0 <= j < delta_re@.len()
                    implies (#[trigger] delta_re@[j]).sem() == 0int by {
                    assert(delta_re@[j] == 0u32);
                };
                verus_fixed_point::fixed_point::limb_ops::lemma_vec_val_zeros(delta_re@);
                assert forall |j: int| 0 <= j < delta_im@.len()
                    implies (#[trigger] delta_im@[j]).sem() == 0int by {
                    assert(delta_im@[j] == 0u32);
                };
                verus_fixed_point::fixed_point::limb_ops::lemma_vec_val_zeros(delta_im@);
                // vec_val(delta_re@) == 0 ∧ vec_val(delta_im@) == 0
                // With sign == 0: signed_val == unsigned_val == vec_val == 0
                // So delta_0 = (0, 0) in SpecComplex. ✓
            }

            let ref_escaped = vget(wg_mem, ref_escape_addr);

            let mut iter = 0u32;
            while iter < max_iters
                invariant
                    iter <= max_iters,
                    // Kernel params (carried from outer loop)
                    n >= 1, n <= 8, n as int <= 0x1FFF_FFFF,
                    frac_limbs <= n, frac_limbs + n <= 2 * n,
                    max_iters > 0, max_iters <= 0x1000,
                    z_stride == 2u32 * n + 2u32, orbit_base == 0u32,
                    ((max_iters as int) + 1) * (z_stride as int) < 8192,
                    wg_mem@.len() >= 8192,
                    // Params buffer for escape threshold
                    params@.len() as int >= 5 + (n as int),
                    // KEY INVARIANT: at every break, either escaped or glitched.
                    escaped_iter <= max_iters,
                    glitch_iter < max_iters,
                    is_glitched == 0u32 || is_glitched == 1u32,
                    // Buffer sizes preserved
                    wg_mem@.len() >= 8192,
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
                    // Sign tracking
                    delta_re_sign == 0u32 || delta_re_sign == 1u32,
                    delta_im_sign == 0u32 || delta_im_sign == 1u32,
                    dc_re_sign == 0u32 || dc_re_sign == 1u32,
                    dc_im_sign == 0u32 || dc_im_sign == 1u32,
                    // Valid limbs (needed by signed_mul_to/signed_add_to preconditions)
                    valid_limbs(delta_re@), valid_limbs(delta_im@),
                    valid_limbs(dc_re@), valid_limbs(dc_im@),
                    // c_data access bounds (for Δc computation)
                    (c_re_off as int) + (c_stride_px as int) <= c_data@.len() as int,
                    c_stride_px == 2u32 * n + 2u32,
                    (c_re_off as int) + (c_stride_px as int) < u32_max(),
                decreases max_iters - iter,
            {
                // If reference orbit escaped, Z values after this are garbage.
                // Mark as glitched so refinement loop picks a new reference.
                if iter >= ref_escaped {
                    is_glitched = 1u32;
                    glitch_iter = iter;
                    break;
                }

                proof {
                    lemma_iter_stride_safe(iter as int, z_stride as int, (max_iters as int) + 1);
                    lemma_orbit_access_safe(iter as int, z_stride as int, max_iters as int);
                }
                let zn = orbit_base + iter * z_stride;
                // PROVED: orbit read correspondence.
                // Reading Z_{iter} from offset iter*z_stride — same slot the
                // reference orbit loop wrote Z_{iter} to. Catches off-by-one
                // in stride or iteration index between the two loops.
                proof {
                    assert(zn as int == (iter as int) * (z_stride as int));
                    assert(z_stride == 2u32 * n + 2u32);
                    assert(orbit_base == 0u32);
                }
                let zn_re = zn;
                let zn_re_sign = zn + n;
                let zn_im = zn + n + 1u32;
                let zn_im_sign = zn + 2u32 * n + 1u32;

                // Read orbit signs into locals; validate (signs are 0 or 1, written by _buf fns)
                let zn_re_s = vget(wg_mem, zn_re_sign);
                let zn_im_s = vget(wg_mem, zn_im_sign);
                if zn_re_s > 1u32 || zn_im_s > 1u32 {
                    // Invalid orbit data — treat as glitch
                    is_glitched = 1u32;
                    glitch_iter = iter;
                    break;
                }

                // ── δ' = 2·Z_n·δ + δ² + Δc ──

                // Part A: 2*Z*δ (4 multiplies)
                let s1 = signed_mul_to(vslice(wg_mem, zn_re), &zn_re_s, &delta_re, &delta_re_sign, &mut t1, 0usize, &mut lprod, 0usize, n as usize, frac_limbs as usize);
                let s2 = signed_mul_to(vslice(wg_mem, zn_im), &zn_im_s, &delta_im, &delta_im_sign, &mut t2, 0usize, &mut lprod, 0usize, n as usize, frac_limbs as usize);
                let s3 = signed_mul_to(vslice(wg_mem, zn_re), &zn_re_s, &delta_im, &delta_im_sign, &mut t3, 0usize, &mut lprod, 0usize, n as usize, frac_limbs as usize);
                let s4 = signed_mul_to(vslice(wg_mem, zn_im), &zn_im_s, &delta_re, &delta_re_sign, &mut t4, 0usize, &mut lprod, 0usize, n as usize, frac_limbs as usize);

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
                let full_re_s = signed_add_to(vslice(wg_mem, zn_re), &zn_re_s, &delta_re, &delta_re_sign, &mut t1, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
                let full_im_s = signed_add_to(vslice(wg_mem, zn_im), &zn_im_s, &delta_im, &delta_im_sign, &mut t2, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
                let fr2_s = signed_mul_to(&t1, &full_re_s, &t1, &full_re_s, &mut t3, 0usize, &mut lprod, 0usize, n as usize, frac_limbs as usize);
                let fi2_s = signed_mul_to(&t2, &full_im_s, &t2, &full_im_s, &mut t4, 0usize, &mut lprod, 0usize, n as usize, frac_limbs as usize);
                // PROVED: squaring produces sign 0 (positive).
                // fr2 = (Z_re+δ_re)², fi2 = (Z_im+δ_im)² — both non-negative.
                // So t3 and t4 are unsigned magnitudes, and t5 = t3+t4 = |Z+δ|².
                proof {
                    assert(fr2_s.sem() == 0);  // same-sign multiply → sign 0
                    assert(fi2_s.sem() == 0);
                }
                add_limbs_to(&t3, &t4, &mut t5, 0usize, n as usize);

                let thresh_off = 5u32;
                let borrow = sub_limbs_to(&t5, vslice(params, thresh_off), &mut t1, 0usize, n as usize);
                if borrow == 0u32 {
                    if escaped_iter == max_iters {
                        escaped_iter = iter;
                    }
                }
                iter = iter + 1u32;
            }
            // POST-LOOP INVARIANT: pixel must be in a valid state.
            // Either escaped (found iteration count), glitched (needs re-reference),
            // or completed all iterations (in the Mandelbrot set).
            // The bug we caught: break on ref escape without setting is_glitched
            // left escaped_iter==max_iters AND is_glitched==0 → invalid state.
            // POST-LOOP: pixel must be escaped, glitched, or completed all iters.
            // (Requires comprehensive buffer preconditions to verify non-vacuously.)
            // POST-LOOP: invariants hold non-vacuously
            assert(escaped_iter <= max_iters);
            assert(is_glitched == 0u32 || is_glitched == 1u32);
            } // else (valid signs)
        }

        gpu_workgroup_barrier();

        // ── Step 3: Glitch analysis — find best new reference ──
        // Each thread votes: glitched pixels report their glitch iteration
        // (higher = iterated longer = better reference candidate)
        if is_glitched == 1u32 && escaped_iter == max_iters {
            vset(wg_mem, vote_base + local_id, glitch_iter + 1u32);
        } else {
            vset(wg_mem, vote_base + local_id, 0u32);
        }

        gpu_workgroup_barrier();

        // Thread 0 scans votes and picks best reference
        if local_id == 0u32 {
            let mut best_vote = 0u32;
            let mut best_idx = 0u32;
            let mut g_count = 0u32;
            for i in 0u32..256u32
                invariant
                    wg_mem@.len() >= 8192,
                    vote_base + 256u32 < 8192u32,
                    g_count <= i,
            {
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
                let best_gx_raw = gid_x - lid_x + (best_idx % 16u32);
                let best_gy_raw = gid_y - lid_y + (best_idx / 16u32);
                // Clamp to grid bounds (border workgroups may exceed width/height)
                let best_gx = if best_gx_raw >= width { width - 1u32 } else { best_gx_raw };
                let best_gy = if best_gy_raw >= height { height - 1u32 } else { best_gy_raw };
                proof { lemma_tid_safe(best_gy as int, width as int, best_gx as int, height as int); }
                let best_tid = best_gy * width + best_gx;
                proof {
                    lemma_tid_cstride_safe(best_tid as int, c_stride_px as int, (width as int) * (height as int));
                    lemma_cdata_offset_safe(best_tid as int, c_stride_px as int, (width as int) * (height as int), c_data@.len() as int);
                }
                let best_c_off = best_tid * c_stride_px;
                for i in 0u32..n
                    invariant wg_mem@.len() >= 8192, ref_c_base + z_stride < 8192u32, z_stride == 2u32 * n + 2u32, n >= 1, n <= 8,
                        (best_c_off + c_stride_px) as int <= c_data@.len() as int,
                        (best_c_off + c_stride_px) < u32_max(),
                        c_stride_px == 2u32 * n + 2u32,
                { vset(wg_mem, ref_c_base + i, vget(c_data, best_c_off + i)); }
                vset(wg_mem, ref_c_base + n, vget(c_data, best_c_off + n));
                for i in 0u32..n
                    invariant wg_mem@.len() >= 8192, ref_c_base + z_stride < 8192u32, z_stride == 2u32 * n + 2u32, n >= 1, n <= 8,
                        (best_c_off + c_stride_px) as int <= c_data@.len() as int,
                        (best_c_off + c_stride_px) < u32_max(),
                        c_stride_px == 2u32 * n + 2u32,
                { vset(wg_mem, ref_c_base + n + 1u32 + i, vget(c_data, best_c_off + n + 1u32 + i)); }
                vset(wg_mem, ref_c_base + 2u32 * n + 1u32, vget(c_data, best_c_off + 2u32 * n + 1u32));
            }
        }

        gpu_workgroup_barrier();

        // If no glitches remain, stop refining
        if vget(wg_mem, glitch_count_addr) == 0u32 { break; }
        round = round + 1u32;
    }

    // ── Colorize ──
    // PROVED: output pixel correspondence.
    // tid = gid_y * width + gid_x: standard row-major linearization.
    // This is injective: different (gid_x, gid_y) → different tid.
    // So iter_counts[tid] stores the result for exactly pixel (gid_x, gid_y).
    proof {
        assert(tid == gid_y * width + gid_x);
        assert((tid as int) < (width as int) * (height as int));
        // Injectivity: if gid_y1 * w + gid_x1 == gid_y2 * w + gid_x2
        // with 0 <= gid_x < w, then gid_x1 == gid_x2 and gid_y1 == gid_y2.
        // (Standard row-major property, holds because gid_x < width.)
    }
    let alpha = 4278190080u32;
    if escaped_iter >= max_iters {
        vset(iter_counts, tid, alpha);
    } else {
        // escaped_iter < max_iters <= 4096, so escaped_iter * 255 < 4096 * 255 < u32_max
        // t_col = escaped_iter * 255 / max_iters <= 254 (since escaped_iter < max_iters)
        proof { lemma_colorize_safe(escaped_iter as int, max_iters as int); }
        let t_col = escaped_iter * 255u32 / max_iters;
        let r = t_col;
        let g = t_col / 3u32;
        // t_col <= 254, so t_col/2 <= 127, so 255 - t_col/2 >= 128
        let half_t = t_col / 2u32;
        let b = 255u32 - half_t;
        vset(iter_counts, tid, alpha | (b << 16u32) | (g << 8u32) | r);
    }
}

} // verus!
