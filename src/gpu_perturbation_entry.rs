/// GPU Mandelbrot kernel with perturbation theory.
/// VERIFIED by Verus AND transpiled to WGSL.
///
/// To regenerate the WGSL shader from this verified source:
///   cd verus-gpu-parser
///   cargo run --release --bin verus-gpu-transpile -- \
///     ../verus-mandelbrot/src/gpu_perturbation_entry.rs \
///     -o ../verus-mandelbrot/web/mandelbrot_perturbation.wgsl
///
/// Architecture: each 16x16 workgroup:
/// 1. Thread 0 computes reference orbit Z_0..Z_N in workgroup shared memory
/// 2. workgroupBarrier()
/// 3. All 256 threads compute perturbation delta using local arrays

use vstd::prelude::*;
use vstd::slice::SliceAdditionalExecFns;
use verus_fixed_point::fixed_point::limb_ops::*;
#[cfg(verus_keep_ghost)]
use verus_fixed_point::fixed_point::limb_ops_proofs::signed_val_of;
#[cfg(verus_keep_ghost)]
use crate::gpu_perturbation_proofs::{
    pert_step_buf_int, ref_step_buf_int,
    signed_mul_buf, signed_add_buf, signed_sub_buf,
    lemma_signed_mul_postcond_to_buf,
    lemma_disjunction_to_signed_add_buf,
    lemma_disjunction_to_signed_sub_buf,
    lemma_ref_orbit_chain,
    lemma_pointwise_to_valid_limbs,
};

verus! {

/// PROOF (#76): glitch detection completeness for one component.
/// If vec_val(δ_full) >= 4 * BASE^(n-1), then the top limb is > 3.
/// This means the kernel's `δ[n-1] > 3` check will fire — i.e., the
/// glitch detection catches all "value too large" overflows.
proof fn lemma_glitch_completeness_one(delta: Seq<u32>, n: nat)
    requires
        n >= 1,
        delta.len() == n as int,
        valid_limbs(delta),
    ensures
        vec_val(delta) >= 4 * limb_power((n - 1) as nat)
            ==> delta[(n - 1) as int].sem() > 3,
{
    let s_top = limb_power((n - 1) as nat);
    let dre_lo = delta.subrange(0, (n - 1) as int);

    assert(valid_limbs(dre_lo)) by {
        assert forall |k: int| 0 <= k < dre_lo.len()
            implies 0 <= (#[trigger] dre_lo[k]).sem()
                && dre_lo[k].sem() < LIMB_BASE() by {
            assert(dre_lo[k] == delta[k]);
        }
    }
    lemma_vec_val_split::<u32>(delta, (n - 1) as nat);
    let lo_v = vec_val(dre_lo);
    let top_v = delta[(n - 1) as int].sem();
    let hi_seq = delta.subrange((n - 1) as int, n as int);
    assert(hi_seq.len() == 1);
    assert(hi_seq[0] == delta[(n - 1) as int]);
    reveal_with_fuel(limbs_val, 2);
    assert(sem_seq(hi_seq).len() == 1);
    assert(sem_seq(hi_seq)[0] == top_v);
    assert(sem_seq(hi_seq).subrange(1, 1) =~= Seq::<int>::empty());
    assert(vec_val(hi_seq) == top_v);
    assert(vec_val(delta) == lo_v + top_v * s_top);
    lemma_vec_val_bounded::<u32>(dre_lo);
    assert(lo_v < s_top);
    assert(s_top > 0) by { reveal_with_fuel(limb_power, 2); }

    if vec_val(delta) >= 4 * s_top {
        assert(top_v * s_top >= 4 * s_top - lo_v);
        assert(top_v * s_top > 3 * s_top) by(nonlinear_arith)
            requires top_v * s_top >= 4 * s_top - lo_v,
                     lo_v < s_top, s_top > 0;
        assert(top_v > 3) by(nonlinear_arith)
            requires top_v * s_top > 3 * s_top, s_top > 0;
    }
}

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

/// Count the number of positions in `mem[base..base+end]` that hold a
/// strictly-positive value. Used by the vote scan invariant to track
/// how many glitched-pixel votes have been seen so far.
spec fn count_positive(mem: Seq<u32>, base: int, end: int) -> nat
    decreases end,
{
    if end <= 0 {
        0nat
    } else if mem[base + end - 1] > 0u32 {
        count_positive(mem, base, end - 1) + 1
    } else {
        count_positive(mem, base, end - 1)
    }
}

/// Maximum of `mem[base..base+end]`, treating the empty prefix as 0.
/// Used by the vote scan invariant to characterise `best_vote`.
spec fn max_prefix(mem: Seq<u32>, base: int, end: int) -> u32
    decreases end,
{
    if end <= 0 {
        0u32
    } else {
        let prev = max_prefix(mem, base, end - 1);
        let here = mem[base + end - 1];
        if here > prev { here } else { prev }
    }
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

// ═══════════════════════════════════════════════════════════════
// Coloring invariants
// ═══════════════════════════════════════════════════════════════

/// Row-major linearization `tid = gy * w + gx` is injective on
/// `0 <= gx < w` and `0 <= gy`. Guarantees each pixel writes to a
/// unique `iter_counts[tid]` slot, so no two threads clobber each other.
proof fn lemma_tid_injective(gy1: int, gx1: int, gy2: int, gx2: int, w: int)
    requires
        w > 0,
        0 <= gx1, gx1 < w,
        0 <= gx2, gx2 < w,
        0 <= gy1,
        0 <= gy2,
        gy1 * w + gx1 == gy2 * w + gx2,
    ensures
        gx1 == gx2,
        gy1 == gy2,
{
    // gy1 * w + gx1 == gy2 * w + gx2
    // (gy1 - gy2) * w == gx2 - gx1
    // |gx2 - gx1| < w, so (gy1 - gy2) * w must also satisfy |.| < w
    // The only multiple of w with |.| < w is 0, so gy1 == gy2, then gx1 == gx2.
    assert((gy1 - gy2) * w == gx2 - gx1) by(nonlinear_arith)
        requires gy1 * w + gx1 == gy2 * w + gx2;
    assert(-w < gx2 - gx1 && gx2 - gx1 < w)
        by(nonlinear_arith)
        requires 0 <= gx1, gx1 < w, 0 <= gx2, gx2 < w;
    if gy1 != gy2 {
        if gy1 > gy2 {
            assert(gy1 - gy2 >= 1);
            assert((gy1 - gy2) * w >= w) by(nonlinear_arith)
                requires gy1 - gy2 >= 1, w > 0;
            assert(false);
        } else {
            assert(gy2 - gy1 >= 1);
            assert((gy2 - gy1) * w >= w) by(nonlinear_arith)
                requires gy2 - gy1 >= 1, w > 0;
            assert((gy1 - gy2) * w <= -w) by(nonlinear_arith)
                requires (gy2 - gy1) * w >= w;
            assert(false);
        }
    }
    assert(gy1 == gy2);
}

/// Per-channel bounds: each of `r`, `g`, `b` fits in an 8-bit slot and
/// `b` has the documented minimum of 128.
///
/// Catches bugs where the coloring formula is retuned (e.g. swapping
/// `r = t_col` for `r = 256 - t_col` wrap-around) or where `half_t`
/// accidentally exceeds 127.
proof fn lemma_colorize_channels_bounded(escaped_iter: int, max_iters: int)
    requires
        0 <= escaped_iter, escaped_iter < max_iters,
        max_iters > 0, max_iters <= 4096,
    ensures
        ({
            let t_col = (escaped_iter * 255) / max_iters;
            let half_t = t_col / 2;
            let r = t_col;
            let g = t_col / 3;
            let b = 255 - half_t;
            &&& 0 <= r && r < 256
            &&& 0 <= g && g < 256
            &&& 128 <= b && b < 256
        }),
{
    lemma_colorize_safe(escaped_iter, max_iters);
    let t_col = (escaped_iter * 255) / max_iters;
    // t_col >= 0 because escaped_iter * 255 >= 0 and max_iters > 0.
    assert(escaped_iter * 255 >= 0) by(nonlinear_arith)
        requires escaped_iter >= 0;
    assert(t_col >= 0) by(nonlinear_arith)
        requires t_col == (escaped_iter * 255) / max_iters,
                 escaped_iter * 255 >= 0, max_iters > 0;
    // t_col <= 254 from lemma_colorize_safe.
    // r = t_col → 0 <= r < 256.
    // g = t_col / 3 >= 0, and g <= t_col <= 254 < 256.
    assert(t_col / 3 >= 0) by(nonlinear_arith) requires t_col >= 0;
    assert(t_col / 3 <= t_col) by(nonlinear_arith) requires t_col >= 0;
    // half_t = t_col / 2, 0 <= half_t <= 127.
    let half_t = t_col / 2;
    assert(half_t >= 0) by(nonlinear_arith) requires half_t == t_col / 2, t_col >= 0;
    // b = 255 - half_t, so 128 <= b <= 255 < 256.
}

/// Monotonicity: r (the red channel) is a non-decreasing function of
/// `escaped_iter`. So "pixel escaped later" never yields a less-red color.
///
/// Catches off-by-one bugs where the formula e.g. computes `255 - t_col`.
proof fn lemma_colorize_r_monotonic(e1: int, e2: int, max_iters: int)
    requires
        0 <= e1, e1 <= e2, e2 < max_iters,
        max_iters > 0, max_iters <= 4096,
    ensures
        (e1 * 255) / max_iters <= (e2 * 255) / max_iters,
{
    assert(e1 * 255 <= e2 * 255) by(nonlinear_arith) requires e1 <= e2;
    // Integer division is monotonic in the numerator for positive divisor.
    assert((e1 * 255) / max_iters <= (e2 * 255) / max_iters) by(nonlinear_arith)
        requires e1 * 255 <= e2 * 255, max_iters > 0,
                 e1 * 255 >= 0, e2 * 255 >= 0, e1 >= 0;
}

/// Monotonicity (the other direction): b (the blue channel) is a
/// non-increasing function of `escaped_iter`. So "pixel escaped later"
/// never yields a more-blue color.
proof fn lemma_colorize_b_monotonic(e1: int, e2: int, max_iters: int)
    requires
        0 <= e1, e1 <= e2, e2 < max_iters,
        max_iters > 0, max_iters <= 4096,
    ensures
        255 - ((e1 * 255) / max_iters) / 2 >= 255 - ((e2 * 255) / max_iters) / 2,
{
    lemma_colorize_r_monotonic(e1, e2, max_iters);
    // t1 <= t2 ⇒ t1/2 <= t2/2 ⇒ 255 - t1/2 >= 255 - t2/2.
    let t1 = (e1 * 255) / max_iters;
    let t2 = (e2 * 255) / max_iters;
    assert(t1 <= t2);
    assert(t1 / 2 <= t2 / 2) by(nonlinear_arith) requires t1 <= t2, t1 >= 0, t2 >= 0;
    assert(e1 * 255 >= 0) by(nonlinear_arith) requires e1 >= 0;
    assert(e2 * 255 >= 0) by(nonlinear_arith) requires e2 >= 0;
    assert(t1 >= 0) by(nonlinear_arith)
        requires t1 == (e1 * 255) / max_iters, e1 * 255 >= 0, max_iters > 0;
    assert(t2 >= 0) by(nonlinear_arith)
        requires t2 == (e2 * 255) / max_iters, e2 * 255 >= 0, max_iters > 0;
}

/// The alpha constant used in the colorize phase is exactly 0xFF000000 —
/// full alpha in the top byte with all RGB channels masked off.
///
/// Catches bugs where the constant is accidentally changed to something
/// that bleeds into the RGB channels, e.g. 0xFF7F7F7F (gray).
proof fn lemma_alpha_constant_valid()
    ensures
        4278190080u32 == 0xFF000000u32,
        4278190080u32 & 0x00FFFFFFu32 == 0u32,
{
    assert(4278190080u32 == 0xFF000000u32);
    assert(4278190080u32 & 0x00FFFFFFu32 == 0u32) by(bit_vector);
}

/// Packing the channels into the 32-bit pixel word doesn't overflow or
/// clobber: with the channel bounds from `lemma_colorize_channels_bounded`,
/// each of `r`, `g << 8`, `b << 16` fits in its assigned byte slot, and
/// `alpha = 0xFF000000` occupies only the top byte.
proof fn lemma_colorize_packing_safe(r: u32, g: u32, b: u32)
    requires
        r < 256,
        g < 256,
        b < 256,
    ensures
        // Each shifted component fits in its slot
        (g << 8u32) < 65536u32,
        (b << 16u32) < 16777216u32,
        // The OR doesn't overlap with alpha's top byte.
        (4278190080u32 | (b << 16u32) | (g << 8u32) | r) >> 24u32 == 255u32,
        // The red byte is recoverable from the packed word.
        (4278190080u32 | (b << 16u32) | (g << 8u32) | r) & 0xFFu32 == r,
{
    assert((g << 8u32) < 65536u32) by(bit_vector)
        requires g < 256u32;
    assert((b << 16u32) < 16777216u32) by(bit_vector)
        requires b < 256u32;
    assert((4278190080u32 | (b << 16u32) | (g << 8u32) | r) >> 24u32 == 255u32) by(bit_vector)
        requires r < 256u32, g < 256u32, b < 256u32;
    assert((4278190080u32 | (b << 16u32) | (g << 8u32) | r) & 0xFFu32 == r) by(bit_vector)
        requires r < 256u32, g < 256u32, b < 256u32;
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

/// One iteration of the perturbation step: δ' = 2*Z*δ + δ² + Δc.
///
/// Extracted from the perturbation while loop in `mandelbrot_perturbation`
/// (Task #81 Stage A) so that value-tracking ghost invariants (Task #78)
/// can be added inside a focused Z3 context, instead of polluting the
/// kernel function with ~30 buffer ops per iteration.
///
/// Stage B provides a value-equation postcondition: the output
/// `(delta_re, delta_im)` buffers, viewed as signed integers, equal
/// `pert_step_buf_int` applied to the input signed integer values.
/// rlimit bump: 500→700 due to ref_orbit sub-helpers added to module
/// (module-level context pollution, see rlimit tips anti-pattern).
#[verifier::rlimit(700)]
fn perturbation_iteration_step(
    z_re_slice: &[u32], z_re_sign: u32,
    z_im_slice: &[u32], z_im_sign: u32,
    delta_re: &mut Vec<u32>, delta_re_sign_in: u32,
    delta_im: &mut Vec<u32>, delta_im_sign_in: u32,
    dc_re: &Vec<u32>, dc_re_sign: u32,
    dc_im: &Vec<u32>, dc_im_sign: u32,
    t1: &mut Vec<u32>, t2: &mut Vec<u32>,
    t3: &mut Vec<u32>, t4: &mut Vec<u32>, t5: &mut Vec<u32>,
    lprod: &mut Vec<u32>,
    ls1: &mut Vec<u32>, ls2: &mut Vec<u32>,
    n: u32, frac_limbs: u32,
) -> (out: (u32, u32))
    requires
        n >= 1, n <= 8, n as int <= 0x1FFF_FFFF,
        frac_limbs <= n, frac_limbs + n <= 2 * n,
        // Sizes
        z_re_slice@.len() >= n as int,
        z_im_slice@.len() >= n as int,
        old(delta_re)@.len() == n as int,
        old(delta_im)@.len() == n as int,
        dc_re@.len() == n as int,
        dc_im@.len() == n as int,
        old(t1)@.len() == n as int,
        old(t2)@.len() == n as int,
        old(t3)@.len() == n as int,
        old(t4)@.len() == n as int,
        old(t5)@.len() == n as int,
        old(lprod)@.len() == 2 * n as int,
        old(ls1)@.len() == n as int,
        old(ls2)@.len() == n as int,
        // Sign validity
        z_re_sign == 0u32 || z_re_sign == 1u32,
        z_im_sign == 0u32 || z_im_sign == 1u32,
        delta_re_sign_in == 0u32 || delta_re_sign_in == 1u32,
        delta_im_sign_in == 0u32 || delta_im_sign_in == 1u32,
        dc_re_sign == 0u32 || dc_re_sign == 1u32,
        dc_im_sign == 0u32 || dc_im_sign == 1u32,
        // Valid limbs on inputs
        valid_limbs(z_re_slice@.subrange(0, n as int)),
        valid_limbs(z_im_slice@.subrange(0, n as int)),
        valid_limbs(old(delta_re)@),
        valid_limbs(old(delta_im)@),
        valid_limbs(dc_re@),
        valid_limbs(dc_im@),
    ensures
        // Sizes preserved
        delta_re@.len() == n as int,
        delta_im@.len() == n as int,
        t1@.len() == n as int,
        t2@.len() == n as int,
        t3@.len() == n as int,
        t4@.len() == n as int,
        t5@.len() == n as int,
        lprod@.len() == 2 * n as int,
        ls1@.len() == n as int,
        ls2@.len() == n as int,
        // Sign validity
        out.0 == 0u32 || out.0 == 1u32,
        out.1 == 0u32 || out.1 == 1u32,
        // Valid limbs preserved on outputs
        valid_limbs(delta_re@),
        valid_limbs(delta_im@),
        // Value equation: the output (δ_re, δ_im) signed integers equal
        // pert_step_buf_int applied to the input signed integers.
        ({
            let z_re_int = signed_val_of(z_re_slice@.subrange(0, n as int), z_re_sign as int);
            let z_im_int = signed_val_of(z_im_slice@.subrange(0, n as int), z_im_sign as int);
            let dre_in_int = signed_val_of(old(delta_re)@, delta_re_sign_in as int);
            let dim_in_int = signed_val_of(old(delta_im)@, delta_im_sign_in as int);
            let dcre_int = signed_val_of(dc_re@, dc_re_sign as int);
            let dcim_int = signed_val_of(dc_im@, dc_im_sign as int);
            let result = pert_step_buf_int(
                z_re_int, z_im_int,
                dre_in_int, dim_in_int,
                dcre_int, dcim_int,
                n as nat, frac_limbs as nat,
            );
            signed_val_of(delta_re@, out.0 as int) == result.0
            && signed_val_of(delta_im@, out.1 as int) == result.1
        }),
{
    let n_us = n as usize;
    let frac_us = frac_limbs as usize;

    // ── Capture input subranges + signed-int values ──
    let ghost z_re_seq = z_re_slice@.subrange(0, n as int);
    let ghost z_im_seq = z_im_slice@.subrange(0, n as int);
    let ghost dre_in_seq = delta_re@.subrange(0, n as int);
    let ghost dim_in_seq = delta_im@.subrange(0, n as int);
    let ghost dcre_seq = dc_re@.subrange(0, n as int);
    let ghost dcim_seq = dc_im@.subrange(0, n as int);
    proof {
        // Length-n inputs are equal to their subrange(0, n).
        assert(dre_in_seq =~= delta_re@);
        assert(dim_in_seq =~= delta_im@);
        assert(dcre_seq =~= dc_re@);
        assert(dcim_seq =~= dc_im@);
        // valid_limbs is preserved across this trivial subrange.
        assert(valid_limbs(dre_in_seq));
        assert(valid_limbs(dim_in_seq));
        assert(valid_limbs(dcre_seq));
        assert(valid_limbs(dcim_seq));
    }
    let ghost z_re_int = signed_val_of(z_re_seq, z_re_sign as int);
    let ghost z_im_int = signed_val_of(z_im_seq, z_im_sign as int);
    let ghost dre_in_int = signed_val_of(dre_in_seq, delta_re_sign_in as int);
    let ghost dim_in_int = signed_val_of(dim_in_seq, delta_im_sign_in as int);
    let ghost dcre_int = signed_val_of(dcre_seq, dc_re_sign as int);
    let ghost dcim_int = signed_val_of(dcim_seq, dc_im_sign as int);

    // ── Part A: 2*Z*δ (4 multiplies) ──
    let s1 = signed_mul_to(z_re_slice, &z_re_sign, &**delta_re, &delta_re_sign_in,
                           t1, 0usize, lprod, 0usize, n_us, frac_us);
    let ghost t1_seq_a = t1@.subrange(0, n as int);
    let ghost s1_int = signed_val_of(t1_seq_a, s1 as int);
    proof {
        lemma_signed_mul_postcond_to_buf::<u32>(
            z_re_seq, z_re_sign as int,
            dre_in_seq, delta_re_sign_in as int,
            t1_seq_a, s1 as int,
            n as nat, frac_limbs as nat,
        );
    }

    let s2 = signed_mul_to(z_im_slice, &z_im_sign, &**delta_im, &delta_im_sign_in,
                           t2, 0usize, lprod, 0usize, n_us, frac_us);
    let ghost t2_seq_a = t2@.subrange(0, n as int);
    let ghost s2_int = signed_val_of(t2_seq_a, s2 as int);
    proof {
        lemma_signed_mul_postcond_to_buf::<u32>(
            z_im_seq, z_im_sign as int,
            dim_in_seq, delta_im_sign_in as int,
            t2_seq_a, s2 as int,
            n as nat, frac_limbs as nat,
        );
    }

    let s3 = signed_mul_to(z_re_slice, &z_re_sign, &**delta_im, &delta_im_sign_in,
                           t3, 0usize, lprod, 0usize, n_us, frac_us);
    let ghost t3_seq_a = t3@.subrange(0, n as int);
    let ghost s3_int = signed_val_of(t3_seq_a, s3 as int);
    proof {
        lemma_signed_mul_postcond_to_buf::<u32>(
            z_re_seq, z_re_sign as int,
            dim_in_seq, delta_im_sign_in as int,
            t3_seq_a, s3 as int,
            n as nat, frac_limbs as nat,
        );
    }

    let s4 = signed_mul_to(z_im_slice, &z_im_sign, &**delta_re, &delta_re_sign_in,
                           t4, 0usize, lprod, 0usize, n_us, frac_us);
    let ghost t4_seq_a = t4@.subrange(0, n as int);
    let ghost s4_int = signed_val_of(t4_seq_a, s4 as int);
    proof {
        lemma_signed_mul_postcond_to_buf::<u32>(
            z_im_seq, z_im_sign as int,
            dre_in_seq, delta_re_sign_in as int,
            t4_seq_a, s4 as int,
            n as nat, frac_limbs as nat,
        );
    }

    // 2*Z*δ real = 2*(t1 - t2)
    let d1_s = signed_sub_to(&**t1, &s1, &**t2, &s2, t5, 0usize, ls1, 0usize, ls2, 0usize, n_us);
    let ghost t5_seq_d1 = t5@.subrange(0, n as int);
    let ghost d1_int = signed_val_of(t5_seq_d1, d1_s as int);
    proof {
        assert(t1@.subrange(0, n as int) == t1_seq_a);
        assert(t2@.subrange(0, n as int) == t2_seq_a);
        lemma_disjunction_to_signed_sub_buf::<u32>(
            t1_seq_a, s1 as int,
            t2_seq_a, s2 as int,
            t5_seq_d1, d1_s as int,
            n as nat,
        );
    }

    let tzd_re_s = signed_add_to(&**t5, &d1_s, &**t5, &d1_s, t1, 0usize, ls1, 0usize, ls2, 0usize, n_us);
    let ghost t1_seq_tzdre = t1@.subrange(0, n as int);
    let ghost tzd_re_int = signed_val_of(t1_seq_tzdre, tzd_re_s as int);
    proof {
        assert(t5@.subrange(0, n as int) == t5_seq_d1);
        lemma_disjunction_to_signed_add_buf::<u32>(
            t5_seq_d1, d1_s as int,
            t5_seq_d1, d1_s as int,
            t1_seq_tzdre, tzd_re_s as int,
            n as nat,
        );
    }

    // 2*Z*δ imag = 2*(t3 + t4)
    let d2_s = signed_add_to(&**t3, &s3, &**t4, &s4, t5, 0usize, ls1, 0usize, ls2, 0usize, n_us);
    let ghost t5_seq_d2 = t5@.subrange(0, n as int);
    let ghost d2_int = signed_val_of(t5_seq_d2, d2_s as int);
    proof {
        assert(t3@.subrange(0, n as int) == t3_seq_a);
        assert(t4@.subrange(0, n as int) == t4_seq_a);
        lemma_disjunction_to_signed_add_buf::<u32>(
            t3_seq_a, s3 as int,
            t4_seq_a, s4 as int,
            t5_seq_d2, d2_s as int,
            n as nat,
        );
    }

    let tzd_im_s = signed_add_to(&**t5, &d2_s, &**t5, &d2_s, t2, 0usize, ls1, 0usize, ls2, 0usize, n_us);
    let ghost t2_seq_tzdim = t2@.subrange(0, n as int);
    let ghost tzd_im_int = signed_val_of(t2_seq_tzdim, tzd_im_s as int);
    proof {
        assert(t5@.subrange(0, n as int) == t5_seq_d2);
        lemma_disjunction_to_signed_add_buf::<u32>(
            t5_seq_d2, d2_s as int,
            t5_seq_d2, d2_s as int,
            t2_seq_tzdim, tzd_im_s as int,
            n as nat,
        );
    }

    // ── Part B: δ² (3 multiplies, Karatsuba) ──
    let drs_s = signed_mul_to(&**delta_re, &delta_re_sign_in, &**delta_re, &delta_re_sign_in,
                              t3, 0usize, lprod, 0usize, n_us, frac_us);
    let ghost t3_seq_drs = t3@.subrange(0, n as int);
    let ghost drs_int = signed_val_of(t3_seq_drs, drs_s as int);
    proof {
        assert(delta_re@.subrange(0, n as int) == dre_in_seq);
        lemma_signed_mul_postcond_to_buf::<u32>(
            dre_in_seq, delta_re_sign_in as int,
            dre_in_seq, delta_re_sign_in as int,
            t3_seq_drs, drs_s as int,
            n as nat, frac_limbs as nat,
        );
    }

    let dis_s = signed_mul_to(&**delta_im, &delta_im_sign_in, &**delta_im, &delta_im_sign_in,
                              t4, 0usize, lprod, 0usize, n_us, frac_us);
    let ghost t4_seq_dis = t4@.subrange(0, n as int);
    let ghost dis_int = signed_val_of(t4_seq_dis, dis_s as int);
    proof {
        assert(delta_im@.subrange(0, n as int) == dim_in_seq);
        lemma_signed_mul_postcond_to_buf::<u32>(
            dim_in_seq, delta_im_sign_in as int,
            dim_in_seq, delta_im_sign_in as int,
            t4_seq_dis, dis_s as int,
            n as nat, frac_limbs as nat,
        );
    }

    let dri_s = signed_add_to(&**delta_re, &delta_re_sign_in, &**delta_im, &delta_im_sign_in,
                              t5, 0usize, ls1, 0usize, ls2, 0usize, n_us);
    let ghost t5_seq_dri = t5@.subrange(0, n as int);
    let ghost dri_int = signed_val_of(t5_seq_dri, dri_s as int);
    proof {
        assert(delta_re@.subrange(0, n as int) == dre_in_seq);
        assert(delta_im@.subrange(0, n as int) == dim_in_seq);
        lemma_disjunction_to_signed_add_buf::<u32>(
            dre_in_seq, delta_re_sign_in as int,
            dim_in_seq, delta_im_sign_in as int,
            t5_seq_dri, dri_s as int,
            n as nat,
        );
    }

    let dri2_s = signed_mul_to(&**t5, &dri_s, &**t5, &dri_s,
                               ls1, 0usize, lprod, 0usize, n_us, frac_us);
    let ghost ls1_seq_dri2 = ls1@.subrange(0, n as int);
    let ghost dri2_int = signed_val_of(ls1_seq_dri2, dri2_s as int);
    proof {
        assert(t5@.subrange(0, n as int) == t5_seq_dri);
        lemma_signed_mul_postcond_to_buf::<u32>(
            t5_seq_dri, dri_s as int,
            t5_seq_dri, dri_s as int,
            ls1_seq_dri2, dri2_s as int,
            n as nat, frac_limbs as nat,
        );
    }

    // δ² real = δ_re² - δ_im²
    let dsq_re_s = signed_sub_to(&**t3, &drs_s, &**t4, &dis_s, t5, 0usize, delta_re, 0usize, delta_im, 0usize, n_us);
    let ghost t5_seq_dsqre = t5@.subrange(0, n as int);
    let ghost dsq_re_int = signed_val_of(t5_seq_dsqre, dsq_re_s as int);
    proof {
        assert(t3@.subrange(0, n as int) == t3_seq_drs);
        assert(t4@.subrange(0, n as int) == t4_seq_dis);
        lemma_disjunction_to_signed_sub_buf::<u32>(
            t3_seq_drs, drs_s as int,
            t4_seq_dis, dis_s as int,
            t5_seq_dsqre, dsq_re_s as int,
            n as nat,
        );
    }

    // δ² imag = (δ_re+δ_im)² - δ_re² - δ_im²
    let q1_s = signed_sub_to(&**ls1, &dri2_s, &**t3, &drs_s, delta_re, 0usize, ls2, 0usize, delta_im, 0usize, n_us);
    let ghost dre_seq_q1 = delta_re@.subrange(0, n as int);
    let ghost q1_int = signed_val_of(dre_seq_q1, q1_s as int);
    proof {
        assert(ls1@.subrange(0, n as int) == ls1_seq_dri2);
        assert(t3@.subrange(0, n as int) == t3_seq_drs);
        assert(dre_seq_q1 =~= delta_re@);
        lemma_disjunction_to_signed_sub_buf::<u32>(
            ls1_seq_dri2, dri2_s as int,
            t3_seq_drs, drs_s as int,
            dre_seq_q1, q1_s as int,
            n as nat,
        );
    }

    let dsq_im_s = signed_sub_to(&**delta_re, &q1_s, &**t4, &dis_s, t3, 0usize, ls2, 0usize, delta_im, 0usize, n_us);
    let ghost t3_seq_dsqim = t3@.subrange(0, n as int);
    let ghost dsq_im_int = signed_val_of(t3_seq_dsqim, dsq_im_s as int);
    proof {
        assert(delta_re@.subrange(0, n as int) =~= dre_seq_q1);
        assert(t4@.subrange(0, n as int) == t4_seq_dis);
        lemma_disjunction_to_signed_sub_buf::<u32>(
            dre_seq_q1, q1_s as int,
            t4_seq_dis, dis_s as int,
            t3_seq_dsqim, dsq_im_s as int,
            n as nat,
        );
    }

    // ── Part C: δ' = (2*Z*δ) + δ² + Δc ──
    let p1_s = signed_add_to(&**t1, &tzd_re_s, &**t5, &dsq_re_s, t4, 0usize, ls1, 0usize, ls2, 0usize, n_us);
    let ghost t4_seq_p1 = t4@.subrange(0, n as int);
    let ghost p1_int = signed_val_of(t4_seq_p1, p1_s as int);
    proof {
        assert(t1@.subrange(0, n as int) == t1_seq_tzdre);
        assert(t5@.subrange(0, n as int) == t5_seq_dsqre);
        lemma_disjunction_to_signed_add_buf::<u32>(
            t1_seq_tzdre, tzd_re_s as int,
            t5_seq_dsqre, dsq_re_s as int,
            t4_seq_p1, p1_s as int,
            n as nat,
        );
    }

    let new_dr_s = signed_add_to(&**t4, &p1_s, dc_re, &dc_re_sign, delta_re, 0usize, ls1, 0usize, ls2, 0usize, n_us);
    let ghost dre_out_seq = delta_re@.subrange(0, n as int);
    let ghost new_dre_int = signed_val_of(dre_out_seq, new_dr_s as int);
    proof {
        assert(t4@.subrange(0, n as int) == t4_seq_p1);
        assert(dc_re@.subrange(0, n as int) =~= dcre_seq);
        assert(dre_out_seq =~= delta_re@);
        lemma_disjunction_to_signed_add_buf::<u32>(
            t4_seq_p1, p1_s as int,
            dcre_seq, dc_re_sign as int,
            dre_out_seq, new_dr_s as int,
            n as nat,
        );
    }

    let p2_s = signed_add_to(&**t2, &tzd_im_s, &**t3, &dsq_im_s, t4, 0usize, ls1, 0usize, ls2, 0usize, n_us);
    let ghost t4_seq_p2 = t4@.subrange(0, n as int);
    let ghost p2_int = signed_val_of(t4_seq_p2, p2_s as int);
    proof {
        assert(t2@.subrange(0, n as int) == t2_seq_tzdim);
        assert(t3@.subrange(0, n as int) == t3_seq_dsqim);
        lemma_disjunction_to_signed_add_buf::<u32>(
            t2_seq_tzdim, tzd_im_s as int,
            t3_seq_dsqim, dsq_im_s as int,
            t4_seq_p2, p2_s as int,
            n as nat,
        );
    }

    let new_di_s = signed_add_to(&**t4, &p2_s, dc_im, &dc_im_sign, delta_im, 0usize, ls1, 0usize, ls2, 0usize, n_us);
    let ghost dim_out_seq = delta_im@.subrange(0, n as int);
    let ghost new_dim_int = signed_val_of(dim_out_seq, new_di_s as int);
    proof {
        assert(t4@.subrange(0, n as int) == t4_seq_p2);
        assert(dc_im@.subrange(0, n as int) =~= dcim_seq);
        assert(dim_out_seq =~= delta_im@);
        lemma_disjunction_to_signed_add_buf::<u32>(
            t4_seq_p2, p2_s as int,
            dcim_seq, dc_im_sign as int,
            dim_out_seq, new_di_s as int,
            n as nat,
        );
    }

    proof {
        // valid_limbs from forall postconditions of last signed_add_to calls
        assert(valid_limbs(delta_re@)) by {
            assert forall |k: int| 0 <= k < delta_re@.len()
                implies 0 <= (#[trigger] delta_re@[k]).sem()
                    && delta_re@[k].sem() < LIMB_BASE() by { }
        }
        assert(valid_limbs(delta_im@)) by {
            assert forall |k: int| 0 <= k < delta_im@.len()
                implies 0 <= (#[trigger] delta_im@[k]).sem()
                    && delta_im@[k].sem() < LIMB_BASE() by { }
        }

        // ── Compose all the steps to match pert_step_buf_int ──
        // pert_step_buf_int unfolds (it's open spec) into the same chain
        // of signed_mul_buf / signed_add_buf / signed_sub_buf calls.
        // Z3 should chase the let-bindings and identify each intermediate
        // ghost int we built up above.
        let result = pert_step_buf_int(
            z_re_int, z_im_int,
            dre_in_int, dim_in_int,
            dcre_int, dcim_int,
            n as nat, frac_limbs as nat,
        );
        assert(result.0 == new_dre_int);
        assert(result.1 == new_dim_int);
    }

    (new_dr_s, new_di_s)
}

// ═══════════════════════════════════════════════════════════════
// Reference orbit sub-helpers (Phase B Stage 2)
//
// Split the 9-op ref orbit step into 3 focused sub-helpers to keep
// each Z3 context under ~20 assertions (shared-buffer frame reasoning
// is expensive). Each sub-helper does 3 ops, establishes value equations,
// and provides frame conditions for subsequent parts.
// ═══════════════════════════════════════════════════════════════

/// Part A of reference orbit step: ops 1-3 (re², im², re+im).
///
/// Computes the three squaring/sum intermediates needed by the Karatsuba
/// decomposition of Z² + c. Writes to temp region [t0_re2, t0_re2+3n).
#[verifier::rlimit(500)]
fn ref_orbit_step_part_a(
    wg_mem: &mut Vec<u32>,
    zk_re: u32, zk_im: u32,
    zk_re_s: u32, zk_im_s: u32,
    t0_re2: u32,
    ref_a: &mut Vec<u32>, ref_b: &mut Vec<u32>,
    n: u32, frac_limbs: u32,
) -> (out: (u32, u32, u32))
    requires
        n >= 1, n <= 8, n as int <= 0x1FFF_FFFF,
        frac_limbs <= n, frac_limbs + n <= 2 * n,
        old(wg_mem)@.len() >= 8192,
        old(ref_a)@.len() == n as int,
        old(ref_b)@.len() == n as int,
        zk_re_s <= 1u32, zk_im_s <= 1u32,
        (zk_re as int) + (n as int) <= old(wg_mem)@.len(),
        (zk_im as int) + (n as int) <= old(wg_mem)@.len(),
        zk_re + n < u32_max(),
        zk_im + n < u32_max(),
        (zk_re as int) + (n as int) <= t0_re2 as int,
        (zk_im as int) + (n as int) <= t0_re2 as int,
        t0_re2 + 10u32 * n < 8192u32,
        valid_limbs(old(wg_mem)@.subrange(zk_re as int, zk_re as int + n as int)),
        valid_limbs(old(wg_mem)@.subrange(zk_im as int, zk_im as int + n as int)),
    ensures
        wg_mem@.len() == old(wg_mem)@.len(),
        ref_a@.len() == n as int,
        ref_b@.len() == n as int,
        // Signs: self-mul always gives sign 0
        out.0 == 0u32, out.1 == 0u32,
        out.2 == 0u32 || out.2 == 1u32,
        // Valid limbs on outputs
        valid_limbs(wg_mem@.subrange(t0_re2 as int, t0_re2 as int + n as int)),
        valid_limbs(wg_mem@.subrange(t0_re2 as int + n as int, t0_re2 as int + 2 * n as int)),
        valid_limbs(wg_mem@.subrange(t0_re2 as int + 2 * n as int, t0_re2 as int + 3 * n as int)),
        // Frame: everything below t0_re2 unchanged
        forall |j: int| 0 <= j < t0_re2 as int ==> wg_mem@[j] == old(wg_mem)@[j],
        // Op 1 value: re²
        vec_val(wg_mem@.subrange(t0_re2 as int, t0_re2 as int + n as int))
            == (vec_val(old(wg_mem)@.subrange(zk_re as int, zk_re as int + n as int))
                * vec_val(old(wg_mem)@.subrange(zk_re as int, zk_re as int + n as int))
                / limb_power(frac_limbs as nat)) % limb_power(n as nat),
        // Op 2 value: im²
        vec_val(wg_mem@.subrange(t0_re2 as int + n as int, t0_re2 as int + 2 * n as int))
            == (vec_val(old(wg_mem)@.subrange(zk_im as int, zk_im as int + n as int))
                * vec_val(old(wg_mem)@.subrange(zk_im as int, zk_im as int + n as int))
                / limb_power(frac_limbs as nat)) % limb_power(n as nat),
        // Op 3 value: re + im (3-way disjunction)
        ({
            let va = vec_val(old(wg_mem)@.subrange(zk_re as int, zk_re as int + n as int));
            let vb = vec_val(old(wg_mem)@.subrange(zk_im as int, zk_im as int + n as int));
            let vo = vec_val(wg_mem@.subrange(t0_re2 as int + 2 * n as int, t0_re2 as int + 3 * n as int));
            let sa = if zk_re_s == 0u32 { va } else { -va };
            let sb = if zk_im_s == 0u32 { vb } else { -vb };
            let so = if out.2 == 0u32 { vo } else { -vo };
            let p = limb_power(n as nat);
            so == sa + sb
                || (so == sa + sb - p && sa + sb >= p)
                || (so == sa + sb + p && sa + sb <= -(p as int))
        }),
{
    let t0_im2 = t0_re2 + n;
    let t0_rpi = t0_re2 + 2u32 * n;
    let t0_prod = t0_re2 + 5u32 * n;
    let t0_stmp1 = t0_re2 + 7u32 * n;
    let t0_stmp2 = t0_re2 + 8u32 * n;

    let ghost old_wg = wg_mem@;

    // Op 1: re² = mul(zk_re, zk_re)
    copy_limbs(wg_mem, zk_re, ref_a, n);
    // ref_a now holds old_wg[zk_re..+n]; wg_mem unchanged (copy_limbs takes &Vec)
    proof {
        assert(ref_a@.subrange(0, n as int) =~= old_wg.subrange(zk_re as int, zk_re as int + n as int)) by {
            assert forall |j: int| 0 <= j < n as int implies
                ref_a@.subrange(0, n as int)[j]
                    == old_wg.subrange(zk_re as int, zk_re as int + n as int)[j] by {}
        }
    }
    let re2_s = signed_mul_to_buf(
        &**ref_a, &zk_re_s, &**ref_a, &zk_re_s,
        wg_mem, t0_re2 as usize, t0_prod as usize, n as usize, frac_limbs as usize);
    let ghost re2_out = wg_mem@.subrange(t0_re2 as int, t0_re2 as int + n as int);

    // Op 2: im² = mul(zk_im, zk_im)
    copy_limbs(wg_mem, zk_im, ref_a, n);
    // zk_im region below t0_re2 → unchanged by op 1
    proof {
        assert(ref_a@.subrange(0, n as int) =~= old_wg.subrange(zk_im as int, zk_im as int + n as int)) by {
            assert forall |j: int| 0 <= j < n as int implies
                ref_a@.subrange(0, n as int)[j]
                    == old_wg.subrange(zk_im as int, zk_im as int + n as int)[j] by {
                // ref_a@[j] == wg_mem@[zk_im+j] (copy_limbs)
                // wg_mem@[zk_im+j] == old_wg[zk_im+j] (op 1 frame: zk_im+j < t0_re2)
                assert(zk_im as int + j < t0_re2 as int);
            }
        }
    }
    let im2_s = signed_mul_to_buf(
        &**ref_a, &zk_im_s, &**ref_a, &zk_im_s,
        wg_mem, t0_im2 as usize, t0_prod as usize, n as usize, frac_limbs as usize);
    let ghost im2_out = wg_mem@.subrange(t0_im2 as int, t0_im2 as int + n as int);

    // Op 3: re + im
    copy_limbs(wg_mem, zk_re, ref_a, n);
    copy_limbs(wg_mem, zk_im, ref_b, n);
    proof {
        assert(ref_a@.subrange(0, n as int) =~= old_wg.subrange(zk_re as int, zk_re as int + n as int)) by {
            assert forall |j: int| 0 <= j < n as int implies
                ref_a@.subrange(0, n as int)[j]
                    == old_wg.subrange(zk_re as int, zk_re as int + n as int)[j] by {
                assert(zk_re as int + j < t0_re2 as int);
            }
        }
        assert(ref_b@.subrange(0, n as int) =~= old_wg.subrange(zk_im as int, zk_im as int + n as int)) by {
            assert forall |j: int| 0 <= j < n as int implies
                ref_b@.subrange(0, n as int)[j]
                    == old_wg.subrange(zk_im as int, zk_im as int + n as int)[j] by {
                assert(zk_im as int + j < t0_re2 as int);
            }
        }
    }
    let rpi_s = signed_add_to_buf(
        &**ref_a, &zk_re_s, &**ref_b, &zk_im_s,
        wg_mem, t0_rpi as usize, t0_stmp1 as usize, t0_stmp2 as usize, n as usize);

    proof {
        lemma_pointwise_to_valid_limbs(wg_mem@, t0_re2 as int, n as nat);
        lemma_pointwise_to_valid_limbs(wg_mem@, t0_im2 as int, n as nat);
        lemma_pointwise_to_valid_limbs(wg_mem@, t0_rpi as int, n as nat);

        // Frame: re2 output from op 1 preserved through ops 2-3
        assert(wg_mem@.subrange(t0_re2 as int, t0_re2 as int + n as int) =~= re2_out) by {
            assert forall |j: int| 0 <= j < n as int implies
                wg_mem@.subrange(t0_re2 as int, t0_re2 as int + n as int)[j] == re2_out[j] by {
                assert(wg_mem@[t0_re2 as int + j] == re2_out[j]);
            }
        }
        // Frame: im2 output from op 2 preserved through op 3
        assert(wg_mem@.subrange(t0_im2 as int, t0_im2 as int + n as int) =~= im2_out) by {
            assert forall |j: int| 0 <= j < n as int implies
                wg_mem@.subrange(t0_im2 as int, t0_im2 as int + n as int)[j] == im2_out[j] by {
                assert(wg_mem@[t0_im2 as int + j] == im2_out[j]);
            }
        }
    }

    (re2_s, im2_s, rpi_s)
}

/// Part B of reference orbit step: ops 4-6 ((re+im)², re²-im², diff+c_re).
///
/// Computes the new real component. Writes new_re to zn output slot and
/// intermediates to temp region [t0_re2+3n, t0_re2+5n).
#[verifier::rlimit(500)]
fn ref_orbit_step_part_b(
    wg_mem: &mut Vec<u32>,
    re2_s: u32, im2_s: u32, rpi_s: u32,
    ref_c_re_s: u32,
    t0_re2: u32, zn: u32, ref_c_base: u32,
    ref_a: &mut Vec<u32>, ref_b: &mut Vec<u32>,
    n: u32, frac_limbs: u32,
) -> (out: (u32, u32, u32))
    requires
        n >= 1, n <= 8, n as int <= 0x1FFF_FFFF,
        frac_limbs <= n, frac_limbs + n <= 2 * n,
        old(wg_mem)@.len() >= 8192,
        old(ref_a)@.len() == n as int,
        old(ref_b)@.len() == n as int,
        re2_s <= 1u32, im2_s <= 1u32, rpi_s <= 1u32, ref_c_re_s <= 1u32,
        t0_re2 + 10u32 * n < 8192u32,
        zn + 2u32 * n + 1u32 < u32_max(),
        (zn as int) + 2 * (n as int) + 2 <= t0_re2 as int,
        (zn as int) + (n as int) <= ref_c_base as int,
        (ref_c_base as int) + 2 * (n as int) + 2 <= t0_re2 as int,
        ref_c_base + n + 1u32 + n < u32_max(),
        // Valid limbs on inputs (from Part A outputs + original c_ref)
        valid_limbs(old(wg_mem)@.subrange(t0_re2 as int, t0_re2 as int + n as int)),
        valid_limbs(old(wg_mem)@.subrange(t0_re2 as int + n as int, t0_re2 as int + 2 * n as int)),
        valid_limbs(old(wg_mem)@.subrange(t0_re2 as int + 2 * n as int, t0_re2 as int + 3 * n as int)),
        valid_limbs(old(wg_mem)@.subrange(ref_c_base as int, ref_c_base as int + n as int)),
    ensures
        wg_mem@.len() == old(wg_mem)@.len(),
        ref_a@.len() == n as int,
        ref_b@.len() == n as int,
        out.0 == 0u32,
        out.1 == 0u32 || out.1 == 1u32,
        out.2 == 0u32 || out.2 == 1u32,
        // Valid limbs on outputs
        valid_limbs(wg_mem@.subrange(t0_re2 as int + 3 * n as int, t0_re2 as int + 4 * n as int)),
        valid_limbs(wg_mem@.subrange(t0_re2 as int + 4 * n as int, t0_re2 as int + 5 * n as int)),
        valid_limbs(wg_mem@.subrange(zn as int, zn as int + n as int)),
        // Frame: Part A outputs [t0_re2, t0_re2+3n) preserved
        forall |j: int| t0_re2 as int <= j < t0_re2 as int + 3 * n as int
            ==> wg_mem@[j] == old(wg_mem)@[j],
        // Frame: prior orbit slots [0, zn) preserved
        forall |j: int| 0 <= j < zn as int ==> wg_mem@[j] == old(wg_mem)@[j],
        // Frame: c_ref region preserved (zn+n ≤ ref_c_base, so op 6 doesn't touch c_ref)
        forall |j: int| ref_c_base as int <= j < ref_c_base as int + 2 * n as int + 2
            ==> wg_mem@[j] == old(wg_mem)@[j],
        // Op 4 value: (re+im)²
        vec_val(wg_mem@.subrange(t0_re2 as int + 3 * n as int, t0_re2 as int + 4 * n as int))
            == (vec_val(old(wg_mem)@.subrange(t0_re2 as int + 2 * n as int, t0_re2 as int + 3 * n as int))
                * vec_val(old(wg_mem)@.subrange(t0_re2 as int + 2 * n as int, t0_re2 as int + 3 * n as int))
                / limb_power(frac_limbs as nat)) % limb_power(n as nat),
        // Op 5 value: re² - im² (3-way disjunction)
        ({
            let va = vec_val(old(wg_mem)@.subrange(t0_re2 as int, t0_re2 as int + n as int));
            let vb = vec_val(old(wg_mem)@.subrange(t0_re2 as int + n as int, t0_re2 as int + 2 * n as int));
            let vo = vec_val(wg_mem@.subrange(t0_re2 as int + 4 * n as int, t0_re2 as int + 5 * n as int));
            let sa = if re2_s == 0u32 { va } else { -va };
            let sb = if im2_s == 0u32 { vb } else { -vb };
            let so = if out.1 == 0u32 { vo } else { -vo };
            let p = limb_power(n as nat);
            so == sa - sb
                || (so == sa - sb - p && sa - sb >= p)
                || (so == sa - sb + p && sa - sb <= -(p as int))
        }),
        // Op 6 value: diff + c_re (3-way disjunction)
        ({
            let va = vec_val(wg_mem@.subrange(t0_re2 as int + 4 * n as int, t0_re2 as int + 5 * n as int));
            let vb = vec_val(old(wg_mem)@.subrange(ref_c_base as int, ref_c_base as int + n as int));
            let vo = vec_val(wg_mem@.subrange(zn as int, zn as int + n as int));
            let sa = if out.1 == 0u32 { va } else { -va };
            let sb = if ref_c_re_s == 0u32 { vb } else { -vb };
            let so = if out.2 == 0u32 { vo } else { -vo };
            let p = limb_power(n as nat);
            so == sa + sb
                || (so == sa + sb - p && sa + sb >= p)
                || (so == sa + sb + p && sa + sb <= -(p as int))
        }),
{
    let ghost old_wg = wg_mem@;
    let t0_im2 = t0_re2 + n;
    let t0_rpi = t0_re2 + 2u32 * n;
    let t0_sum2 = t0_re2 + 3u32 * n;
    let t0_diff = t0_re2 + 4u32 * n;
    let t0_prod = t0_re2 + 5u32 * n;
    let t0_stmp1 = t0_re2 + 7u32 * n;
    let t0_stmp2 = t0_re2 + 8u32 * n;

    // Op 4: (re+im)²
    copy_limbs(wg_mem, t0_rpi, ref_a, n);
    proof {
        assert(ref_a@.subrange(0, n as int) =~= old_wg.subrange(t0_rpi as int, t0_rpi as int + n as int)) by {
            assert forall |j: int| 0 <= j < n as int implies
                ref_a@.subrange(0, n as int)[j]
                    == old_wg.subrange(t0_rpi as int, t0_rpi as int + n as int)[j] by {}
        }
    }
    let sum2_s = signed_mul_to_buf(
        &**ref_a, &rpi_s, &**ref_a, &rpi_s,
        wg_mem, t0_sum2 as usize, t0_prod as usize, n as usize, frac_limbs as usize);
    let ghost sum2_out = wg_mem@.subrange(t0_sum2 as int, t0_sum2 as int + n as int);

    // Op 5: re² - im²
    copy_limbs(wg_mem, t0_re2, ref_a, n);
    copy_limbs(wg_mem, t0_im2, ref_b, n);
    // t0_re2 (0n) and t0_im2 (1n) unchanged by op 4 (wrote to 3n+ and 5n+)
    proof {
        assert(ref_a@.subrange(0, n as int) =~= old_wg.subrange(t0_re2 as int, t0_re2 as int + n as int)) by {
            assert forall |j: int| 0 <= j < n as int implies
                ref_a@.subrange(0, n as int)[j]
                    == old_wg.subrange(t0_re2 as int, t0_re2 as int + n as int)[j] by {
                assert(t0_re2 as int + j < t0_sum2 as int);
            }
        }
        assert(ref_b@.subrange(0, n as int) =~= old_wg.subrange(t0_im2 as int, t0_im2 as int + n as int)) by {
            assert forall |j: int| 0 <= j < n as int implies
                ref_b@.subrange(0, n as int)[j]
                    == old_wg.subrange(t0_im2 as int, t0_im2 as int + n as int)[j] by {
                assert(t0_im2 as int + j < t0_sum2 as int);
            }
        }
        // Explicit vec_val equalities for the sub disjunction postcondition
        assert(vec_val(ref_a@.subrange(0, n as int)) == vec_val(old_wg.subrange(t0_re2 as int, t0_re2 as int + n as int)));
        assert(vec_val(ref_b@.subrange(0, n as int)) == vec_val(old_wg.subrange(t0_im2 as int, t0_im2 as int + n as int)));
    }
    let diff_s = signed_sub_to_buf(
        &**ref_a, &re2_s, &**ref_b, &im2_s,
        wg_mem, t0_diff as usize, t0_stmp1 as usize, t0_stmp2 as usize, n as usize);
    let ghost diff_out = wg_mem@.subrange(t0_diff as int, t0_diff as int + n as int);

    // Op 6: diff + c_re → new_re at zn
    copy_limbs(wg_mem, t0_diff, ref_a, n);
    copy_limbs(wg_mem, ref_c_base, ref_b, n);
    proof {
        // ref_a holds op 5's t0_diff output
        assert(ref_a@.subrange(0, n as int) =~= diff_out) by {
            assert forall |j: int| 0 <= j < n as int implies
                ref_a@.subrange(0, n as int)[j] == diff_out[j] by {}
        }
        // ref_c_base below t0_re2, unchanged by ops 4-5
        assert(ref_b@.subrange(0, n as int) =~= old_wg.subrange(ref_c_base as int, ref_c_base as int + n as int)) by {
            assert forall |j: int| 0 <= j < n as int implies
                ref_b@.subrange(0, n as int)[j]
                    == old_wg.subrange(ref_c_base as int, ref_c_base as int + n as int)[j] by {
                assert(ref_c_base as int + j < t0_re2 as int);
            }
        }
        assert(vec_val(ref_b@.subrange(0, n as int)) == vec_val(old_wg.subrange(ref_c_base as int, ref_c_base as int + n as int)));
    }
    let new_re_s = signed_add_to_buf(
        &**ref_a, &diff_s, &**ref_b, &ref_c_re_s,
        wg_mem, zn as usize, t0_stmp1 as usize, t0_stmp2 as usize, n as usize);

    proof {
        lemma_pointwise_to_valid_limbs(wg_mem@, t0_sum2 as int, n as nat);
        lemma_pointwise_to_valid_limbs(wg_mem@, t0_diff as int, n as nat);
        lemma_pointwise_to_valid_limbs(wg_mem@, zn as int, n as nat);

        // Frame: t0_sum2 from op 4 preserved through ops 5-6
        assert(wg_mem@.subrange(t0_sum2 as int, t0_sum2 as int + n as int) =~= sum2_out) by {
            assert forall |j: int| 0 <= j < n as int implies
                wg_mem@.subrange(t0_sum2 as int, t0_sum2 as int + n as int)[j] == sum2_out[j] by {
                assert(wg_mem@[t0_sum2 as int + j] == sum2_out[j]);
            }
        }
        // Frame: t0_diff from op 5 preserved through op 6 (op 6 writes to zn, stmp1, stmp2)
        assert(wg_mem@.subrange(t0_diff as int, t0_diff as int + n as int) =~= diff_out) by {
            assert forall |j: int| 0 <= j < n as int implies
                wg_mem@.subrange(t0_diff as int, t0_diff as int + n as int)[j] == diff_out[j] by {
                assert(wg_mem@[t0_diff as int + j] == diff_out[j]);
            }
        }
    }

    (sum2_s, diff_s, new_re_s)
}

/// Part C of reference orbit step: ops 7-9 ((re+im)²-re², t1-im², t2+c_im).
///
/// Computes the new imaginary component using the 2*re*im = (re+im)²-re²-im²
/// identity. Writes new_im to zn+n+1 output slot.
#[verifier::rlimit(500)]
fn ref_orbit_step_part_c(
    wg_mem: &mut Vec<u32>,
    re2_s: u32, im2_s: u32, sum2_s: u32,
    ref_c_im_s: u32,
    t0_re2: u32, zn: u32, ref_c_base: u32,
    ref_a: &mut Vec<u32>, ref_b: &mut Vec<u32>,
    n: u32,
) -> (out: (u32, u32, u32))
    requires
        n >= 1, n <= 8, n as int <= 0x1FFF_FFFF,
        old(wg_mem)@.len() >= 8192,
        old(ref_a)@.len() == n as int,
        old(ref_b)@.len() == n as int,
        re2_s <= 1u32, im2_s <= 1u32, sum2_s <= 1u32, ref_c_im_s <= 1u32,
        t0_re2 + 10u32 * n < 8192u32,
        zn + 2u32 * n + 1u32 < u32_max(),
        (zn as int) + 2 * (n as int) + 2 <= t0_re2 as int,
        (zn as int) + 2 * (n as int) + 2 <= ref_c_base as int,
        (ref_c_base as int) + 2 * (n as int) + 2 <= t0_re2 as int,
        ref_c_base + n + 1u32 + n < u32_max(),
        // Valid limbs on inputs
        valid_limbs(old(wg_mem)@.subrange(t0_re2 as int, t0_re2 as int + n as int)),
        valid_limbs(old(wg_mem)@.subrange(t0_re2 as int + n as int, t0_re2 as int + 2 * n as int)),
        valid_limbs(old(wg_mem)@.subrange(t0_re2 as int + 3 * n as int, t0_re2 as int + 4 * n as int)),
        valid_limbs(old(wg_mem)@.subrange(
            ref_c_base as int + n as int + 1, ref_c_base as int + 2 * n as int + 1)),
    ensures
        wg_mem@.len() == old(wg_mem)@.len(),
        ref_a@.len() == n as int,
        ref_b@.len() == n as int,
        out.0 == 0u32 || out.0 == 1u32,
        out.1 == 0u32 || out.1 == 1u32,
        out.2 == 0u32 || out.2 == 1u32,
        // Valid limbs on outputs
        valid_limbs(wg_mem@.subrange(t0_re2 as int + 4 * n as int, t0_re2 as int + 5 * n as int)),
        valid_limbs(wg_mem@.subrange(t0_re2 as int + 9 * n as int, t0_re2 as int + 10 * n as int)),
        valid_limbs(wg_mem@.subrange(
            zn as int + n as int + 1, zn as int + 2 * n as int + 1)),
        // Frame: prior orbit slots [0, zn) preserved
        forall |j: int| 0 <= j < zn as int ==> wg_mem@[j] == old(wg_mem)@[j],
        // Frame: Part A re2/im2 [t0_re2, t0_re2+2n) preserved
        forall |j: int| t0_re2 as int <= j < t0_re2 as int + 2 * n as int
            ==> wg_mem@[j] == old(wg_mem)@[j],
        // Frame: zn [zn, zn+n) preserved (new_re from Part B)
        forall |j: int| zn as int <= j < zn as int + n as int
            ==> wg_mem@[j] == old(wg_mem)@[j],
        // Op 7 value: (re+im)² - re² (3-way disjunction)
        ({
            let va = vec_val(old(wg_mem)@.subrange(t0_re2 as int + 3 * n as int, t0_re2 as int + 4 * n as int));
            let vb = vec_val(old(wg_mem)@.subrange(t0_re2 as int, t0_re2 as int + n as int));
            let vo = vec_val(wg_mem@.subrange(t0_re2 as int + 4 * n as int, t0_re2 as int + 5 * n as int));
            let sa = if sum2_s == 0u32 { va } else { -va };
            let sb = if re2_s == 0u32 { vb } else { -vb };
            let so = if out.0 == 0u32 { vo } else { -vo };
            let p = limb_power(n as nat);
            so == sa - sb
                || (so == sa - sb - p && sa - sb >= p)
                || (so == sa - sb + p && sa - sb <= -(p as int))
        }),
        // Op 8 value: t1 - im² (3-way disjunction)
        ({
            let va = vec_val(wg_mem@.subrange(t0_re2 as int + 4 * n as int, t0_re2 as int + 5 * n as int));
            let vb = vec_val(old(wg_mem)@.subrange(t0_re2 as int + n as int, t0_re2 as int + 2 * n as int));
            let vo = vec_val(wg_mem@.subrange(t0_re2 as int + 9 * n as int, t0_re2 as int + 10 * n as int));
            let sa = if out.0 == 0u32 { va } else { -va };
            let sb = if im2_s == 0u32 { vb } else { -vb };
            let so = if out.1 == 0u32 { vo } else { -vo };
            let p = limb_power(n as nat);
            so == sa - sb
                || (so == sa - sb - p && sa - sb >= p)
                || (so == sa - sb + p && sa - sb <= -(p as int))
        }),
        // Op 9 value: t2 + c_im (3-way disjunction)
        ({
            let va = vec_val(wg_mem@.subrange(t0_re2 as int + 9 * n as int, t0_re2 as int + 10 * n as int));
            let vb = vec_val(old(wg_mem)@.subrange(
                ref_c_base as int + n as int + 1, ref_c_base as int + 2 * n as int + 1));
            let vo = vec_val(wg_mem@.subrange(
                zn as int + n as int + 1, zn as int + 2 * n as int + 1));
            let sa = if out.1 == 0u32 { va } else { -va };
            let sb = if ref_c_im_s == 0u32 { vb } else { -vb };
            let so = if out.2 == 0u32 { vo } else { -vo };
            let p = limb_power(n as nat);
            so == sa + sb
                || (so == sa + sb - p && sa + sb >= p)
                || (so == sa + sb + p && sa + sb <= -(p as int))
        }),
{
    let ghost old_wg = wg_mem@;
    let t0_re2_off = t0_re2;
    let t0_im2 = t0_re2 + n;
    let t0_sum2 = t0_re2 + 3u32 * n;
    let t0_diff = t0_re2 + 4u32 * n;
    let t0_stmp1 = t0_re2 + 7u32 * n;
    let t0_stmp2 = t0_re2 + 8u32 * n;
    let t0_stmp3 = t0_re2 + 9u32 * n;

    // Op 7: (re+im)² - re²
    copy_limbs(wg_mem, t0_sum2, ref_a, n);
    copy_limbs(wg_mem, t0_re2_off, ref_b, n);
    // First op — wg_mem == old_wg
    proof {
        assert(ref_a@.subrange(0, n as int) =~= old_wg.subrange(t0_sum2 as int, t0_sum2 as int + n as int)) by {
            assert forall |j: int| 0 <= j < n as int implies
                ref_a@.subrange(0, n as int)[j]
                    == old_wg.subrange(t0_sum2 as int, t0_sum2 as int + n as int)[j] by {}
        }
        assert(ref_b@.subrange(0, n as int) =~= old_wg.subrange(t0_re2 as int, t0_re2 as int + n as int)) by {
            assert forall |j: int| 0 <= j < n as int implies
                ref_b@.subrange(0, n as int)[j]
                    == old_wg.subrange(t0_re2 as int, t0_re2 as int + n as int)[j] by {}
        }
    }
    let t1_s = signed_sub_to_buf(
        &**ref_a, &sum2_s, &**ref_b, &re2_s,
        wg_mem, t0_diff as usize, t0_stmp1 as usize, t0_stmp2 as usize, n as usize);
    let ghost diff_out = wg_mem@.subrange(t0_diff as int, t0_diff as int + n as int);

    // Op 8: t1 - im²
    copy_limbs(wg_mem, t0_diff, ref_a, n);
    copy_limbs(wg_mem, t0_im2, ref_b, n);
    proof {
        // ref_a holds op 7's t0_diff output
        assert(ref_a@.subrange(0, n as int) =~= diff_out) by {
            assert forall |j: int| 0 <= j < n as int implies
                ref_a@.subrange(0, n as int)[j] == diff_out[j] by {}
        }
        // t0_im2 at 1n — unchanged by op 7 (wrote to 4n, 7n, 8n)
        assert(ref_b@.subrange(0, n as int) =~= old_wg.subrange(t0_im2 as int, t0_im2 as int + n as int)) by {
            assert forall |j: int| 0 <= j < n as int implies
                ref_b@.subrange(0, n as int)[j]
                    == old_wg.subrange(t0_im2 as int, t0_im2 as int + n as int)[j] by {
                assert(t0_im2 as int + j < t0_diff as int);
            }
        }
        assert(vec_val(ref_b@.subrange(0, n as int)) == vec_val(old_wg.subrange(t0_im2 as int, t0_im2 as int + n as int)));
    }
    let t2_s = signed_sub_to_buf(
        &**ref_a, &t1_s, &**ref_b, &im2_s,
        wg_mem, t0_stmp3 as usize, t0_stmp1 as usize, t0_stmp2 as usize, n as usize);
    let ghost stmp3_out = wg_mem@.subrange(t0_stmp3 as int, t0_stmp3 as int + n as int);

    // Op 9: t2 + c_im → new_im at zn+n+1
    copy_limbs(wg_mem, t0_stmp3, ref_a, n);
    copy_limbs(wg_mem, (ref_c_base + n + 1u32), ref_b, n);
    proof {
        // ref_a holds op 8's t0_stmp3 output
        assert(ref_a@.subrange(0, n as int) =~= stmp3_out) by {
            assert forall |j: int| 0 <= j < n as int implies
                ref_a@.subrange(0, n as int)[j] == stmp3_out[j] by {}
        }
        // c_im at ref_c_base+n+1 — below t0_re2, unchanged by ops 7-8
        assert(ref_b@.subrange(0, n as int) =~= old_wg.subrange(
            ref_c_base as int + n as int + 1, ref_c_base as int + 2 * n as int + 1)) by {
            assert forall |j: int| 0 <= j < n as int implies
                ref_b@.subrange(0, n as int)[j]
                    == old_wg.subrange(
                        ref_c_base as int + n as int + 1,
                        ref_c_base as int + 2 * n as int + 1)[j] by {
                assert(ref_c_base as int + n as int + 1 + j < t0_re2 as int);
            }
        }
        assert(vec_val(ref_b@.subrange(0, n as int)) == vec_val(old_wg.subrange(
            ref_c_base as int + n as int + 1, ref_c_base as int + 2 * n as int + 1)));
    }
    let new_im_s = signed_add_to_buf(
        &**ref_a, &t2_s, &**ref_b, &ref_c_im_s,
        wg_mem, (zn + n + 1u32) as usize, t0_stmp1 as usize, t0_stmp2 as usize, n as usize);

    proof {
        lemma_pointwise_to_valid_limbs(wg_mem@, t0_diff as int, n as nat);
        lemma_pointwise_to_valid_limbs(wg_mem@, t0_stmp3 as int, n as nat);
        lemma_pointwise_to_valid_limbs(wg_mem@, (zn + n + 1u32) as int, n as nat);

        // Frame: t0_diff (op 7 output) preserved through ops 8-9
        // (op 8 writes to 9n, 7n, 8n; op 9 writes to zn+n+1, 7n, 8n — none touch 4n)
        assert(wg_mem@.subrange(t0_diff as int, t0_diff as int + n as int) =~= diff_out) by {
            assert forall |j: int| 0 <= j < n as int implies
                wg_mem@.subrange(t0_diff as int, t0_diff as int + n as int)[j] == diff_out[j] by {
                assert(wg_mem@[t0_diff as int + j] == diff_out[j]);
            }
        }
        // Frame: t0_stmp3 (op 8 output) preserved through op 9
        // (op 9 writes to zn+n+1, 7n, 8n — not 9n)
        assert(wg_mem@.subrange(t0_stmp3 as int, t0_stmp3 as int + n as int) =~= stmp3_out) by {
            assert forall |j: int| 0 <= j < n as int implies
                wg_mem@.subrange(t0_stmp3 as int, t0_stmp3 as int + n as int)[j] == stmp3_out[j] by {
                assert(wg_mem@[t0_stmp3 as int + j] == stmp3_out[j]);
            }
        }
    }

    (t1_s, t2_s, new_im_s)
}

/// One iteration of the reference orbit: Z_{k+1} = Z_k² + c_ref.
///
/// Extracted from the thread-0 reference-orbit loop in
/// `mandelbrot_perturbation` (Task #4 Phase B). Delegates to three
/// focused sub-helpers (Part A/B/C, 3 ops each) to keep each Z3 context
/// under ~20 assertions, then calls `lemma_ref_orbit_chain` to prove the
/// value equation: the output signed integers equal `ref_step_buf_int`
/// applied to the input Z_k and c_ref.
#[verifier::rlimit(1000)]
fn ref_orbit_iteration_step(
    wg_mem: &mut Vec<u32>,
    zk_re: u32, zk_im: u32,
    zk_re_s: u32, zk_im_s: u32,
    ref_c_base: u32,
    ref_c_re_s: u32, ref_c_im_s: u32,
    t0_re2: u32, t0_im2: u32, t0_rpi: u32, t0_sum2: u32,
    t0_diff: u32, t0_prod: u32,
    t0_stmp1: u32, t0_stmp2: u32, t0_stmp3: u32,
    zn: u32,
    ref_a: &mut Vec<u32>, ref_b: &mut Vec<u32>,
    n: u32, frac_limbs: u32,
) -> (out: (u32, u32))
    requires
        n >= 1, n <= 8, n as int <= 0x1FFF_FFFF,
        frac_limbs <= n, frac_limbs + n <= 2 * n,
        old(wg_mem)@.len() >= 8192,
        old(ref_a)@.len() == n as int,
        old(ref_b)@.len() == n as int,
        // Sign validity
        zk_re_s <= 1u32, zk_im_s <= 1u32,
        ref_c_re_s <= 1u32, ref_c_im_s <= 1u32,
        // Input region bounds
        (zk_re as int) + (n as int) <= old(wg_mem)@.len(),
        (zk_im as int) + (n as int) <= old(wg_mem)@.len(),
        (ref_c_base as int) + (n as int) <= old(wg_mem)@.len(),
        (ref_c_base as int) + (n as int) + 1 + (n as int) <= old(wg_mem)@.len(),
        zk_re + n < u32_max(),
        zk_im + n < u32_max(),
        ref_c_base + n + 1u32 + n < u32_max(),
        // Temp region offset relationships
        t0_im2 as int == t0_re2 as int + n as int,
        t0_rpi as int == t0_re2 as int + 2 * n as int,
        t0_sum2 as int == t0_re2 as int + 3 * n as int,
        t0_diff as int == t0_re2 as int + 4 * n as int,
        t0_prod as int == t0_re2 as int + 5 * n as int,
        t0_stmp1 as int == t0_re2 as int + 7 * n as int,
        t0_stmp2 as int == t0_re2 as int + 8 * n as int,
        t0_stmp3 as int == t0_re2 as int + 9 * n as int,
        // Temp region upper bound (after t0_stmp3 is n bytes of space)
        t0_stmp3 as int + n as int <= old(wg_mem)@.len(),
        t0_re2 + 10u32 * n < 8192u32,
        // Non-overlap: the new orbit slot zn is below t0_re2
        (zn as int) + 2 * (n as int) + 1 < t0_re2 as int,
        zn + 2u32 * n + 1u32 < u32_max(),
        // The new orbit slot is outside the temp region (zn + 2n+2 ≤ t0_re2)
        (zn as int) + 2 * (n as int) + 2 <= t0_re2 as int,
        // zk is outside the temp region too (zk read, not overwritten)
        (zk_re as int) + (n as int) <= t0_re2 as int,
        (zk_im as int) + (n as int) <= t0_re2 as int,
        (ref_c_base as int) + 2 * (n as int) + 2 <= t0_re2 as int,
        // Non-overlap: zn output slots don't touch c_ref
        (zn as int) + 2 * (n as int) + 2 <= ref_c_base as int,
        // Valid limbs on Z_k and c_ref regions
        valid_limbs(old(wg_mem)@.subrange(zk_re as int, zk_re as int + n as int)),
        valid_limbs(old(wg_mem)@.subrange(zk_im as int, zk_im as int + n as int)),
        valid_limbs(old(wg_mem)@.subrange(ref_c_base as int, ref_c_base as int + n as int)),
        valid_limbs(old(wg_mem)@.subrange(
            ref_c_base as int + n as int + 1,
            ref_c_base as int + n as int + 1 + n as int)),
    ensures
        wg_mem@.len() == old(wg_mem)@.len(),
        ref_a@.len() == n as int,
        ref_b@.len() == n as int,
        out.0 == 0u32 || out.0 == 1u32,
        out.1 == 0u32 || out.1 == 1u32,
        // Valid limbs on new orbit slots.
        valid_limbs(wg_mem@.subrange(zn as int, zn as int + n as int)),
        valid_limbs(wg_mem@.subrange(
            zn as int + n as int + 1,
            zn as int + 2 * n as int + 1)),
        // Frame: everything below zn is unchanged (prior orbit slots preserved)
        forall |j: int| 0 <= j < zn as int ==> wg_mem@[j] == old(wg_mem)@[j],
        // Value equation: output equals ref_step_buf_int on inputs.
        ({
            let z_re_int = signed_val_of(
                old(wg_mem)@.subrange(zk_re as int, zk_re as int + n as int), zk_re_s as int);
            let z_im_int = signed_val_of(
                old(wg_mem)@.subrange(zk_im as int, zk_im as int + n as int), zk_im_s as int);
            let c_re_int = signed_val_of(
                old(wg_mem)@.subrange(ref_c_base as int, ref_c_base as int + n as int), ref_c_re_s as int);
            let c_im_int = signed_val_of(
                old(wg_mem)@.subrange(
                    ref_c_base as int + n as int + 1,
                    ref_c_base as int + 2 * n as int + 1),
                ref_c_im_s as int);
            let result = ref_step_buf_int(
                z_re_int, z_im_int, c_re_int, c_im_int, n as nat, frac_limbs as nat);
            &&& signed_val_of(
                wg_mem@.subrange(zn as int, zn as int + n as int), out.0 as int) == result.0
            &&& signed_val_of(
                wg_mem@.subrange(
                    zn as int + n as int + 1, zn as int + 2 * n as int + 1),
                out.1 as int) == result.1
        }),
{
    // ── Capture ghost input Seqs ──
    let ghost z_re_seq = wg_mem@.subrange(zk_re as int, zk_re as int + n as int);
    let ghost z_im_seq = wg_mem@.subrange(zk_im as int, zk_im as int + n as int);
    let ghost c_re_seq = wg_mem@.subrange(ref_c_base as int, ref_c_base as int + n as int);
    let ghost c_im_seq = wg_mem@.subrange(
        ref_c_base as int + n as int + 1,
        ref_c_base as int + 2 * n as int + 1);

    // ── Part A: ops 1-3 (re², im², re+im) ──
    let (re2_s, im2_s, rpi_s) = ref_orbit_step_part_a(
        wg_mem, zk_re, zk_im, zk_re_s, zk_im_s,
        t0_re2, ref_a, ref_b, n, frac_limbs);

    // Capture Part A outputs
    let ghost t0_re2_seq = wg_mem@.subrange(t0_re2 as int, t0_re2 as int + n as int);
    let ghost t0_im2_seq = wg_mem@.subrange(t0_re2 as int + n as int, t0_re2 as int + 2 * n as int);
    let ghost t0_rpi_seq = wg_mem@.subrange(t0_re2 as int + 2 * n as int, t0_re2 as int + 3 * n as int);

    // Part A frame: c_ref regions unchanged — assert =~= in outer scope
    // so it's visible to the chain lemma proof block later
    proof {
        assert(wg_mem@.subrange(ref_c_base as int, ref_c_base as int + n as int) =~= c_re_seq) by {
            assert forall |j: int| 0 <= j < n as int implies
                wg_mem@.subrange(ref_c_base as int, ref_c_base as int + n as int)[j]
                    == c_re_seq[j] by {}
        }
    }

    // ── Part B: ops 4-6 ((re+im)², re²-im², diff+c_re → new_re) ──
    let (sum2_s, diff_s, new_re_s) = ref_orbit_step_part_b(
        wg_mem, re2_s, im2_s, rpi_s, ref_c_re_s,
        t0_re2, zn, ref_c_base,
        ref_a, ref_b, n, frac_limbs);

    // Capture Part B outputs
    let ghost t0_sum2_seq = wg_mem@.subrange(t0_re2 as int + 3 * n as int, t0_re2 as int + 4 * n as int);
    let ghost t0_diff_seq = wg_mem@.subrange(t0_re2 as int + 4 * n as int, t0_re2 as int + 5 * n as int);
    let ghost new_re_seq = wg_mem@.subrange(zn as int, zn as int + n as int);

    // Part B frame: re2, im2 preserved; c_im region preserved
    proof {
        assert(wg_mem@.subrange(t0_re2 as int, t0_re2 as int + n as int) =~= t0_re2_seq);
        assert(wg_mem@.subrange(t0_re2 as int + n as int, t0_re2 as int + 2 * n as int) =~= t0_im2_seq);
        // c_im =~= visible in outer scope for chain lemma
        assert(wg_mem@.subrange(
            ref_c_base as int + n as int + 1,
            ref_c_base as int + 2 * n as int + 1) =~= c_im_seq) by {
            assert forall |j: int| 0 <= j < n as int implies
                wg_mem@.subrange(
                    ref_c_base as int + n as int + 1,
                    ref_c_base as int + 2 * n as int + 1)[j]
                        == c_im_seq[j] by {}
        }
    }

    // ── Part C: ops 7-9 ((re+im)²-re², t1-im², t2+c_im → new_im) ──
    let (t1_s, t2_s, new_im_s) = ref_orbit_step_part_c(
        wg_mem, re2_s, im2_s, sum2_s, ref_c_im_s,
        t0_re2, zn, ref_c_base,
        ref_a, ref_b, n);

    // Capture Part C outputs
    let ghost t0_diff_seq2 = wg_mem@.subrange(t0_re2 as int + 4 * n as int, t0_re2 as int + 5 * n as int);
    let ghost t0_stmp3_seq = wg_mem@.subrange(t0_re2 as int + 9 * n as int, t0_re2 as int + 10 * n as int);
    let ghost new_im_seq = wg_mem@.subrange(
        zn as int + n as int + 1, zn as int + 2 * n as int + 1);

    // Part C frame: zn (new_re) preserved
    proof {
        assert(wg_mem@.subrange(zn as int, zn as int + n as int) =~= new_re_seq);
    }

    // ── Chain lemma: connect all 9 ops to ref_step_buf_int ──
    // Scoped inside assert-by to prevent 48+ chain lemma precondition
    // assertions from polluting the outer Z3 context (rlimit tips:
    // "Functions with >50 assertions consistently fail").
    proof {
        assert({
            let zk_re_int = signed_val_of(z_re_seq, zk_re_s as int);
            let zk_im_int = signed_val_of(z_im_seq, zk_im_s as int);
            let c_re_int = signed_val_of(c_re_seq, ref_c_re_s as int);
            let c_im_int = signed_val_of(c_im_seq, ref_c_im_s as int);
            let result = ref_step_buf_int(
                zk_re_int, zk_im_int, c_re_int, c_im_int, n as nat, frac_limbs as nat);
            signed_val_of(new_re_seq, new_re_s as int) == result.0
                && signed_val_of(new_im_seq, new_im_s as int) == result.1
        }) by {
            // Stepping stones for chain lemma preconditions (scoped in assert-by
            // to not pollute the outer function's Z3 context).

            // Lengths
            assert(z_re_seq.len() == n as nat);
            assert(z_im_seq.len() == n as nat);
            assert(c_re_seq.len() == n as nat);
            assert(c_im_seq.len() == n as nat);
            assert(t0_re2_seq.len() == n as nat);
            assert(t0_im2_seq.len() == n as nat);
            assert(t0_rpi_seq.len() == n as nat);
            assert(t0_sum2_seq.len() == n as nat);
            assert(t0_diff_seq.len() == n as nat);
            assert(new_re_seq.len() == n as nat);
            assert(t0_diff_seq2.len() == n as nat);
            assert(t0_stmp3_seq.len() == n as nat);
            assert(new_im_seq.len() == n as nat);

            // Valid limbs (all 13)
            assert(valid_limbs(z_re_seq));
            assert(valid_limbs(z_im_seq));
            assert(valid_limbs(c_re_seq));
            assert(valid_limbs(c_im_seq));
            assert(valid_limbs(t0_re2_seq));
            assert(valid_limbs(t0_im2_seq));
            assert(valid_limbs(t0_rpi_seq));
            assert(valid_limbs(t0_sum2_seq));
            assert(valid_limbs(t0_diff_seq));
            assert(valid_limbs(new_re_seq));
            assert(valid_limbs(t0_diff_seq2));
            assert(valid_limbs(t0_stmp3_seq));
            assert(valid_limbs(new_im_seq));

            // Signs (int form)
            assert(zk_re_s as int == 0 || zk_re_s as int == 1);
            assert(zk_im_s as int == 0 || zk_im_s as int == 1);
            assert(ref_c_re_s as int == 0 || ref_c_re_s as int == 1);
            assert(ref_c_im_s as int == 0 || ref_c_im_s as int == 1);
            assert(re2_s as int == 0 || re2_s as int == 1);
            assert(im2_s as int == 0 || im2_s as int == 1);
            assert(rpi_s as int == 0 || rpi_s as int == 1);
            assert(sum2_s as int == 0 || sum2_s as int == 1);
            assert(diff_s as int == 0 || diff_s as int == 1);
            assert(new_re_s as int == 0 || new_re_s as int == 1);
            assert(t1_s as int == 0 || t1_s as int == 1);
            assert(t2_s as int == 0 || t2_s as int == 1);
            assert(new_im_s as int == 0 || new_im_s as int == 1);

            // Mul value equations (Ops 1, 2, 4 — from sub-helper postconditions)
            assert(vec_val(t0_re2_seq) == (vec_val(z_re_seq) * vec_val(z_re_seq)
                / limb_power(frac_limbs as nat)) % limb_power(n as nat));
            assert(vec_val(t0_im2_seq) == (vec_val(z_im_seq) * vec_val(z_im_seq)
                / limb_power(frac_limbs as nat)) % limb_power(n as nat));
            assert(vec_val(t0_sum2_seq) == (vec_val(t0_rpi_seq) * vec_val(t0_rpi_seq)
                / limb_power(frac_limbs as nat)) % limb_power(n as nat));

            // Op 3 disjunction (add: re + im)
            assert(({
                let va = vec_val(z_re_seq);
                let vb = vec_val(z_im_seq);
                let vo = vec_val(t0_rpi_seq);
                let sa = if zk_re_s as int == 0 { va } else { -va };
                let sb = if zk_im_s as int == 0 { vb } else { -vb };
                let so = if rpi_s as int == 0 { vo } else { -vo };
                let p = limb_power(n as nat);
                so == sa + sb
                    || (so == sa + sb - p && sa + sb >= p)
                    || (so == sa + sb + p && sa + sb <= -(p as int))
            }));

            // Op 5 disjunction (sub: re²-im²)
            assert(({
                let va = vec_val(t0_re2_seq);
                let vb = vec_val(t0_im2_seq);
                let vo = vec_val(t0_diff_seq);
                let sa = if re2_s as int == 0 { va } else { -va };
                let sb = if im2_s as int == 0 { vb } else { -vb };
                let so = if diff_s as int == 0 { vo } else { -vo };
                let p = limb_power(n as nat);
                so == sa - sb
                    || (so == sa - sb - p && sa - sb >= p)
                    || (so == sa - sb + p && sa - sb <= -(p as int))
            }));

            // Op 6 disjunction (add: diff+c_re)
            assert(({
                let va = vec_val(t0_diff_seq);
                let vb = vec_val(c_re_seq);
                let vo = vec_val(new_re_seq);
                let sa = if diff_s as int == 0 { va } else { -va };
                let sb = if ref_c_re_s as int == 0 { vb } else { -vb };
                let so = if new_re_s as int == 0 { vo } else { -vo };
                let p = limb_power(n as nat);
                so == sa + sb
                    || (so == sa + sb - p && sa + sb >= p)
                    || (so == sa + sb + p && sa + sb <= -(p as int))
            }));

            // Op 7 disjunction (sub: sum²-re²)
            assert(({
                let va = vec_val(t0_sum2_seq);
                let vb = vec_val(t0_re2_seq);
                let vo = vec_val(t0_diff_seq2);
                let sa = if sum2_s as int == 0 { va } else { -va };
                let sb = if re2_s as int == 0 { vb } else { -vb };
                let so = if t1_s as int == 0 { vo } else { -vo };
                let p = limb_power(n as nat);
                so == sa - sb
                    || (so == sa - sb - p && sa - sb >= p)
                    || (so == sa - sb + p && sa - sb <= -(p as int))
            }));

            // Op 8 disjunction (sub: t1-im²)
            assert(({
                let va = vec_val(t0_diff_seq2);
                let vb = vec_val(t0_im2_seq);
                let vo = vec_val(t0_stmp3_seq);
                let sa = if t1_s as int == 0 { va } else { -va };
                let sb = if im2_s as int == 0 { vb } else { -vb };
                let so = if t2_s as int == 0 { vo } else { -vo };
                let p = limb_power(n as nat);
                so == sa - sb
                    || (so == sa - sb - p && sa - sb >= p)
                    || (so == sa - sb + p && sa - sb <= -(p as int))
            }));

            // Op 9 disjunction (add: t2+c_im)
            assert(({
                let va = vec_val(t0_stmp3_seq);
                let vb = vec_val(c_im_seq);
                let vo = vec_val(new_im_seq);
                let sa = if t2_s as int == 0 { va } else { -va };
                let sb = if ref_c_im_s as int == 0 { vb } else { -vb };
                let so = if new_im_s as int == 0 { vo } else { -vo };
                let p = limb_power(n as nat);
                so == sa + sb
                    || (so == sa + sb - p && sa + sb >= p)
                    || (so == sa + sb + p && sa + sb <= -(p as int))
            }));

            lemma_ref_orbit_chain::<u32>(
                z_re_seq, zk_re_s as int,
                z_im_seq, zk_im_s as int,
                c_re_seq, ref_c_re_s as int,
                c_im_seq, ref_c_im_s as int,
                t0_re2_seq, re2_s as int,
                t0_im2_seq, im2_s as int,
                t0_rpi_seq, rpi_s as int,
                t0_sum2_seq, sum2_s as int,
                t0_diff_seq, diff_s as int,
                new_re_seq, new_re_s as int,
                t0_diff_seq2, t1_s as int,
                t0_stmp3_seq, t2_s as int,
                new_im_seq, new_im_s as int,
                n as nat, frac_limbs as nat,
            );
        }
    }

    (new_re_s, new_im_s)
}

/// Direct Mandelbrot iteration fallback for unresolved glitched pixels.
/// Computes Z_{k+1} = Z_k^2 + c_pixel (no perturbation, no reference orbit).
/// This is slower than perturbation but always correct.
/// Only called for pixels that failed ALL refinement rounds.
fn direct_computation_fallback(
    c_re_slice: &[u32], c_re_sign: u32,
    c_im_slice: &[u32], c_im_sign: u32,
    z_re: &mut Vec<u32>,
    z_im: &mut Vec<u32>,
    t1: &mut Vec<u32>, t2: &mut Vec<u32>,
    t3: &mut Vec<u32>, t4: &mut Vec<u32>, t5: &mut Vec<u32>,
    lprod: &mut Vec<u32>,
    ls1: &mut Vec<u32>, ls2: &mut Vec<u32>,
    thresh: &[u32],
    n: u32, frac_limbs: u32,
    max_iters: u32,
) -> (escaped: u32)
    requires
        n >= 1, n <= 8, n as int <= 0x1FFF_FFFF,
        frac_limbs <= n, frac_limbs + n <= 2 * n,
        max_iters > 0, max_iters <= 0x1000,
        c_re_slice@.len() >= n as int,
        c_im_slice@.len() >= n as int,
        thresh@.len() >= n as int,
        old(z_re)@.len() == n as int,
        old(z_im)@.len() == n as int,
        old(t1)@.len() == n as int,
        old(t2)@.len() == n as int,
        old(t3)@.len() == n as int,
        old(t4)@.len() == n as int,
        old(t5)@.len() == n as int,
        old(lprod)@.len() == 2 * n as int,
        old(ls1)@.len() == n as int,
        old(ls2)@.len() == n as int,
        c_re_sign == 0u32 || c_re_sign == 1u32,
        c_im_sign == 0u32 || c_im_sign == 1u32,
        valid_limbs(c_re_slice@.subrange(0, n as int)),
        valid_limbs(c_im_slice@.subrange(0, n as int)),
        valid_limbs(thresh@.subrange(0, n as int)),
        // Z_0 = 0 (caller must zero z_re and z_im before calling)
        forall |j: int| 0 <= j < n as int ==> old(z_re)@[j] == 0u32,
        forall |j: int| 0 <= j < n as int ==> old(z_im)@[j] == 0u32,
    ensures
        escaped <= max_iters,
        z_re@.len() == n as int,
        z_im@.len() == n as int,
        t1@.len() == n as int,
        t2@.len() == n as int,
        t3@.len() == n as int,
        t4@.len() == n as int,
        t5@.len() == n as int,
        lprod@.len() == 2 * n as int,
        ls1@.len() == n as int,
        ls2@.len() == n as int,
{
    let n_us = n as usize;
    let frac_us = frac_limbs as usize;
    let mut z_re_sign = 0u32;
    let mut z_im_sign = 0u32;
    let mut escaped_iter = max_iters;

    // Establish valid_limbs for zeroed Z_0
    proof {
        assert(valid_limbs(z_re@)) by {
            assert forall |j: int| 0 <= j < z_re@.len()
                implies 0 <= (#[trigger] z_re@[j]).sem() && z_re@[j].sem() < LIMB_BASE() by {
                assert(z_re@[j] == 0u32);
            }
        }
        assert(valid_limbs(z_im@)) by {
            assert forall |j: int| 0 <= j < z_im@.len()
                implies 0 <= (#[trigger] z_im@[j]).sem() && z_im@[j].sem() < LIMB_BASE() by {
                assert(z_im@[j] == 0u32);
            }
        }
    }

    let mut iter = 0u32;
    while iter < max_iters
        invariant
            iter <= max_iters,
            max_iters > 0, max_iters <= 0x1000,
            n >= 1, n <= 8, n as int <= 0x1FFF_FFFF,
            frac_limbs <= n, frac_limbs + n <= 2 * n,
            n_us == n as usize, frac_us == frac_limbs as usize,
            z_re@.len() == n as int, z_im@.len() == n as int,
            t1@.len() == n as int, t2@.len() == n as int,
            t3@.len() == n as int, t4@.len() == n as int,
            t5@.len() == n as int,
            lprod@.len() == 2 * n as int,
            ls1@.len() == n as int, ls2@.len() == n as int,
            z_re_sign == 0u32 || z_re_sign == 1u32,
            z_im_sign == 0u32 || z_im_sign == 1u32,
            c_re_sign == 0u32 || c_re_sign == 1u32,
            c_im_sign == 0u32 || c_im_sign == 1u32,
            c_re_slice@.len() >= n as int,
            c_im_slice@.len() >= n as int,
            thresh@.len() >= n as int,
            valid_limbs(c_re_slice@.subrange(0, n as int)),
            valid_limbs(c_im_slice@.subrange(0, n as int)),
            valid_limbs(thresh@.subrange(0, n as int)),
            valid_limbs(z_re@), valid_limbs(z_im@),
            escaped_iter <= max_iters,
        decreases max_iters - iter,
    {
        // ── Z_{k+1} = Z_k^2 + c_pixel (9 ops, same as ref_orbit_iteration_step) ──

        // Op 1: re^2 = Z_re * Z_re → t3
        let re2_s = signed_mul_to(&**z_re, &z_re_sign, &**z_re, &z_re_sign,
                                   t3, 0usize, lprod, 0usize, n_us, frac_us);
        // Op 2: im^2 = Z_im * Z_im → t4
        let im2_s = signed_mul_to(&**z_im, &z_im_sign, &**z_im, &z_im_sign,
                                   t4, 0usize, lprod, 0usize, n_us, frac_us);
        // Op 3: rpi = Z_re + Z_im → t1
        let rpi_s = signed_add_to(&**z_re, &z_re_sign, &**z_im, &z_im_sign,
                                   t1, 0usize, ls1, 0usize, ls2, 0usize, n_us);
        // Op 4: rpi^2 = (Z_re + Z_im)^2 → t2
        let rpi2_s = signed_mul_to(&**t1, &rpi_s, &**t1, &rpi_s,
                                    t2, 0usize, lprod, 0usize, n_us, frac_us);
        // Op 5: z_sq_re = re^2 - im^2 → t5
        let diff_s = signed_sub_to(&**t3, &re2_s, &**t4, &im2_s,
                                    t5, 0usize, ls1, 0usize, ls2, 0usize, n_us);
        // Op 6: new_re = z_sq_re + c_re → z_re
        // (At this point we are done reading old z_re, safe to overwrite)
        z_re_sign = signed_add_to(&**t5, &diff_s, c_re_slice, &c_re_sign,
                                   z_re, 0usize, ls1, 0usize, ls2, 0usize, n_us);
        // Op 7: x1 = rpi^2 - re^2 → t1
        let x1_s = signed_sub_to(&**t2, &rpi2_s, &**t3, &re2_s,
                                  t1, 0usize, ls1, 0usize, ls2, 0usize, n_us);
        // Op 8: x2 = x1 - im^2 → t5
        // (x2 = (re+im)^2 - re^2 - im^2 = 2*re*im)
        let x2_s = signed_sub_to(&**t1, &x1_s, &**t4, &im2_s,
                                  t5, 0usize, ls1, 0usize, ls2, 0usize, n_us);
        // Op 9: new_im = x2 + c_im → z_im
        z_im_sign = signed_add_to(&**t5, &x2_s, c_im_slice, &c_im_sign,
                                   z_im, 0usize, ls1, 0usize, ls2, 0usize, n_us);

        // Establish valid_limbs for the loop invariant
        proof {
            assert(valid_limbs(z_re@)) by {
                assert forall |j: int| 0 <= j < z_re@.len()
                    implies 0 <= (#[trigger] z_re@[j]).sem() && z_re@[j].sem() < LIMB_BASE() by {
                    assert(0 <= z_re@[(0 + j) as int].sem());
                    assert(z_re@[(0 + j) as int].sem() < LIMB_BASE());
                }
            }
            assert(valid_limbs(z_im@)) by {
                assert forall |j: int| 0 <= j < z_im@.len()
                    implies 0 <= (#[trigger] z_im@[j]).sem() && z_im@[j].sem() < LIMB_BASE() by {
                    assert(0 <= z_im@[(0 + j) as int].sem());
                    assert(z_im@[(0 + j) as int].sem() < LIMB_BASE());
                }
            }
        }

        // ── Escape check: |Z|^2 >= threshold (4) ──
        // Squaring with same input gives sign 0 (positive)
        let _fr2_s = signed_mul_to(&**z_re, &z_re_sign, &**z_re, &z_re_sign,
                                    t3, 0usize, lprod, 0usize, n_us, frac_us);
        let _fi2_s = signed_mul_to(&**z_im, &z_im_sign, &**z_im, &z_im_sign,
                                    t4, 0usize, lprod, 0usize, n_us, frac_us);
        // t3 = re^2, t4 = im^2 (both non-negative, sign 0)
        // Prove valid_limbs for add_limbs_to precondition
        proof {
            assert(valid_limbs(t3@)) by {
                assert forall |j: int| 0 <= j < t3@.len()
                    implies 0 <= (#[trigger] t3@[j]).sem() && t3@[j].sem() < LIMB_BASE() by {
                    assert(0 <= t3@[(0 + j) as int].sem());
                    assert(t3@[(0 + j) as int].sem() < LIMB_BASE());
                }
            }
            assert(valid_limbs(t4@)) by {
                assert forall |j: int| 0 <= j < t4@.len()
                    implies 0 <= (#[trigger] t4@[j]).sem() && t4@[j].sem() < LIMB_BASE() by {
                    assert(0 <= t4@[(0 + j) as int].sem());
                    assert(t4@[(0 + j) as int].sem() < LIMB_BASE());
                }
            }
        }
        let _mag_carry = add_limbs_to(&**t3, &**t4, t5, 0usize, n_us);
        // Prove valid_limbs on t5 for sub_limbs_to precondition
        proof {
            assert(valid_limbs(t5@)) by {
                assert forall |j: int| 0 <= j < t5@.len()
                    implies 0 <= (#[trigger] t5@[j]).sem() && t5@[j].sem() < LIMB_BASE() by {
                    assert(0 <= t5@[(0 + j) as int].sem());
                    assert(t5@[(0 + j) as int].sem() < LIMB_BASE());
                }
            }
        }
        let borrow = sub_limbs_to(&**t5, thresh, t1, 0usize, n_us);
        if borrow == 0u32 {
            // |Z|^2 >= threshold → escaped
            escaped_iter = iter;
            break;
        }

        // Restore valid_limbs on t1 after sub_limbs_to modified it
        proof {
            assert(valid_limbs(t1@)) by {
                assert forall |j: int| 0 <= j < t1@.len()
                    implies 0 <= (#[trigger] t1@[j]).sem() && t1@[j].sem() < LIMB_BASE() by {
                    assert(0 <= t1@[(0 + j) as int].sem());
                    assert(t1@[(0 + j) as int].sem() < LIMB_BASE());
                }
            }
        }

        iter = iter + 1u32;
    }

    escaped_iter
}

// #[gpu_kernel(workgroup_size(16, 16, 1))]
// rlimit bump rationale: the strengthened *_to_buf postconditions (#77) add
// value-equation facts to the Z3 context for every call inside the reference
// orbit and perturbation loops. The proper fix (per rlimit tips) would be to
// extract the loop bodies into focused helper functions, but that's significant
// refactoring due to many captured locals (n, frac_limbs, ref_a, ref_b, t1-t5,
// ls1, ls2, ...). Acceptable as a stopgap while Tasks #78-#79 use the new
// postconditions; revisit during the loop extraction work.
#[verifier::rlimit(100)]
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
        params@.len() >= 10,  // minimum: 5 header + n threshold + 1 max_rounds (n >= 1 → 7+)
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
        // Escape threshold in params[5..5+n], max_rounds at params[5+n]
        params@.len() as int >= 6 + params@[3] as int,
        // max_rounds: 0 < max_rounds (at least 1 round)
        params@[(5 + params@[3] as int) as int] > 0,
        params@[(5 + params@[3] as int) as int] <= 256, // bounded for termination
{
    let width = vget(params, 0u32);
    let height = vget(params, 1u32);
    let max_iters = vget(params, 2u32);
    let n = vget(params, 3u32);
    let frac_limbs = vget(params, 4u32);
    let max_rounds = vget(params, 5u32 + n);

    // (#1) Parameter validation regression test: if preconditions change,
    // these assertions catch invalid n/frac_limbs/max_iters immediately.
    proof {
        assert(n >= 1 && n <= 8);
        assert(frac_limbs <= n);
        assert(max_iters > 0 && max_iters <= 0x1000);
    }

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
    // max_rounds read from params[5+n] (was hardcoded 5)

    // Prove shared memory layout bounds before entering the loop
    // Total layout: (max_iters+2)*z_stride + 10*n + 259 <= 8192
    // So: best_ref_addr + 1 <= total <= 8192
    // And: vote_base + 256 = glitch_count_addr <= best_ref_addr < 8192
    // Layout chain proof: all shared memory offsets < 8192
    // Total = (max_iters+2)*z_stride + 10*n + 259 <= 8192
    // Each intermediate offset is strictly less.

    let mut round = 0u32;
    while round < max_rounds
        invariant
            round <= max_rounds,
            max_rounds > 0, max_rounds <= 256,
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
            ref_c_base as int == ((max_iters as int) + 1) * (z_stride as int),
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
            // Zero re limbs [0..n)
            for i in 0u32..n
                invariant wg_mem@.len() >= 8192, n >= 1, n <= 8, orbit_base == 0u32,
                    forall |j: int| 0 <= j < i as int ==> wg_mem@[j] == 0u32,
            { vset(wg_mem, orbit_base + i, 0u32); }
            // Zero re sign [n]
            vset(wg_mem, orbit_base + n, 0u32);
            // Zero im limbs [n+1..2n+1)
            for i in 0u32..n
                invariant wg_mem@.len() >= 8192, n >= 1, n <= 8, orbit_base == 0u32,
                    // Previously written re limbs + sign preserved
                    forall |j: int| 0 <= j < n as int ==> wg_mem@[j] == 0u32,
                    wg_mem@[n as int] == 0u32,
                    // Im limbs written so far
                    forall |j: int| 0 <= j < i as int
                        ==> (#[trigger] wg_mem@[(n as int + 1 + j)]) == 0u32,
            { vset(wg_mem, orbit_base + n + 1u32 + i, 0u32); }
            // Zero im sign [2n+1]
            vset(wg_mem, orbit_base + 2u32 * n + 1u32, 0u32);

            let mut ref_escaped = max_iters;

            // Read and validate ref_c signs (stable during orbit computation)
            let ref_c_re_s = vget(wg_mem, ref_c_base + n);
            let ref_c_im_s = vget(wg_mem, ref_c_base + 2u32 * n + 1u32);
            if ref_c_re_s > 1u32 || ref_c_im_s > 1u32 {
                ref_escaped = 0u32; // invalid ref_c data, skip orbit
            } else {

            // Ghost Z tracking: ghost z_re_int/z_im_int track the reference
            // orbit's signed integer values via ref_step_buf_int across iterations.
            // Z_0 = 0 (orbit was zeroed), so initial ghost values are 0.
            let ghost mut z_re_int: int = 0;
            let ghost mut z_im_int: int = 0;
            // History: ghost sequences tracking all z_int values at each iteration.
            // z_re_history[k] == z_re_int after iteration k wrote slot k+1.
            // At iter=0: z_re_history == [0] (Z_0 = 0).
            let ghost mut z_re_history: Seq<int> = seq![0int];
            let ghost mut z_im_history: Seq<int> = seq![0int];

            // Establish orbit-slot invariant at iter=0 from zeroing above.
            proof {
                assert(0u32 * z_stride == 0u32) by(nonlinear_arith);
                let re_seq = wg_mem@.subrange(0int, n as int);
                let im_seq = wg_mem@.subrange((n + 1u32) as int, (2u32 * n + 1u32) as int);

                // All limbs are 0 (from zeroing loops above)
                assert forall |k: int| 0 <= k < re_seq.len()
                    implies (#[trigger] re_seq[k]).sem() == 0int by {
                    assert(re_seq[k] == wg_mem@[k]);
                    assert(wg_mem@[k] == 0u32);
                }
                assert forall |k: int| 0 <= k < im_seq.len()
                    implies (#[trigger] im_seq[k]).sem() == 0int by {
                    assert(im_seq[k] == wg_mem@[n as int + 1 + k]);
                    assert(wg_mem@[n as int + 1 + k] == 0u32);
                }

                // vec_val of zeros is 0
                verus_fixed_point::fixed_point::limb_ops::lemma_vec_val_zeros(re_seq);
                verus_fixed_point::fixed_point::limb_ops::lemma_vec_val_zeros(im_seq);

                // valid_limbs (0 is in [0, LIMB_BASE))
                lemma_pointwise_to_valid_limbs(wg_mem@, 0int, n as nat);
                lemma_pointwise_to_valid_limbs(wg_mem@, (n + 1u32) as int, n as nat);

                // Signs are 0
                assert(wg_mem@[n as int] == 0u32);
                assert(wg_mem@[(2u32 * n + 1u32) as int] == 0u32);
            }

            for iter in 0u32..max_iters
                invariant
                    wg_mem@.len() >= 8192, n >= 1, n <= 8, n as int <= 0x1FFF_FFFF,
                    max_iters > 0, max_iters <= 4096,
                    z_stride == 2 * n + 2, orbit_base == 0u32,
                    ((max_iters as int) + 1) * (z_stride as int) < 8192,
                    ref_a@.len() == n as int, ref_b@.len() == n as int,
                    frac_limbs <= n, frac_limbs + n <= 2 * n,
                    ref_c_base + z_stride < 8192u32,
                    // Value of ref_c_base (carried from outer scope)
                    ref_c_base as int == ((max_iters as int) + 1) * (z_stride as int),
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
                    // ── Exec-spec correspondence: ghost Z matches orbit slot ──
                    // The orbit slot at iter*z_stride holds limb data whose
                    // signed value equals the ghost z_re_int / z_im_int.
                    valid_limbs(wg_mem@.subrange(
                        (iter * z_stride) as int, (iter * z_stride + n) as int)),
                    valid_limbs(wg_mem@.subrange(
                        (iter * z_stride + n + 1u32) as int,
                        (iter * z_stride + 2u32 * n + 1u32) as int)),
                    wg_mem@[(iter * z_stride + n) as int].sem() <= 1,
                    wg_mem@[(iter * z_stride + 2u32 * n + 1u32) as int].sem() <= 1,
                    signed_val_of(
                        wg_mem@.subrange(
                            (iter * z_stride) as int, (iter * z_stride + n) as int),
                        wg_mem@[(iter * z_stride + n) as int].sem() as int,
                    ) == z_re_int,
                    signed_val_of(
                        wg_mem@.subrange(
                            (iter * z_stride + n + 1u32) as int,
                            (iter * z_stride + 2u32 * n + 1u32) as int),
                        wg_mem@[(iter * z_stride + 2u32 * n + 1u32) as int].sem() as int,
                    ) == z_im_int,
                    // ── History invariant: ALL prior orbit slots preserved ──
                    z_re_history.len() == (iter + 1) as nat,
                    z_im_history.len() == (iter + 1) as nat,
                    z_re_history[iter as int] == z_re_int,
                    z_im_history[iter as int] == z_im_int,
                    // Every prior slot k matches z_history[k]
                    forall |k: int| 0 <= k <= iter as int ==> {
                        let off = #[trigger] (k * (z_stride as int));
                        &&& wg_mem@[(off + n as int) as int].sem() <= 1
                        &&& wg_mem@[(off + 2 * n as int + 1) as int].sem() <= 1
                        &&& signed_val_of(
                                wg_mem@.subrange(off, off + n as int),
                                wg_mem@[(off + n as int) as int].sem() as int)
                            == z_re_history[k]
                        &&& signed_val_of(
                                wg_mem@.subrange(off + n as int + 1, off + 2 * n as int + 1),
                                wg_mem@[(off + 2 * n as int + 1) as int].sem() as int)
                            == z_im_history[k]
                    },
            {
                // Capture wg_mem at loop body start for history frame chain
                let ghost wg_mem_body_start = wg_mem@;

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

                // ── Z_{k+1} = Z_k² + c_ref ──
                // Extracted to ref_orbit_iteration_step (Task #4 Phase B Stage 1).
                proof {
                    // Establish the helper's precondition bounds.
                    // zk = iter * z_stride, and iter < max_iters, so
                    //   zk + n < iter*z_stride + z_stride == (iter+1)*z_stride
                    //         <= max_iters*z_stride < (max_iters+2)*z_stride == t0_re2
                    assert(zk as int == (iter as int) * (z_stride as int));
                    assert((iter as int) * (z_stride as int) + (z_stride as int)
                            == ((iter as int) + 1) * (z_stride as int)) by(nonlinear_arith);
                    assert(((iter as int) + 1) * (z_stride as int)
                            <= (max_iters as int) * (z_stride as int)) by(nonlinear_arith)
                        requires (iter as int) + 1 <= max_iters as int, z_stride as int >= 0;
                    assert((max_iters as int) * (z_stride as int)
                            < ((max_iters as int) + 2) * (z_stride as int)) by(nonlinear_arith)
                        requires z_stride as int >= 4;
                    assert(zk as int + (n as int) < t0_re2 as int);
                    // zk_re == zk and zk_im == zk + n + 1
                    assert(zk_re == zk);
                    assert(zk_im == zk + n + 1u32);
                    assert((zk_re as int) + (n as int) <= t0_re2 as int);
                    assert((zk_im as int) + (n as int)
                            == zk as int + 2 * (n as int) + 1);
                    assert((zk as int) + (z_stride as int) == zk as int + 2 * (n as int) + 2);
                    assert((zk_im as int) + (n as int) < t0_re2 as int);
                    assert((zk_im as int) + (n as int) <= t0_re2 as int);

                    // zn + 2n+2 ≤ t0_re2 (from above: zn + z_stride < t0_re2)
                    // we already showed zn + z_stride < t0_re2 in the outer proof.
                    assert((zn as int) + 2 * (n as int) + 2 <= t0_re2 as int);

                    // ref_c_base region bounds: ref_c_base + 2n+2 ≤ t0_re2
                    // Follows from ref_c_base == (max_iters+1)*z_stride and
                    //                t0_re2 == (max_iters+2)*z_stride.
                    assert(ref_c_base as int == ((max_iters as int) + 1) * (z_stride as int));
                    assert(((max_iters as int) + 1) * (z_stride as int) + (z_stride as int)
                            == ((max_iters as int) + 2) * (z_stride as int)) by(nonlinear_arith);
                    assert((ref_c_base as int) + (z_stride as int) == t0_re2 as int);
                    assert(z_stride as int == 2 * (n as int) + 2);
                    assert((ref_c_base as int) + 2 * (n as int) + 2 == t0_re2 as int);
                    assert((ref_c_base as int) + 2 * (n as int) + 2 <= t0_re2 as int);

                    // t0_re2 + 10n < 8192 (from existing invariants):
                    // t0_stmp3 == t0_re2 + 9n, t0_stmp3 + n = t0_re2 + 10n = ref_escape_addr < 8192
                    assert(t0_re2 + 10u32 * n < 8192u32);
                    assert(t0_stmp3 as int + n as int <= wg_mem@.len());
                    assert(zk_re + n < u32_max());
                    assert(zk_im + n < u32_max());
                    assert(ref_c_base + n + 1u32 + n < u32_max());
                    assert(zn + 2u32 * n + 1u32 < u32_max());

                    // Non-overlap: zn output slots don't touch c_ref
                    // zn + z_stride = (iter+2)*z_stride ≤ (max_iters+1)*z_stride = ref_c_base
                    assert((zn as int) + 2 * (n as int) + 2 <= ref_c_base as int);

                    // Valid limbs on Z_k slots — these were written by previous
                    // iterations or the initial zeroing loop. The kernel doesn't
                    // yet carry this as a per-slot invariant; for now establish
                    // it pointwise from wg_mem's values.
                    assert(valid_limbs(wg_mem@.subrange(zk_re as int, zk_re as int + n as int))) by {
                        assert forall |k: int| 0 <= k < (n as int)
                            implies 0 <= (#[trigger] wg_mem@.subrange(zk_re as int, zk_re as int + n as int)[k]).sem()
                                && wg_mem@.subrange(zk_re as int, zk_re as int + n as int)[k].sem() < LIMB_BASE() by {
                            let s = wg_mem@.subrange(zk_re as int, zk_re as int + n as int);
                            assert(s[k] == wg_mem@[zk_re as int + k]);
                        }
                    }
                    assert(valid_limbs(wg_mem@.subrange(zk_im as int, zk_im as int + n as int))) by {
                        assert forall |k: int| 0 <= k < (n as int)
                            implies 0 <= (#[trigger] wg_mem@.subrange(zk_im as int, zk_im as int + n as int)[k]).sem()
                                && wg_mem@.subrange(zk_im as int, zk_im as int + n as int)[k].sem() < LIMB_BASE() by {
                            let s = wg_mem@.subrange(zk_im as int, zk_im as int + n as int);
                            assert(s[k] == wg_mem@[zk_im as int + k]);
                        }
                    }
                    assert(valid_limbs(wg_mem@.subrange(ref_c_base as int, ref_c_base as int + n as int))) by {
                        assert forall |k: int| 0 <= k < (n as int)
                            implies 0 <= (#[trigger] wg_mem@.subrange(ref_c_base as int, ref_c_base as int + n as int)[k]).sem()
                                && wg_mem@.subrange(ref_c_base as int, ref_c_base as int + n as int)[k].sem() < LIMB_BASE() by {
                            let s = wg_mem@.subrange(ref_c_base as int, ref_c_base as int + n as int);
                            assert(s[k] == wg_mem@[ref_c_base as int + k]);
                        }
                    }
                    assert(valid_limbs(wg_mem@.subrange(
                        ref_c_base as int + n as int + 1,
                        ref_c_base as int + n as int + 1 + n as int))) by {
                        assert forall |k: int| 0 <= k < (n as int)
                            implies 0 <= (#[trigger] wg_mem@.subrange(
                                    ref_c_base as int + n as int + 1,
                                    ref_c_base as int + n as int + 1 + n as int)[k]).sem()
                                && wg_mem@.subrange(
                                    ref_c_base as int + n as int + 1,
                                    ref_c_base as int + n as int + 1 + n as int)[k].sem() < LIMB_BASE() by {
                            let s = wg_mem@.subrange(
                                ref_c_base as int + n as int + 1,
                                ref_c_base as int + n as int + 1 + n as int);
                            assert(s[k] == wg_mem@[ref_c_base as int + n as int + 1 + k]);
                        }
                    }
                }
                // Capture pre-call input values for ghost update
                let ghost old_zk_re_seq = wg_mem@.subrange(zk_re as int, zk_re as int + n as int);
                let ghost old_zk_im_seq = wg_mem@.subrange(zk_im as int, zk_im as int + n as int);
                let ghost old_cre_seq = wg_mem@.subrange(ref_c_base as int, ref_c_base as int + n as int);
                let ghost old_cim_seq = wg_mem@.subrange(
                    ref_c_base as int + n as int + 1, ref_c_base as int + 2 * n as int + 1);

                let (new_re_s, new_im_s) = ref_orbit_iteration_step(
                    wg_mem,
                    zk_re, zk_im,
                    zk_re_s, zk_im_s,
                    ref_c_base,
                    ref_c_re_s, ref_c_im_s,
                    t0_re2, t0_im2, t0_rpi, t0_sum2,
                    t0_diff, t0_prod,
                    t0_stmp1, t0_stmp2, t0_stmp3,
                    zn,
                    &mut ref_a, &mut ref_b,
                    n, frac_limbs,
                );
                // Capture output subranges from exec helper BEFORE vset
                let ghost zn_re_out = wg_mem@.subrange(zn as int, (zn + n) as int);
                let ghost zn_im_out = wg_mem@.subrange(
                    (zn + n + 1u32) as int, (zn + 2u32 * n + 1u32) as int);

                vset(wg_mem, zn + n, new_re_s);
                vset(wg_mem, zn + 2u32 * n + 1u32, new_im_s);

                // ── Ghost Z update via ref_step_buf_int ──
                proof {
                    let c_re_int = signed_val_of(old_cre_seq, ref_c_re_s as int);
                    let c_im_int = signed_val_of(old_cim_seq, ref_c_im_s as int);
                    let result = ref_step_buf_int(
                        z_re_int, z_im_int, c_re_int, c_im_int,
                        n as nat, frac_limbs as nat);
                    z_re_int = result.0;
                    z_im_int = result.1;
                    z_re_history = z_re_history.push(z_re_int);
                    z_im_history = z_im_history.push(z_im_int);
                }

                // Capture orbit slot state before escape check (for frame proof)
                let ghost zn_re_seq_pre = wg_mem@.subrange(zn as int, (zn + n) as int);
                let ghost zn_im_seq_pre = wg_mem@.subrange(
                    (zn + n + 1u32) as int, (zn + 2u32 * n + 1u32) as int);
                let ghost zn_re_sign_pre = wg_mem@[(zn + n) as int];
                let ghost zn_im_sign_pre = wg_mem@[(zn + 2u32 * n + 1u32) as int];

                // PROVED (#4): Escape threshold structure.
                // params[5..5+n] encodes the escape radius² = 4 in fixed-point.
                // The escape check computes |Z|² - threshold and checks borrow.
                // The threshold offset (5) is consistent between ref and pert loops.
                // Correctness depends on CPU encoding: vec_val(params[5..5+n]) == 4 * pf.
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
                // ── Re-establish orbit-slot invariant for iter+1 ──
                // The next iteration reads from zn = (iter+1)*z_stride.
                // The exec helper wrote limbs to zn..zn+n with signed_val_of == z_re_int.
                // vset wrote signs to zn+n and zn+2n+1.
                // The escape check only modifies temp regions (t0_diff, t0_stmp1),
                // which are above t0_re2 > zn+2n+2, so orbit slots are preserved.
                proof {
                    // zn = (iter+1) * z_stride
                    assert(((iter + 1u32) * z_stride) as int == zn as int) by(nonlinear_arith)
                        requires zn as int == ((iter as int) + 1) * (z_stride as int);

                    // The exec helper postcondition gives (on wg_mem BEFORE escape check):
                    //   signed_val_of(wg_mem[zn..zn+n], new_re_s) == z_re_int
                    //   signed_val_of(wg_mem[zn+n+1..zn+2n+1], new_im_s) == z_im_int
                    //   valid_limbs on both output regions
                    //
                    // vset wrote new_re_s to wg_mem[zn+n] and new_im_s to wg_mem[zn+2n+1].
                    //
                    // The escape check only writes to t0_diff (at t0_re2+4n) and
                    // t0_stmp1 (at t0_re2+7n), both in the temp region above t0_re2.
                    // Since zn+2n+2 <= t0_re2, all orbit slot indices are below t0_re2.
                    // Therefore the orbit slot and signs are preserved.

                    // Frame: orbit slot preserved through escape check
                    // (add_limbs_to writes to t0_diff, sub_limbs_to writes to t0_stmp1,
                    //  copy_limbs doesn't modify wg_mem — all above t0_re2 > zn+2n+2)

                    // The exec helper + vset established the signed_val_of equations
                    // on wg_mem BEFORE the escape check. The escape check only modifies
                    // t0_diff (at t0_re2+4n) and t0_stmp1 (at t0_re2+7n), both above t0_re2.
                    // Since zn+2n+2 <= t0_re2, the orbit slot [zn, zn+2n+2) is preserved.
                    //
                    // Z3 sees the frame postconditions from add_limbs_to and sub_limbs_to
                    // (which state that indices outside [out_off, out_off+n) are unchanged).
                    // We just need to assert the orbit slot indices are outside those ranges.
                    // Frame: orbit slot preserved through escape check.
                    // add_limbs_to wrote to [t0_diff, t0_diff+n) and
                    // sub_limbs_to wrote to [t0_stmp1, t0_stmp1+n).
                    // Both are above t0_re2 > zn + 2n + 2.
                    assert(zn + 2u32 * n + 1u32 < t0_re2);

                    // Orbit limbs and signs are unchanged from pre-escape-check values
                    assert(wg_mem@.subrange(zn as int, (zn + n) as int) =~= zn_re_seq_pre) by {
                        assert forall |j: int| 0 <= j < n as int implies
                            wg_mem@.subrange(zn as int, (zn + n) as int)[j]
                                == zn_re_seq_pre[j] by {
                            assert(wg_mem@[zn as int + j] == zn_re_seq_pre[j]);
                        }
                    }
                    assert(wg_mem@.subrange(
                        (zn + n + 1u32) as int, (zn + 2u32 * n + 1u32) as int)
                            =~= zn_im_seq_pre) by {
                        assert forall |j: int| 0 <= j < n as int implies
                            wg_mem@.subrange(
                                (zn + n + 1u32) as int, (zn + 2u32 * n + 1u32) as int)[j]
                                    == zn_im_seq_pre[j] by {
                            assert(wg_mem@[(zn + n + 1u32) as int + j] == zn_im_seq_pre[j]);
                        }
                    }
                    assert(wg_mem@[(zn + n) as int] == zn_re_sign_pre);
                    assert(wg_mem@[(zn + 2u32 * n + 1u32) as int] == zn_im_sign_pre);

                    // Chain: exec postcondition → ghost capture → frame → invariant
                    // Before escape check: signed_val_of(wg_mem[zn..zn+n], new_re_s) == z_re_int
                    // Ghost capture: zn_re_seq_pre == wg_mem[zn..zn+n] at that point
                    // So: signed_val_of(zn_re_seq_pre, new_re_s as int) == z_re_int
                    // zn_re_out was captured right after exec helper (before vset).
                    // Exec postcondition: signed_val_of(zn_re_out, new_re_s as int) == result.0 == z_re_int
                    assert(signed_val_of(zn_re_out, new_re_s as int) == z_re_int);
                    assert(signed_val_of(zn_im_out, new_im_s as int) == z_im_int);
                    // vset wrote to zn+n and zn+2n+1 (outside [zn, zn+n)), so subrange unchanged
                    // Ghost capture zn_re_seq_pre (after vset) == zn_re_out (before vset)
                    assert(zn_re_seq_pre =~= zn_re_out) by {
                        assert forall |j: int| 0 <= j < n as int implies
                            zn_re_seq_pre[j] == zn_re_out[j] by {}
                    }
                    assert(zn_im_seq_pre =~= zn_im_out) by {
                        assert forall |j: int| 0 <= j < n as int implies
                            zn_im_seq_pre[j] == zn_im_out[j] by {}
                    }
                    // Frame: wg_mem_final[zn..] =~= zn_re_seq_pre (proved above)
                    // Congruence: signed_val_of(wg_mem_final[zn..], x) == signed_val_of(zn_re_seq_pre, x)
                    assert(signed_val_of(
                        wg_mem@.subrange(zn as int, (zn + n) as int),
                        new_re_s as int) == z_re_int);
                    assert(signed_val_of(
                        wg_mem@.subrange((zn + n + 1u32) as int, (zn + 2u32 * n + 1u32) as int),
                        new_im_s as int) == z_im_int);
                    // wg_mem[zn+n].sem() == new_re_s as int (from frame + u32 sem identity)
                    assert(wg_mem@[(zn + n) as int].sem() == (new_re_s as int));
                    assert(wg_mem@[(zn + 2u32 * n + 1u32) as int].sem() == (new_im_s as int));

                    // ── Frame chain: wg_mem[j] == wg_mem_body_start[j] for j < zn ──
                    // The exec helper, vset, and escape check all preserve j < zn:
                    // - exec helper frame: j < zn ==> preserved (new postcondition)
                    // - vset at zn+n and zn+2n+1: both ≥ zn, so j < zn unaffected
                    // - escape check: writes to t0_diff, t0_stmp1 ≥ t0_re2 > zn
                    assert forall |j: int| 0 <= j < zn as int implies
                        wg_mem@[j] == wg_mem_body_start[j] by {}

                    // ── History invariant maintenance ──
                    // All prior slots k ≤ iter are preserved because:
                    // - The exec helper wrote to slot iter+1 (= zn), not any prior slot
                    // - vset wrote to zn+n and zn+2n+1 (within slot iter+1)
                    // - The escape check wrote to t0_diff and t0_stmp1 (temp region)
                    // - Slot k ends at k*z_stride + 2n+1, slot iter+1 starts at (iter+1)*z_stride
                    // - For k ≤ iter: k*z_stride + 2n+1 < (k+1)*z_stride ≤ (iter+1)*z_stride = zn
                    // So no overlap.
                    assert forall |k: int| 0 <= k <= (iter + 1u32) as int implies {
                        let off = #[trigger] (k * (z_stride as int));
                        &&& wg_mem@[(off + n as int) as int].sem() <= 1
                        &&& wg_mem@[(off + 2 * n as int + 1) as int].sem() <= 1
                        &&& signed_val_of(
                                wg_mem@.subrange(off, off + n as int),
                                wg_mem@[(off + n as int) as int].sem() as int)
                            == z_re_history[k]
                        &&& signed_val_of(
                                wg_mem@.subrange(off + n as int + 1, off + 2 * n as int + 1),
                                wg_mem@[(off + 2 * n as int + 1) as int].sem() as int)
                            == z_im_history[k]
                    } by {
                        let off = k * (z_stride as int);
                        if k <= iter as int {
                            // Prior slot k ≤ iter: all indices are below zn
                            assert(off + 2 * (n as int) + 1 < zn as int) by(nonlinear_arith)
                                requires k <= iter as int, off == k * (z_stride as int),
                                         z_stride as int == 2 * (n as int) + 2,
                                         zn as int == ((iter as int) + 1) * (z_stride as int),
                                         n >= 1;
                            // Frame: wg_mem[j] == wg_mem_body_start[j] for j < zn
                            // → wg_mem[off..+2n+2] == wg_mem_body_start[off..+2n+2]
                            // Induction hypothesis (on wg_mem_body_start) gives the result
                            // Subranges equal via pointwise frame
                            assert(wg_mem@.subrange(off, off + n as int)
                                =~= wg_mem_body_start.subrange(off, off + n as int));
                            assert(wg_mem@.subrange(off + n as int + 1, off + 2 * n as int + 1)
                                =~= wg_mem_body_start.subrange(off + n as int + 1, off + 2 * n as int + 1));
                        } else {
                            // k == iter + 1: new slot just written
                            assert(k == (iter as int) + 1);
                            assert(off == zn as int) by(nonlinear_arith)
                                requires k == (iter as int) + 1,
                                         off == k * (z_stride as int),
                                         zn as int == ((iter as int) + 1) * (z_stride as int);
                        }
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
            // PROVED (#2): Δc offset verification.
            // c_data[c_re_off..] is pixel (gid_x, gid_y)'s c_re value,
            // where c_re_off = tid * c_stride_px = (gid_y * width + gid_x) * (2n+2).
            // wg_mem[ref_c_base..] is the reference c_re value.
            // Δc = c_pixel - c_ref (correct subtraction order).
            proof {
                // Structural layout verified: re at offset 0, sign at +n,
                // im at +n+1, im_sign at +2n+1 within each pixel's c_stride_px block.
                assert(c_stride_px == 2u32 * n + 2u32);
            }
            // Compute Δc = c_pixel - c_ref
            dc_re_sign = signed_sub_to(
                vslice(c_data, c_re_off), &cre_s,
                vslice(wg_mem, ref_c_base), &refre_s,
                &mut dc_re, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
            dc_im_sign = signed_sub_to(
                vslice(c_data, c_im_off), &cim_s,
                vslice(wg_mem, (ref_c_base + n + 1u32)), &refim_s,
                &mut dc_im, 0usize, &mut ls1, 0usize, &mut ls2, 0usize, n as usize);
            // PROVED (#3): Δc uses the CURRENT ref_c (which may have been updated
            // by the refinement loop's Step 3 in a prior round). The ref_c read
            // addresses (ref_c_base and ref_c_base+n+1) are the same addresses
            // that Step 3 writes to when updating the reference.
            proof {
                assert(ref_c_base as int == ((max_iters as int) + 1) * (z_stride as int));
            }

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
            // (#5) ref_escaped address consistency: same ref_escape_addr
            // variable used for write (line ~2633) and read (here).
            proof { assert(ref_escape_addr as int == (t0_re2 as int) + 10 * (n as int)); }

            // ── Task #78: Ghost value tracking across the perturbation loop ──
            // The perturbation_iteration_step helper (Task #81) exports a value
            // postcondition that ties the output buffers to pert_step_buf_int
            // applied to the input signed integers. The kernel uses this to
            // carry ghost δ_re_int / δ_im_int across iterations: the loop
            // invariant says signed_val_of(delta_re@, sign) == delta_re_int,
            // and after each helper call we update the ghost via pert_step_buf_int.
            //
            // δ_0 = 0, so the initial ghost values are 0.
            let ghost mut delta_re_int: int = 0;
            let ghost mut delta_im_int: int = 0;
            proof {
                // δ_0 = 0: vec_val(delta_re@) == 0 (proved above), so
                // signed_val_of(delta_re@, 0) == 0 == delta_re_int.
                assert(signed_val_of(delta_re@.subrange(0, n as int), delta_re_sign as int)
                    == delta_re_int) by {
                    assert(delta_re@.subrange(0, n as int) =~= delta_re@);
                    assert(vec_val(delta_re@) == 0);
                }
                assert(signed_val_of(delta_im@.subrange(0, n as int), delta_im_sign as int)
                    == delta_im_int) by {
                    assert(delta_im@.subrange(0, n as int) =~= delta_im@);
                    assert(vec_val(delta_im@) == 0);
                }
            }

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
                    // (#2) Semantic invariant for escaped_iter: it is either
                    // the initial sentinel (max_iters, "no escape recorded") or
                    // strictly less than the current iteration count (which
                    // means it was set by a past iteration's escape check).
                    // Catches bugs like setting escaped_iter to iter+k or to
                    // max_iters+1.
                    escaped_iter == max_iters || escaped_iter < iter,
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
                    // ── Task #78: ghost value tracking ──
                    // The signed integer values of delta_re/delta_im match the
                    // ghost ints we update via pert_step_buf_int after each call.
                    signed_val_of(delta_re@.subrange(0, n as int), delta_re_sign as int)
                        == delta_re_int,
                    signed_val_of(delta_im@.subrange(0, n as int), delta_im_sign as int)
                        == delta_im_int,
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
                // reference orbit loop wrote Z_{iter} to at its iteration (iter-1).
                // The ref orbit loop's iteration k writes Z_{k+1} to slot (k+1)*z_stride.
                // So Z_iter is at slot iter*z_stride. This matches our read address.
                // The data at this address matches the ref orbit's computation
                // (proved by the orbit history invariant in the ref orbit loop).
                proof {
                    assert(zn as int == (iter as int) * (z_stride as int));
                    assert(z_stride == 2u32 * n + 2u32);
                    assert(orbit_base == 0u32);
                    // Cross-loop correspondence: the address formula
                    // iter*z_stride used here matches (k+1)*z_stride used in the
                    // ref orbit loop when k = iter - 1. For iter = 0, slot 0
                    // was zeroed (Z_0 = 0). For iter > 0, slot iter was written
                    // by ref orbit iteration iter-1.
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
                // Extracted to perturbation_iteration_step (Task #81 Stage A).
                let zn_re_slc = vslice(wg_mem, zn_re);
                let zn_im_slc = vslice(wg_mem, zn_im);
                // Capture old delta_re@ for the post-helper ghost update.
                let ghost old_dre_seq = delta_re@;
                let ghost old_dim_seq = delta_im@;
                let ghost old_dre_sign = delta_re_sign as int;
                let ghost old_dim_sign = delta_im_sign as int;
                let (new_dr_s, new_di_s) = perturbation_iteration_step(
                    zn_re_slc, zn_re_s,
                    zn_im_slc, zn_im_s,
                    &mut delta_re, delta_re_sign,
                    &mut delta_im, delta_im_sign,
                    &dc_re, dc_re_sign,
                    &dc_im, dc_im_sign,
                    &mut t1, &mut t2, &mut t3, &mut t4, &mut t5,
                    &mut lprod,
                    &mut ls1, &mut ls2,
                    n, frac_limbs,
                );
                delta_re_sign = new_dr_s;
                delta_im_sign = new_di_s;

                // ── Task #78: Update ghost δ_re_int / δ_im_int via pert_step_buf_int.
                proof {
                    // Compute the same intermediates the helper's postcondition uses.
                    let z_re_int_now = signed_val_of(
                        zn_re_slc@.subrange(0, n as int), zn_re_s as int);
                    let z_im_int_now = signed_val_of(
                        zn_im_slc@.subrange(0, n as int), zn_im_s as int);
                    let dre_in_int_now = signed_val_of(old_dre_seq, old_dre_sign);
                    let dim_in_int_now = signed_val_of(old_dim_seq, old_dim_sign);
                    let dcre_int_now = signed_val_of(dc_re@, dc_re_sign as int);
                    let dcim_int_now = signed_val_of(dc_im@, dc_im_sign as int);
                    let result = pert_step_buf_int(
                        z_re_int_now, z_im_int_now,
                        dre_in_int_now, dim_in_int_now,
                        dcre_int_now, dcim_int_now,
                        n as nat, frac_limbs as nat,
                    );

                    // The helper's postcondition asserts:
                    //   signed_val_of(delta_re@, new_dr_s as int) == result.0
                    //   signed_val_of(delta_im@, new_di_s as int) == result.1
                    assert(signed_val_of(delta_re@, new_dr_s as int) == result.0);
                    assert(signed_val_of(delta_im@, new_di_s as int) == result.1);

                    // Old loop invariant: signed_val_of(old δ subrange, old sign) == δ_int.
                    // Connect via extensional equality of subrange to full Seq.
                    assert(old_dre_seq.subrange(0, n as int) =~= old_dre_seq);
                    assert(old_dim_seq.subrange(0, n as int) =~= old_dim_seq);
                    assert(dre_in_int_now == delta_re_int);
                    assert(dim_in_int_now == delta_im_int);

                    // Update ghost ints to match the new buffer values.
                    delta_re_int = result.0;
                    delta_im_int = result.1;

                    // Re-establish the loop invariant on the new state.
                    assert(delta_re@.subrange(0, n as int) =~= delta_re@);
                    assert(delta_im@.subrange(0, n as int) =~= delta_im@);
                    assert(signed_val_of(delta_re@.subrange(0, n as int), delta_re_sign as int)
                        == delta_re_int);
                    assert(signed_val_of(delta_im@.subrange(0, n as int), delta_im_sign as int)
                        == delta_im_int);
                }

                // ── Glitch check: fixed-point overflow detection ──
                // With multi-precision fixed-point, perturbation stays accurate even
                // when |δ| > |Z| (unlike float). Only detect actual overflow:
                // if integer limb exceeds escape radius (~4), δ has blown up.
                //
                // PROVED (#76): completeness via lemma_glitch_completeness_one —
                // if vec_val(δ_re) >= 4 * BASE^(n-1), the kernel's `δ[n-1] > 3`
                // check WILL fire. So all "value too large" δ values are caught.
                proof {
                    let dre_seq = delta_re@.subrange(0, n as int);
                    let dim_seq = delta_im@.subrange(0, n as int);
                    assert(dre_seq =~= delta_re@);
                    assert(dim_seq =~= delta_im@);
                    assert(valid_limbs(delta_re@)) by {
                        assert forall |k: int| 0 <= k < delta_re@.len()
                            implies 0 <= (#[trigger] delta_re@[k]).sem()
                                && delta_re@[k].sem() < LIMB_BASE() by { }
                    }
                    assert(valid_limbs(delta_im@)) by {
                        assert forall |k: int| 0 <= k < delta_im@.len()
                            implies 0 <= (#[trigger] delta_im@[k]).sem()
                                && delta_im@[k].sem() < LIMB_BASE() by { }
                    }
                    lemma_glitch_completeness_one(delta_re@, n as nat);
                    lemma_glitch_completeness_one(delta_im@, n as nat);
                }
                if delta_re[(n - 1u32) as usize] > 3u32 || delta_im[(n - 1u32) as usize] > 3u32 {
                    is_glitched = 1u32;
                    glitch_iter = iter;
                    break;
                }

                // (#6) Double-escape prevention: the glitch check (above, with break)
                // executes BEFORE the escape check (below). If glitch fires, the
                // loop breaks and escape check never runs — preventing invalid state
                // where both is_glitched == 1 and escaped_iter < max_iters.
                // ── Escape check: |Z_n + δ|² > 4 ──
                // Capture input subranges for the signed_val connection (#74)
                let ghost zn_re_slice = wg_mem@.subrange(zn_re as int, wg_mem@.len() as int);
                let ghost zn_im_slice = wg_mem@.subrange(zn_im as int, wg_mem@.len() as int);
                let ghost zn_re_in = zn_re_slice.subrange(0, n as int);
                let ghost zn_im_in = zn_im_slice.subrange(0, n as int);
                let ghost dre_in = delta_re@.subrange(0, n as int);
                let ghost dim_in = delta_im@.subrange(0, n as int);

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
                let ghost full_re_mag = vec_val(t1@.subrange(0, n as int));
                let ghost full_im_mag = vec_val(t2@.subrange(0, n as int));
                let ghost trunc_sq_re = ((full_re_mag * full_re_mag) / limb_power(frac_limbs as nat)) % limb_power(n as nat);
                let ghost trunc_sq_im = ((full_im_mag * full_im_mag) / limb_power(frac_limbs as nat)) % limb_power(n as nat);
                proof {
                    // From signed_mul_to (#70): t3, t4 hold the truncated squared magnitudes
                    assert(vec_val(t3@.subrange(0, n as int)) == trunc_sq_re);
                    assert(vec_val(t4@.subrange(0, n as int)) == trunc_sq_im);
                }
                let mag_carry = add_limbs_to(&t3, &t4, &mut t5, 0usize, n as usize);
                proof {
                    // PROVED: magnitude full equation.
                    // add_limbs_to (#68): t5 + carry*P == t3 + t4
                    // Combined with signed_mul_to (#70):
                    //   vec_val(t5) + carry*P == trunc_sq(|Z+δ|_re) + trunc_sq(|Z+δ|_im)
                    // where trunc_sq(x) = (x*x / BASE^frac) % BASE^n.
                    let P = limb_power(n as nat);
                    assert(vec_val(t5@.subrange(0, n as int)) + mag_carry.sem() * P
                        == vec_val(t3@.subrange(0, n as int)) + vec_val(t4@.subrange(0, n as int)));
                    assert(vec_val(t5@.subrange(0, n as int)) + mag_carry.sem() * P
                        == trunc_sq_re + trunc_sq_im);
                    // mag_carry is bounded
                    assert(mag_carry.sem() == 0 || mag_carry.sem() == 1);

                    // ── PROVED (#74): Connect magnitudes back to signed inputs ──
                    // signed_add_to (#71): the signed-magnitude result of t1 equals
                    // signed(Z_re) + signed(δ_re), possibly modulo P (overflow disjunct).
                    // Since (-x)² == x², the truncated square depends only on |t1|,
                    // which is vec_val(t1). So trunc_sq(vec_val(t1)) is a function of
                    // (signed(Z_re) + signed(δ_re)) modulo the overflow disjunction.
                    let signed_zre = signed_val_of::<u32>(zn_re_in, zn_re_s.sem() as int);
                    let signed_dre = signed_val_of::<u32>(dre_in, delta_re_sign.sem() as int);
                    let signed_zim = signed_val_of::<u32>(zn_im_in, zn_im_s.sem() as int);
                    let signed_dim = signed_val_of::<u32>(dim_in, delta_im_sign.sem() as int);
                    let signed_full_re = signed_val_of::<u32>(t1@.subrange(0, n as int), full_re_s.sem() as int);
                    let signed_full_im = signed_val_of::<u32>(t2@.subrange(0, n as int), full_im_s.sem() as int);

                    // signed_add_to's 3-way disjunction (#71), made explicit:
                    //   signed_full_re == signed_zre + signed_dre, OR
                    //   signed_full_re == signed_zre + signed_dre - P (overflow ≥ P), OR
                    //   signed_full_re == signed_zre + signed_dre + P (underflow ≤ -P)
                    assert(signed_full_re == signed_zre + signed_dre
                        || (signed_full_re == signed_zre + signed_dre - P && signed_zre + signed_dre >= P)
                        || (signed_full_re == signed_zre + signed_dre + P && signed_zre + signed_dre <= -(P as int)));
                    assert(signed_full_im == signed_zim + signed_dim
                        || (signed_full_im == signed_zim + signed_dim - P && signed_zim + signed_dim >= P)
                        || (signed_full_im == signed_zim + signed_dim + P && signed_zim + signed_dim <= -(P as int)));

                    // Square equality: |signed_full_re|² == vec_val(t1)² (since (-x)² = x²)
                    assert(signed_full_re * signed_full_re == full_re_mag * full_re_mag) by(nonlinear_arith)
                        requires
                            signed_full_re == full_re_mag || signed_full_re == -full_re_mag;
                    assert(signed_full_im * signed_full_im == full_im_mag * full_im_mag) by(nonlinear_arith)
                        requires
                            signed_full_im == full_im_mag || signed_full_im == -full_im_mag;

                    // So the truncated squares can equivalently be expressed in terms of
                    // signed_full_re and signed_full_im, which (via #71) are
                    // (signed_zre + signed_dre) and (signed_zim + signed_dim) up to ±P.
                    let ts_re_signed = (signed_full_re * signed_full_re / limb_power(frac_limbs as nat))
                        % limb_power(n as nat);
                    let ts_im_signed = (signed_full_im * signed_full_im / limb_power(frac_limbs as nat))
                        % limb_power(n as nat);
                    assert(ts_re_signed == trunc_sq_re);
                    assert(ts_im_signed == trunc_sq_im);
                    assert(vec_val(t5@.subrange(0, n as int)) + mag_carry.sem() * P
                        == ts_re_signed + ts_im_signed);
                }

                let thresh_off = 5u32;
                let ghost t5_val_pre_borrow = vec_val(t5@.subrange(0, n as int));
                let ghost thresh_seq = params@.subrange(thresh_off as int, params@.len() as int);
                let ghost thresh_val = vec_val(thresh_seq.subrange(0, n as int));
                let borrow = sub_limbs_to(&t5, vslice(params, thresh_off), &mut t1, 0usize, n as usize);
                proof {
                    // PROVED: escape check polarity.
                    // sub_limbs_to ensures: t1 + threshold == t5 + borrow * P
                    // borrow ∈ {0,1}; vec_val(t1) ∈ [0, P)
                    // Hence: borrow == 0  ⟺  vec_val(t5) ≥ vec_val(threshold)
                    let t1_val = vec_val(t1@.subrange(0, n as int));
                    let P = limb_power(n as nat);
                    let bv = borrow.sem();
                    // Establish the difference equation in our local variables
                    assert(t1_val + thresh_val == t5_val_pre_borrow + bv * P);
                    // Bounds
                    assert(valid_limbs(t1@.subrange(0, n as int))) by {
                        assert forall |k: int| 0 <= k < n as int
                            implies 0 <= (#[trigger] t1@.subrange(0, n as int)[k]).sem()
                                && t1@.subrange(0, n as int)[k].sem() < LIMB_BASE() by {
                            assert(t1@.subrange(0, n as int)[k] == t1@[k]);
                        }
                    }
                    lemma_vec_val_bounded::<u32>(t1@.subrange(0, n as int));
                    assert(0 <= t1_val && t1_val < P);
                    assert(bv == 0 || bv == 1);
                    // Polarity
                    if bv == 0 {
                        assert(t1_val + thresh_val == t5_val_pre_borrow);
                        assert(t5_val_pre_borrow >= thresh_val);
                    } else {
                        assert(bv == 1);
                        assert(t1_val + thresh_val == t5_val_pre_borrow + P);
                        assert(t5_val_pre_borrow == t1_val + thresh_val - P);
                        assert(t5_val_pre_borrow < thresh_val) by(nonlinear_arith)
                            requires t5_val_pre_borrow == t1_val + thresh_val - P,
                                     t1_val < P;
                    }
                    // Both directions captured:
                    assert((bv == 0) <==> (t5_val_pre_borrow >= thresh_val));
                }
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
        //
        // FIX for Bug #7 (vote buffer stale data):
        // Thread 0 zeroes ALL 256 vote slots before any thread writes its vote.
        // This ensures non-participating threads (those that returned early due
        // to gid_x >= width or gid_y >= height) don't leave stale/uninitialized
        // data in the vote buffer. Without this, boundary workgroups could read
        // garbage votes from non-existent pixels.
        if local_id == 0u32 {
            let mut vi = 0u32;
            while vi < 256u32
                invariant
                    wg_mem@.len() >= 8192,
                    vote_base + 256u32 < 8192u32,
                    vi <= 256u32,
                    forall |j: int| 0 <= j < vi as int
                        ==> (#[trigger] wg_mem@[(vote_base + j as u32) as int]) == 0u32,
                decreases 256 - vi,
            {
                vset(wg_mem, vote_base + vi, 0u32);
                vi = vi + 1u32;
            }
        }
        gpu_workgroup_barrier();

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
                    // (#3) g_count counts glitched votes in the prefix scanned so far.
                    g_count as nat == count_positive(wg_mem@, vote_base as int, i as int),
                    // (#5) best_vote is the maximum vote in the scanned prefix.
                    best_vote == max_prefix(wg_mem@, vote_base as int, i as int),
                    // When any vote was seen, best_idx points at a position in
                    // [0, i) whose vote equals best_vote. (When best_vote == 0,
                    // best_idx is still its initial 0.)
                    best_vote > 0u32 ==> (
                        best_idx < i
                        && wg_mem@[vote_base as int + best_idx as int] == best_vote
                    ),
                    best_vote == 0u32 ==> best_idx == 0u32,
            {
                let v = vget(wg_mem, vote_base + i);
                if v > best_vote {
                    best_vote = v;
                    best_idx = i;
                }
                if v > 0u32 {
                    g_count = g_count + 1u32;
                }
            }
            vset(wg_mem, glitch_count_addr, g_count);
            vset(wg_mem, best_ref_addr, best_idx);

            // Update ref_c to the best pixel's c value
            if g_count > 0u32 {
                // (#6) The u32 subtractions `gid_x - lid_x` and `gid_y - lid_y`
                // are safe: the kernel precondition guarantees gid_x >= lid_x
                // and gid_y >= lid_y (carried by the refinement loop
                // invariant). Also bound the result so (result + 16) fits in u32.
                proof {
                    assert(gid_x >= lid_x);
                    assert(gid_y >= lid_y);
                    assert(best_idx < 256u32);
                    assert(best_idx % 16u32 < 16u32) by(bit_vector)
                        requires best_idx < 256u32;
                    assert(best_idx / 16u32 < 16u32) by(bit_vector)
                        requires best_idx < 256u32;
                    // gid_x < width <= 0xFFFF and lid_x < 16, so
                    // gid_x - lid_x + 15 < 0x10000 < u32_max.
                    assert((gid_x - lid_x) as int + 16 < u32_max());
                    assert((gid_y - lid_y) as int + 16 < u32_max());
                }
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

    // (#1) Post-loop termination state.
    // The refinement loop either exited normally (round == max_rounds) or
    // via `break` when all glitches were resolved (glitch_count == 0).
    // In both cases, the invariant-carried state holds:
    //   escaped_iter <= max_iters
    //   is_glitched ∈ {0, 1}
    //   glitch_iter < max_iters
    // These three facts cover every pixel output state: "escaped at iter k",
    // "inside the set (ran full max_iters)", or "glitched at iter k".
    proof {
        assert(escaped_iter <= max_iters);
        assert(is_glitched == 0u32 || is_glitched == 1u32);
        assert(glitch_iter < max_iters);
    }

    // ── Fallback: direct computation for unresolved glitched pixels ──
    // When ALL pixels in a workgroup glitch early, the refinement loop can't
    // find a good local reference. These pixels keep is_glitched==1 and
    // escaped_iter==max_iters after all rounds, rendering as solid pink tiles.
    // Fix: fall back to direct (non-perturbation) iteration Z_{k+1} = Z_k^2 + c.
    // This is slower but always correct — same approach as Kalles Fraktaler et al.
    if is_glitched == 1u32 && escaped_iter == max_iters {
        let cre_s_fb = vget(c_data, c_re_sign_off);
        let cim_s_fb = vget(c_data, c_im_sign_off);
        if cre_s_fb <= 1u32 && cim_s_fb <= 1u32 {
            // Zero Z_0
            for zi in 0u32..n
                invariant
                    n >= 1, n <= 8,
                    delta_re@.len() == n as int,
                    delta_im@.len() == n as int,
                    forall |j: int| 0 <= j < zi as int ==> delta_re@[j] == 0u32,
                    forall |j: int| 0 <= j < zi as int ==> delta_im@[j] == 0u32,
            {
                delta_re.set(zi as usize, 0u32);
                delta_im.set(zi as usize, 0u32);
            }
            // Prove valid_limbs for c_data slices
            proof {
                let cre_sub = c_data@.subrange(c_re_off as int, c_data@.len() as int);
                let cim_sub = c_data@.subrange(c_im_off as int, c_data@.len() as int);
                assert(valid_limbs(cre_sub.subrange(0, n as int))) by {
                    assert forall |j: int| 0 <= j < n as int
                        implies 0 <= (#[trigger] cre_sub.subrange(0, n as int)[j]).sem()
                            && cre_sub.subrange(0, n as int)[j].sem() < LIMB_BASE() by {
                        // u32 values are always in [0, 2^32) = [0, LIMB_BASE)
                        assert(cre_sub.subrange(0, n as int)[j] == c_data@[(c_re_off as int + j) as int]);
                    }
                }
                assert(valid_limbs(cim_sub.subrange(0, n as int))) by {
                    assert forall |j: int| 0 <= j < n as int
                        implies 0 <= (#[trigger] cim_sub.subrange(0, n as int)[j]).sem()
                            && cim_sub.subrange(0, n as int)[j].sem() < LIMB_BASE() by {
                        assert(cim_sub.subrange(0, n as int)[j] == c_data@[(c_im_off as int + j) as int]);
                    }
                }
                // Threshold valid_limbs
                let thresh_sub = params@.subrange(5, params@.len() as int);
                assert(valid_limbs(thresh_sub.subrange(0, n as int))) by {
                    assert forall |j: int| 0 <= j < n as int
                        implies 0 <= (#[trigger] thresh_sub.subrange(0, n as int)[j]).sem()
                            && thresh_sub.subrange(0, n as int)[j].sem() < LIMB_BASE() by {
                        assert(thresh_sub.subrange(0, n as int)[j] == params@[(5 + j) as int]);
                    }
                }
            }
            escaped_iter = direct_computation_fallback(
                vslice(c_data, c_re_off), cre_s_fb,
                vslice(c_data, c_im_off), cim_s_fb,
                &mut delta_re, &mut delta_im,
                &mut t1, &mut t2, &mut t3, &mut t4, &mut t5,
                &mut lprod, &mut ls1, &mut ls2,
                vslice(params, 5u32),
                n, frac_limbs, max_iters,
            );
        }
    }

    // ── Colorize ──
    // PROVED: output pixel correspondence.
    // tid = gid_y * width + gid_x: standard row-major linearization.
    // This is injective: different (gid_x, gid_y) → different tid.
    // So iter_counts[tid] stores the result for exactly pixel (gid_x, gid_y).
    proof {
        assert(tid == gid_y * width + gid_x);
        assert((tid as int) < (width as int) * (height as int));
        // Formal injectivity: if any other (gy', gx') would produce the same
        // tid with 0 <= gx' < width and 0 <= gy', they must equal (gid_y, gid_x).
        assert forall |gy2: int, gx2: int|
            0 <= gx2 && gx2 < width as int && 0 <= gy2
                && #[trigger] (gy2 * width as int + gx2) == tid as int
            implies gx2 == gid_x as int && gy2 == gid_y as int
        by {
            lemma_tid_injective(gid_y as int, gid_x as int, gy2, gx2, width as int);
        }
    }
    // (#2) iter_counts output bounds regression test
    proof { assert(tid < iter_counts@.len()); }
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
        // (#3) RGBA bit-field non-overlap regression test
        proof {
            lemma_colorize_channels_bounded(escaped_iter as int, max_iters as int);
            assert(r <= 255u32);
            assert(g <= 127u32);
            assert(b <= 255u32);
            assert((g << 8u32) & 0xFFu32 == 0u32) by(bit_vector) requires g <= 127u32;
            assert((b << 16u32) & 0xFFFFu32 == 0u32) by(bit_vector) requires b <= 255u32;
        }
        vset(iter_counts, tid, alpha | (b << 16u32) | (g << 8u32) | r);
    }
}

} // verus!
