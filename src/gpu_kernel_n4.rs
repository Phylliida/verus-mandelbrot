///  GPU kernel entry point for N=4 limbs (128-bit prime field).
///  p = 2^128 - c where c is a small constant.
///
///  This file is designed for transpilation to WGSL via verus-gpu-parser.
///  Each multi-limb value is stored as 4 consecutive u32 entries in a buffer.
///  Buffer layout: value[i] at offset (pixel_id * 4 + limb).

///  4-limb addition with carry chain. Returns (r0,r1,r2,r3,carry).
fn add4(a0: u32, a1: u32, a2: u32, a3: u32,
        b0: u32, b1: u32, b2: u32, b3: u32) -> (u32, u32, u32, u32, u32)
{
    //  LSB-first carry chain (limb 0 is least significant)
    let sum0 = a0.wrapping_add(b0);
    let c0 = if sum0 < a0 { 1u32 } else { 0u32 };

    let sum1_tmp = a1.wrapping_add(b1);
    let c1a = if sum1_tmp < a1 { 1u32 } else { 0u32 };
    let sum1 = sum1_tmp.wrapping_add(c0);
    let c1b = if sum1 < sum1_tmp { 1u32 } else { 0u32 };
    let c1 = c1a + c1b;

    let sum2_tmp = a2.wrapping_add(b2);
    let c2a = if sum2_tmp < a2 { 1u32 } else { 0u32 };
    let sum2 = sum2_tmp.wrapping_add(c1);
    let c2b = if sum2 < sum2_tmp { 1u32 } else { 0u32 };
    let c2 = c2a + c2b;

    let sum3_tmp = a3.wrapping_add(b3);
    let c3a = if sum3_tmp < a3 { 1u32 } else { 0u32 };
    let sum3 = sum3_tmp.wrapping_add(c2);
    let c3b = if sum3 < sum3_tmp { 1u32 } else { 0u32 };
    let carry = c3a + c3b;

    (sum0, sum1, sum2, sum3, carry)
}

///  4-limb subtraction with borrow chain. Returns (r0,r1,r2,r3,borrow).
fn sub4(a0: u32, a1: u32, a2: u32, a3: u32,
        b0: u32, b1: u32, b2: u32, b3: u32) -> (u32, u32, u32, u32, u32)
{
    let diff0 = a0.wrapping_sub(b0);
    let bw0 = if a0 < b0 { 1u32 } else { 0u32 };

    let diff1_tmp = a1.wrapping_sub(b1);
    let bw1a = if a1 < b1 { 1u32 } else { 0u32 };
    let diff1 = diff1_tmp.wrapping_sub(bw0);
    let bw1b = if diff1_tmp < bw0 { 1u32 } else { 0u32 };
    let bw1 = bw1a + bw1b;

    let diff2_tmp = a2.wrapping_sub(b2);
    let bw2a = if a2 < b2 { 1u32 } else { 0u32 };
    let diff2 = diff2_tmp.wrapping_sub(bw1);
    let bw2b = if diff2_tmp < bw1 { 1u32 } else { 0u32 };
    let bw2 = bw2a + bw2b;

    let diff3_tmp = a3.wrapping_sub(b3);
    let bw3a = if a3 < b3 { 1u32 } else { 0u32 };
    let diff3 = diff3_tmp.wrapping_sub(bw2);
    let bw3b = if diff3_tmp < bw2 { 1u32 } else { 0u32 };
    let borrow = bw3a + bw3b;

    (diff0, diff1, diff2, diff3, borrow)
}

///  Conditional select: if cond == 0, return a; else return b.
fn select4(cond: u32, a0: u32, a1: u32, a2: u32, a3: u32,
                      b0: u32, b1: u32, b2: u32, b3: u32) -> (u32, u32, u32, u32)
{
    if cond == 0u32 {
        (a0, a1, a2, a3)
    } else {
        (b0, b1, b2, b3)
    }
}

///  Modular addition: (a + b) mod p where p = 2^128 - C.
///  Uses carry fold: sum + carry*lp ≡ sum + carry*C (mod p).
///  Then conditional subtract p.
fn add_mod4(a0: u32, a1: u32, a2: u32, a3: u32,
            b0: u32, b1: u32, b2: u32, b3: u32,
            p0: u32, p1: u32, p2: u32, p3: u32,
            c_val: u32) -> (u32, u32, u32, u32)
{
    let (s0, s1, s2, s3, carry) = add4(a0, a1, a2, a3, b0, b1, b2, b3);
    //  Fold carry: carry * c_val (carry is 0 or 1)
    let carry_c = carry * c_val;
    let (f0, f1, f2, f3, _fc) = add4(s0, s1, s2, s3, carry_c, 0u32, 0u32, 0u32);
    //  Conditional subtract p
    let (d0, d1, d2, d3, borrow) = sub4(f0, f1, f2, f3, p0, p1, p2, p3);
    select4(borrow, d0, d1, d2, d3, f0, f1, f2, f3)
}

///  Modular negation: (p - a) mod p. Returns 0 if a == 0.
fn neg_mod4(a0: u32, a1: u32, a2: u32, a3: u32,
            p0: u32, p1: u32, p2: u32, p3: u32) -> (u32, u32, u32, u32)
{
    let (r0, r1, r2, r3, _bw) = sub4(p0, p1, p2, p3, a0, a1, a2, a3);
    //  If result == p (i.e., a was 0), subtract p again
    let (d0, d1, d2, d3, bw2) = sub4(r0, r1, r2, r3, p0, p1, p2, p3);
    select4(bw2, d0, d1, d2, d3, r0, r1, r2, r3)
}

///  Modular subtraction: (a - b) mod p = a + neg(b).
fn sub_mod4(a0: u32, a1: u32, a2: u32, a3: u32,
            b0: u32, b1: u32, b2: u32, b3: u32,
            p0: u32, p1: u32, p2: u32, p3: u32,
            c_val: u32) -> (u32, u32, u32, u32)
{
    let (nb0, nb1, nb2, nb3) = neg_mod4(b0, b1, b2, b3, p0, p1, p2, p3);
    add_mod4(a0, a1, a2, a3, nb0, nb1, nb2, nb3, p0, p1, p2, p3, c_val)
}

///  Multiply two limbs: a * b = (lo, hi).
fn mul_limb(a: u32, b: u32) -> (u32, u32)
{
    //  Split into 16-bit halves for GPU-friendly multiplication
    let a_lo = a & 0xFFFFu32;
    let a_hi = a >> 16u32;
    let b_lo = b & 0xFFFFu32;
    let b_hi = b >> 16u32;

    let p0 = a_lo * b_lo;
    let p1 = a_lo * b_hi;
    let p2 = a_hi * b_lo;
    let p3 = a_hi * b_hi;

    let mid = p1 + p2;
    let mid_carry = if mid < p1 { 1u32 } else { 0u32 };

    let lo = p0.wrapping_add(mid << 16u32);
    let lo_carry = if lo < p0 { 1u32 } else { 0u32 };
    let hi = p3 + (mid >> 16u32) + (mid_carry << 16u32) + lo_carry;

    (lo, hi)
}

///  Schoolbook 4x4 multiply → 8-limb product.
///  Returns (r0..r7) where r0 is LSB.
fn mul4x4(a0: u32, a1: u32, a2: u32, a3: u32,
          b0: u32, b1: u32, b2: u32, b3: u32) -> (u32, u32, u32, u32, u32, u32, u32, u32)
{
    //  Column-by-column schoolbook multiply with 3-word accumulator
    //  For clarity, compute each column's partial products and accumulate

    //  Column 0: a0*b0
    let (c0_lo, c0_hi) = mul_limb(a0, b0);
    let r0 = c0_lo;

    //  Column 1: a0*b1 + a1*b0 + carry
    let (p10_lo, p10_hi) = mul_limb(a0, b1);
    let (p11_lo, p11_hi) = mul_limb(a1, b0);
    let acc1 = c0_hi as u64 + p10_lo as u64 + p11_lo as u64;
    let r1 = acc1 as u32;
    let carry1 = (acc1 >> 32u64) as u32 + p10_hi + p11_hi;

    //  Column 2: a0*b2 + a1*b1 + a2*b0 + carry
    let (p20_lo, p20_hi) = mul_limb(a0, b2);
    let (p21_lo, p21_hi) = mul_limb(a1, b1);
    let (p22_lo, p22_hi) = mul_limb(a2, b0);
    let acc2 = carry1 as u64 + p20_lo as u64 + p21_lo as u64 + p22_lo as u64;
    let r2 = acc2 as u32;
    let carry2 = (acc2 >> 32u64) as u32 + p20_hi + p21_hi + p22_hi;

    //  Column 3: a0*b3 + a1*b2 + a2*b1 + a3*b0 + carry
    let (p30_lo, p30_hi) = mul_limb(a0, b3);
    let (p31_lo, p31_hi) = mul_limb(a1, b2);
    let (p32_lo, p32_hi) = mul_limb(a2, b1);
    let (p33_lo, p33_hi) = mul_limb(a3, b0);
    let acc3 = carry2 as u64 + p30_lo as u64 + p31_lo as u64 + p32_lo as u64 + p33_lo as u64;
    let r3 = acc3 as u32;
    let carry3 = (acc3 >> 32u64) as u32 + p30_hi + p31_hi + p32_hi + p33_hi;

    //  Column 4: a1*b3 + a2*b2 + a3*b1 + carry
    let (p40_lo, p40_hi) = mul_limb(a1, b3);
    let (p41_lo, p41_hi) = mul_limb(a2, b2);
    let (p42_lo, p42_hi) = mul_limb(a3, b1);
    let acc4 = carry3 as u64 + p40_lo as u64 + p41_lo as u64 + p42_lo as u64;
    let r4 = acc4 as u32;
    let carry4 = (acc4 >> 32u64) as u32 + p40_hi + p41_hi + p42_hi;

    //  Column 5: a2*b3 + a3*b2 + carry
    let (p50_lo, p50_hi) = mul_limb(a2, b3);
    let (p51_lo, p51_hi) = mul_limb(a3, b2);
    let acc5 = carry4 as u64 + p50_lo as u64 + p51_lo as u64;
    let r5 = acc5 as u32;
    let carry5 = (acc5 >> 32u64) as u32 + p50_hi + p51_hi;

    //  Column 6: a3*b3 + carry
    let (p60_lo, p60_hi) = mul_limb(a3, b3);
    let acc6 = carry5 as u64 + p60_lo as u64;
    let r6 = acc6 as u32;
    let r7 = (acc6 >> 32u64) as u32 + p60_hi;

    (r0, r1, r2, r3, r4, r5, r6, r7)
}

///  Mersenne reduction of 8-limb product to 4-limb result mod p = 2^128 - c.
///  Uses: hi * 2^128 ≡ hi * c (mod p).
fn reduce4(r0: u32, r1: u32, r2: u32, r3: u32,
           r4: u32, r5: u32, r6: u32, r7: u32,
           p0: u32, p1: u32, p2: u32, p3: u32,
           c_val: u32) -> (u32, u32, u32, u32)
{
    //  hi = (r4, r5, r6, r7), lo = (r0, r1, r2, r3)
    //  hi * c: multiply 4-limb hi by scalar c
    let (h0_lo, h0_hi) = mul_limb(r4, c_val);
    let (h1_lo, h1_hi) = mul_limb(r5, c_val);
    let (h2_lo, h2_hi) = mul_limb(r6, c_val);
    let (h3_lo, h3_hi) = mul_limb(r7, c_val);

    //  Accumulate hi*c as a 5-limb value
    let hc0 = h0_lo;
    let acc1 = h0_hi as u64 + h1_lo as u64;
    let hc1 = acc1 as u32;
    let c1 = (acc1 >> 32u64) as u32;
    let acc2 = c1 as u64 + h1_hi as u64 + h2_lo as u64;
    let hc2 = acc2 as u32;
    let c2 = (acc2 >> 32u64) as u32;
    let acc3 = c2 as u64 + h2_hi as u64 + h3_lo as u64;
    let hc3 = acc3 as u32;
    let hc4 = (acc3 >> 32u64) as u32 + h3_hi;

    //  lo + hi*c
    let (s0, s1, s2, s3, carry) = add4(r0, r1, r2, r3, hc0, hc1, hc2, hc3);

    //  Fold remaining: (carry + hc4) * c + s
    let extra = (carry + hc4) * c_val;
    let (f0, f1, f2, f3, _fc) = add4(s0, s1, s2, s3, extra, 0u32, 0u32, 0u32);

    //  Conditional subtract p (up to twice since f could be up to ~2p)
    let (d0, d1, d2, d3, bw1) = sub4(f0, f1, f2, f3, p0, p1, p2, p3);
    let (e0, e1, e2, e3) = select4(bw1, d0, d1, d2, d3, f0, f1, f2, f3);
    let (d20, d21, d22, d23, bw2) = sub4(e0, e1, e2, e3, p0, p1, p2, p3);
    select4(bw2, d20, d21, d22, d23, e0, e1, e2, e3)
}

///  Modular multiplication: (a * b) mod p.
fn mul_mod4(a0: u32, a1: u32, a2: u32, a3: u32,
            b0: u32, b1: u32, b2: u32, b3: u32,
            p0: u32, p1: u32, p2: u32, p3: u32,
            c_val: u32) -> (u32, u32, u32, u32)
{
    let (r0, r1, r2, r3, r4, r5, r6, r7) = mul4x4(a0, a1, a2, a3, b0, b1, b2, b3);
    reduce4(r0, r1, r2, r3, r4, r5, r6, r7, p0, p1, p2, p3, c_val)
}

///  Complex squaring over prime field: z^2 = (re^2 - im^2, 2*re*im).
///  Uses 3 muls: re^2, im^2, (re+im)^2.
fn complex_square4(
    re0: u32, re1: u32, re2: u32, re3: u32,
    im0: u32, im1: u32, im2: u32, im3: u32,
    p0: u32, p1: u32, p2: u32, p3: u32,
    c_val: u32,
) -> (u32, u32, u32, u32, u32, u32, u32, u32)
{
    let (re2_0, re2_1, re2_2, re2_3) = mul_mod4(re0, re1, re2, re3, re0, re1, re2, re3, p0, p1, p2, p3, c_val);
    let (im2_0, im2_1, im2_2, im2_3) = mul_mod4(im0, im1, im2, im3, im0, im1, im2, im3, p0, p1, p2, p3, c_val);
    //  new_re = re^2 - im^2
    let (nr0, nr1, nr2, nr3) = sub_mod4(re2_0, re2_1, re2_2, re2_3, im2_0, im2_1, im2_2, im2_3, p0, p1, p2, p3, c_val);
    //  new_im = (re+im)^2 - re^2 - im^2
    let (s0, s1, s2, s3) = add_mod4(re0, re1, re2, re3, im0, im1, im2, im3, p0, p1, p2, p3, c_val);
    let (s2_0, s2_1, s2_2, s2_3) = mul_mod4(s0, s1, s2, s3, s0, s1, s2, s3, p0, p1, p2, p3, c_val);
    let (t0, t1, t2, t3) = sub_mod4(s2_0, s2_1, s2_2, s2_3, re2_0, re2_1, re2_2, re2_3, p0, p1, p2, p3, c_val);
    let (ni0, ni1, ni2, ni3) = sub_mod4(t0, t1, t2, t3, im2_0, im2_1, im2_2, im2_3, p0, p1, p2, p3, c_val);
    (nr0, nr1, nr2, nr3, ni0, ni1, ni2, ni3)
}

///  Reference orbit step: Z' = Z^2 + c.
fn ref_step4(
    zr0: u32, zr1: u32, zr2: u32, zr3: u32,
    zi0: u32, zi1: u32, zi2: u32, zi3: u32,
    cr0: u32, cr1: u32, cr2: u32, cr3: u32,
    ci0: u32, ci1: u32, ci2: u32, ci3: u32,
    p0: u32, p1: u32, p2: u32, p3: u32,
    c_val: u32,
) -> (u32, u32, u32, u32, u32, u32, u32, u32)
{
    let (sq_r0, sq_r1, sq_r2, sq_r3, sq_i0, sq_i1, sq_i2, sq_i3) =
        complex_square4(zr0, zr1, zr2, zr3, zi0, zi1, zi2, zi3, p0, p1, p2, p3, c_val);
    let (nr0, nr1, nr2, nr3) = add_mod4(sq_r0, sq_r1, sq_r2, sq_r3, cr0, cr1, cr2, cr3, p0, p1, p2, p3, c_val);
    let (ni0, ni1, ni2, ni3) = add_mod4(sq_i0, sq_i1, sq_i2, sq_i3, ci0, ci1, ci2, ci3, p0, p1, p2, p3, c_val);
    (nr0, nr1, nr2, nr3, ni0, ni1, ni2, ni3)
}

///  Perturbation step: δ' = 2*Z*δ + δ^2 + Δc.
fn perturb_step4(
    //  Z_ref (reference orbit value at this iteration)
    zr0: u32, zr1: u32, zr2: u32, zr3: u32,
    zi0: u32, zi1: u32, zi2: u32, zi3: u32,
    //  δ (current perturbation)
    dr0: u32, dr1: u32, dr2: u32, dr3: u32,
    di0: u32, di1: u32, di2: u32, di3: u32,
    //  Δc (per-pixel offset from reference)
    dcr0: u32, dcr1: u32, dcr2: u32, dcr3: u32,
    dci0: u32, dci1: u32, dci2: u32, dci3: u32,
    //  Prime field parameters
    p0: u32, p1: u32, p2: u32, p3: u32,
    c_val: u32,
) -> (u32, u32, u32, u32, u32, u32, u32, u32)
{
    //  2*Z
    let (tz_r0, tz_r1, tz_r2, tz_r3) = add_mod4(zr0, zr1, zr2, zr3, zr0, zr1, zr2, zr3, p0, p1, p2, p3, c_val);
    let (tz_i0, tz_i1, tz_i2, tz_i3) = add_mod4(zi0, zi1, zi2, zi3, zi0, zi1, zi2, zi3, p0, p1, p2, p3, c_val);

    //  2*Z*δ (complex multiply)
    let k1_0 = mul_mod4(tz_r0, tz_r1, tz_r2, tz_r3, dr0, dr1, dr2, dr3, p0, p1, p2, p3, c_val);
    let k2_0 = mul_mod4(tz_i0, tz_i1, tz_i2, tz_i3, di0, di1, di2, di3, p0, p1, p2, p3, c_val);
    let tzd_re = sub_mod4(k1_0.0, k1_0.1, k1_0.2, k1_0.3, k2_0.0, k2_0.1, k2_0.2, k2_0.3, p0, p1, p2, p3, c_val);

    let k3_0 = mul_mod4(tz_r0, tz_r1, tz_r2, tz_r3, di0, di1, di2, di3, p0, p1, p2, p3, c_val);
    let k4_0 = mul_mod4(tz_i0, tz_i1, tz_i2, tz_i3, dr0, dr1, dr2, dr3, p0, p1, p2, p3, c_val);
    let tzd_im = add_mod4(k3_0.0, k3_0.1, k3_0.2, k3_0.3, k4_0.0, k4_0.1, k4_0.2, k4_0.3, p0, p1, p2, p3, c_val);

    //  δ^2
    let (dsq_r0, dsq_r1, dsq_r2, dsq_r3, dsq_i0, dsq_i1, dsq_i2, dsq_i3) =
        complex_square4(dr0, dr1, dr2, dr3, di0, di1, di2, di3, p0, p1, p2, p3, c_val);

    //  2*Z*δ + δ^2
    let (s_r0, s_r1, s_r2, s_r3) = add_mod4(tzd_re.0, tzd_re.1, tzd_re.2, tzd_re.3, dsq_r0, dsq_r1, dsq_r2, dsq_r3, p0, p1, p2, p3, c_val);
    let (s_i0, s_i1, s_i2, s_i3) = add_mod4(tzd_im.0, tzd_im.1, tzd_im.2, tzd_im.3, dsq_i0, dsq_i1, dsq_i2, dsq_i3, p0, p1, p2, p3, c_val);

    //  + Δc
    let (out_r0, out_r1, out_r2, out_r3) = add_mod4(s_r0, s_r1, s_r2, s_r3, dcr0, dcr1, dcr2, dcr3, p0, p1, p2, p3, c_val);
    let (out_i0, out_i1, out_i2, out_i3) = add_mod4(s_i0, s_i1, s_i2, s_i3, dci0, dci1, dci2, dci3, p0, p1, p2, p3, c_val);

    (out_r0, out_r1, out_r2, out_r3, out_i0, out_i1, out_i2, out_i3)
}

///  GPU kernel: compute reference orbit for one point.
///  Buffer layout (all u32):
///    c_data[0..4]:  c_re limbs,  c_data[4..8]:  c_im limbs
///    orbit_re[iter*4 .. iter*4+4]: Z_re at iteration iter
///    orbit_im[iter*4 .. iter*4+4]: Z_im at iteration iter
///    params[0]: max_iters, params[1]: c_val (Mersenne constant)
///    params[2..6]: p limbs (the prime)
///    iter_counts[tid]: output iteration count (escape iter or max_iters)
#[gpu_kernel(workgroup_size(16, 16, 1))]
fn mandelbrot_ref_orbit(
    #[gpu_builtin(thread_id_x)] gid_x: u32,
    #[gpu_builtin(thread_id_y)] gid_y: u32,
    #[gpu_buffer(0, read)] c_data: &[u32],
    #[gpu_buffer(1, read_write)] orbit_re: &mut [u32],
    #[gpu_buffer(2, read_write)] orbit_im: &mut [u32],
    #[gpu_buffer(3, read)] params: &[u32],
    #[gpu_buffer(4, read_write)] iter_counts: &mut [u32],
) {
    let width = params[0u32];
    let max_iters = params[1u32];
    let c_val = params[2u32];
    let p0 = params[3u32];
    let p1 = params[4u32];
    let p2 = params[5u32];
    let p3 = params[6u32];

    let tid = gid_y * width + gid_x;

    //  Load c for this pixel (tid indexes into c_data)
    let base = tid * 8u32;
    let cr0 = c_data[base + 0u32];
    let cr1 = c_data[base + 1u32];
    let cr2 = c_data[base + 2u32];
    let cr3 = c_data[base + 3u32];
    let ci0 = c_data[base + 4u32];
    let ci1 = c_data[base + 5u32];
    let ci2 = c_data[base + 6u32];
    let ci3 = c_data[base + 7u32];

    //  Z_0 = 0
    let mut zr0 = 0u32;
    let mut zr1 = 0u32;
    let mut zr2 = 0u32;
    let mut zr3 = 0u32;
    let mut zi0 = 0u32;
    let mut zi1 = 0u32;
    let mut zi2 = 0u32;
    let mut zi3 = 0u32;

    let mut escaped_iter = max_iters;

    for iter in 0u32..max_iters {
        //  Store Z_n in orbit buffers
        let orbit_base = (tid * max_iters + iter) * 4u32;
        orbit_re[orbit_base + 0u32] = zr0;
        orbit_re[orbit_base + 1u32] = zr1;
        orbit_re[orbit_base + 2u32] = zr2;
        orbit_re[orbit_base + 3u32] = zr3;
        orbit_im[orbit_base + 0u32] = zi0;
        orbit_im[orbit_base + 1u32] = zi1;
        orbit_im[orbit_base + 2u32] = zi2;
        orbit_im[orbit_base + 3u32] = zi3;

        //  Z_{n+1} = Z_n^2 + c
        let (nr0, nr1, nr2, nr3, ni0, ni1, ni2, ni3) =
            ref_step4(zr0, zr1, zr2, zr3, zi0, zi1, zi2, zi3,
                      cr0, cr1, cr2, cr3, ci0, ci1, ci2, ci3,
                      p0, p1, p2, p3, c_val);
        zr0 = nr0; zr1 = nr1; zr2 = nr2; zr3 = nr3;
        zi0 = ni0; zi1 = ni1; zi2 = ni2; zi3 = ni3;

        //  Escape check: |Z|^2 > 4 (simplified: check if top limb > 4)
        //  For proper escape detection, we'd use magnitude_squared + centered comparison.
        //  For now: if zr3 > 4 || zi3 > 4, likely escaped (rough check on MSB limb).
        let (mag_0, mag_1, mag_2, mag_3) = add_mod4(
            mul_mod4(zr0, zr1, zr2, zr3, zr0, zr1, zr2, zr3, p0, p1, p2, p3, c_val).0,
            mul_mod4(zr0, zr1, zr2, zr3, zr0, zr1, zr2, zr3, p0, p1, p2, p3, c_val).1,
            mul_mod4(zr0, zr1, zr2, zr3, zr0, zr1, zr2, zr3, p0, p1, p2, p3, c_val).2,
            mul_mod4(zr0, zr1, zr2, zr3, zr0, zr1, zr2, zr3, p0, p1, p2, p3, c_val).3,
            mul_mod4(zi0, zi1, zi2, zi3, zi0, zi1, zi2, zi3, p0, p1, p2, p3, c_val).0,
            mul_mod4(zi0, zi1, zi2, zi3, zi0, zi1, zi2, zi3, p0, p1, p2, p3, c_val).1,
            mul_mod4(zi0, zi1, zi2, zi3, zi0, zi1, zi2, zi3, p0, p1, p2, p3, c_val).2,
            mul_mod4(zi0, zi1, zi2, zi3, zi0, zi1, zi2, zi3, p0, p1, p2, p3, c_val).3,
            p0, p1, p2, p3, c_val);
        //  TODO: proper escape detection via centered comparison
    }

    iter_counts[tid] = escaped_iter;
}
