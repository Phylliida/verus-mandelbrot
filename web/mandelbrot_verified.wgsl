struct R2 {
  _0: u32,
  _1: u32,
}

@group(0) @binding(0) var<storage, read> c_data: array<u32>;
@group(0) @binding(1) var<storage, read_write> scratch: array<u32>;
@group(0) @binding(2) var<storage, read_write> iter_counts: array<u32>;
@group(0) @binding(3) var<storage, read> params: array<u32>;

fn fp_mul_scratch_scratch(a_limbs: u32, a_sign: u32, b_limbs: u32, b_sign: u32, n: u32, frac_limbs: u32) -> R2 {
  var product: u32;
  var _gc: u32;
  var truncated: u32;
  var sign_b_flip: u32;
  var result_sign: u32;
  var __ret: R2;
  {
    var __td = generic_mul_karatsuba_d6(a_limbs, b_limbs, n);
    product = __td._0;
    _gc = __td._1;
  }
  truncated = generic_slice_vec(product, frac_limbs, (frac_limbs + n));
  sign_b_flip = select_limb(b_sign, 1u, 0u);
  result_sign = select_limb(a_sign, b_sign, sign_b_flip);
  __ret = R2(truncated, result_sign);
  return __ret;
}

fn fp_signed_add_c_data(a_limbs: u32, a_sign: u32, b_limbs: u32, b_sign: u32, n: u32) -> R2 {
  var sum: u32;
  var _carry: u32;
  var a_minus_b: u32;
  var borrow_ab: u32;
  var b_minus_a: u32;
  var _borrow_ba: u32;
  var sign_diff: u32;
  var sign_borrow: u32;
  var diff_zero: u32;
  var borrow_zero: u32;
  var same_sign: u32;
  var _: u32;
  var diff_result: u32;
  var diff_sign: u32;
  var result_limbs: u32;
  var result_sign: u32;
  var __ret: R2;
  {
    var __td = generic_add_limbs(a_limbs, b_limbs, n);
    sum = __td._0;
    _carry = __td._1;
  }
  {
    var __td = generic_sub_limbs_params(a_limbs, b_limbs, n);
    a_minus_b = __td._0;
    borrow_ab = __td._1;
  }
  {
    var __td = generic_sub_limbs_params(b_limbs, a_limbs, n);
    b_minus_a = __td._0;
    _borrow_ba = __td._1;
  }
  {
    var __td = sub_borrow(a_sign, b_sign, 0u);
    sign_diff = __td._0;
    sign_borrow = __td._1;
  }
  diff_zero = is_zero_limb(sign_diff);
  borrow_zero = is_zero_limb(sign_borrow);
  {
    var __td = mul2(diff_zero, borrow_zero);
    same_sign = __td._0;
    _ = __td._1;
  }
  diff_result = generic_select_vec(borrow_ab, a_minus_b, b_minus_a, n);
  diff_sign = select_limb(borrow_ab, a_sign, b_sign);
  result_limbs = generic_select_vec(same_sign, sum, diff_result, n);
  result_sign = select_limb(same_sign, a_sign, diff_sign);
  __ret = R2(result_limbs, result_sign);
  return __ret;
}

fn fp_mag_squared(re_limbs: u32, re_sign: u32, im_limbs: u32, im_sign: u32, n: u32, frac_limbs: u32) -> R2 {
  var re2: u32;
  var _re2_sign: u32;
  var im2: u32;
  var _im2_sign: u32;
  var mag: u32;
  var _carry: u32;
  var __ret: R2;
  {
    var __td = fp_mul_scratch_scratch(re_limbs, re_sign, re_limbs, re_sign, n, frac_limbs);
    re2 = __td._0;
    _re2_sign = __td._1;
  }
  {
    var __td = fp_mul_scratch_scratch(im_limbs, im_sign, im_limbs, im_sign, n, frac_limbs);
    im2 = __td._0;
    _im2_sign = __td._1;
  }
  {
    var __td = generic_add_limbs(re2, im2, n);
    mag = __td._0;
    _carry = __td._1;
  }
  __ret = R2(mag, 0u);
  return __ret;
}

fn generic_sub_limbs_params(a: u32, b: u32, n: u32) -> R2 {
  var out_len: u32;
  var borrow: u32;
  var i: u32;
  var digit: u32;
  var next_borrow: u32;
  var __ret: R2;
  out_len = 0u;
  borrow = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var __td = sub_borrow(params[(a + i)], scratch[(b + i)], borrow);
      digit = __td._0;
      next_borrow = __td._1;
    }
    scratch[(out + out_len)] = digit;
    out_len = out_len + 1u;
    borrow = next_borrow;
  }
  __ret = R2(out, borrow);
  return __ret;
}

fn fp_signed_sub(a_limbs: u32, a_sign: u32, b_limbs: u32, b_sign: u32, n: u32) -> R2 {
  var neg_b_sign: u32;
  var __ret: R2;
  neg_b_sign = select_limb(b_sign, 1u, 0u);
  __ret = fp_signed_add_c_data(a_limbs, a_sign, b_limbs, neg_b_sign, n);
  return __ret;
}

fn select_limb(cond: u32, if_zero: u32, if_nonzero: u32) -> u32 {
  var __ret: u32;
  if ((cond == 0u)) {
    __ret = if_zero;
  } else {
    __ret = if_nonzero;
  }
  return __ret;
}

fn generic_mul_karatsuba_d0(a: u32, b: u32, n: u32) -> R2 {
  var half: u32;
  var upper: u32;
  var a_lo: u32;
  var a_hi: u32;
  var b_lo: u32;
  var b_hi: u32;
  var a_lo_p: u32;
  var b_lo_p: u32;
  var z0: u32;
  var gz0: u32;
  var z2: u32;
  var gz2: u32;
  var a_sum_body: u32;
  var a_carry: u32;
  var b_sum_body: u32;
  var b_carry: u32;
  var a_sum: u32;
  var b_sum: u32;
  var z1_full: u32;
  var gz1f: u32;
  var tgt: u32;
  var z0_p: u32;
  var z2_p: u32;
  var z1_tmp: u32;
  var bw1: u32;
  var z1: u32;
  var bw2: u32;
  var z1_shifted: u32;
  var z2_shifted: u32;
  var rlen: u32;
  var z0_f: u32;
  var z1_f: u32;
  var z2_f: u32;
  var s1: u32;
  var c1: u32;
  var s2: u32;
  var c2: u32;
  var __ret: R2;
  if ((n <= 4u)) {
    return;
  } else {
  }
  half = (n / 2u);
  upper = (n - half);
  a_lo = generic_slice_vec(a, 0u, half);
  a_hi = generic_slice_vec(a, half, n);
  b_lo = generic_slice_vec(b, 0u, half);
  b_hi = generic_slice_vec(b, half, n);
  a_lo_p = generic_pad_to_length(a_lo, upper);
  b_lo_p = generic_pad_to_length(b_lo, upper);
  {
    var __td = generic_mul_karatsuba_d0(a_lo_p, b_lo_p, upper);
    z0 = __td._0;
    gz0 = __td._1;
  }
  {
    var __td = generic_mul_karatsuba_d0(a_hi, b_hi, upper);
    z2 = __td._0;
    gz2 = __td._1;
  }
  {
    var __td = generic_add_limbs(a_lo_p, a_hi, upper);
    a_sum_body = __td._0;
    a_carry = __td._1;
  }
  {
    var __td = generic_add_limbs(b_lo_p, b_hi, upper);
    b_sum_body = __td._0;
    b_carry = __td._1;
  }
  a_sum = a_sum_body;
  __call_tmp = fn_18(a_carry);
  b_sum = b_sum_body;
  __call_tmp = fn_19(b_carry);
  {
    var __td = generic_mul_karatsuba_d0(a_sum, b_sum, (upper + 1u));
    z1_full = __td._0;
    gz1f = __td._1;
  }
  tgt = (2u * (upper + 1u));
  z0_p = generic_pad_to_length(z0, tgt);
  z2_p = generic_pad_to_length(z2, tgt);
  {
    var __td = generic_sub_limbs_params(z1_full, z0_p, tgt);
    z1_tmp = __td._0;
    bw1 = __td._1;
  }
  {
    var __td = generic_sub_limbs_params(z1_tmp, z2_p, tgt);
    z1 = __td._0;
    bw2 = __td._1;
  }
  z1_shifted = generic_shift_left(z1, half);
  z2_shifted = generic_shift_left(z2, (2u * half));
  rlen = (2u * n);
  z0_f = generic_pad_to_length(z0, rlen);
  z1_f = generic_pad_to_length(z1_shifted, rlen);
  z2_f = generic_pad_to_length(z2_shifted, rlen);
  {
    var __td = generic_add_limbs(z0_f, z1_f, rlen);
    s1 = __td._0;
    c1 = __td._1;
  }
  {
    var __td = generic_add_limbs(s1, z2_f, rlen);
    s2 = __td._0;
    c2 = __td._1;
  }
  __ret = R2(s2, fn_21((fn_20(c1) + fn_20(c2))));
  return __ret;
}

fn generic_mul_karatsuba_d1(a: u32, b: u32, n: u32) -> R2 {
  var half: u32;
  var upper: u32;
  var a_lo: u32;
  var a_hi: u32;
  var b_lo: u32;
  var b_hi: u32;
  var a_lo_p: u32;
  var b_lo_p: u32;
  var z0: u32;
  var gz0: u32;
  var z2: u32;
  var gz2: u32;
  var a_sum_body: u32;
  var a_carry: u32;
  var b_sum_body: u32;
  var b_carry: u32;
  var a_sum: u32;
  var b_sum: u32;
  var z1_full: u32;
  var gz1f: u32;
  var tgt: u32;
  var z0_p: u32;
  var z2_p: u32;
  var z1_tmp: u32;
  var bw1: u32;
  var z1: u32;
  var bw2: u32;
  var z1_shifted: u32;
  var z2_shifted: u32;
  var rlen: u32;
  var z0_f: u32;
  var z1_f: u32;
  var z2_f: u32;
  var s1: u32;
  var c1: u32;
  var s2: u32;
  var c2: u32;
  var __ret: R2;
  if ((n <= 4u)) {
    return;
  } else {
  }
  half = (n / 2u);
  upper = (n - half);
  a_lo = generic_slice_vec(a, 0u, half);
  a_hi = generic_slice_vec(a, half, n);
  b_lo = generic_slice_vec(b, 0u, half);
  b_hi = generic_slice_vec(b, half, n);
  a_lo_p = generic_pad_to_length(a_lo, upper);
  b_lo_p = generic_pad_to_length(b_lo, upper);
  {
    var __td = generic_mul_karatsuba_d0(a_lo_p, b_lo_p, upper);
    z0 = __td._0;
    gz0 = __td._1;
  }
  {
    var __td = generic_mul_karatsuba_d0(a_hi, b_hi, upper);
    z2 = __td._0;
    gz2 = __td._1;
  }
  {
    var __td = generic_add_limbs(a_lo_p, a_hi, upper);
    a_sum_body = __td._0;
    a_carry = __td._1;
  }
  {
    var __td = generic_add_limbs(b_lo_p, b_hi, upper);
    b_sum_body = __td._0;
    b_carry = __td._1;
  }
  a_sum = a_sum_body;
  __call_tmp = fn_18(a_carry);
  b_sum = b_sum_body;
  __call_tmp = fn_19(b_carry);
  {
    var __td = generic_mul_karatsuba_d0(a_sum, b_sum, (upper + 1u));
    z1_full = __td._0;
    gz1f = __td._1;
  }
  tgt = (2u * (upper + 1u));
  z0_p = generic_pad_to_length(z0, tgt);
  z2_p = generic_pad_to_length(z2, tgt);
  {
    var __td = generic_sub_limbs_params(z1_full, z0_p, tgt);
    z1_tmp = __td._0;
    bw1 = __td._1;
  }
  {
    var __td = generic_sub_limbs_params(z1_tmp, z2_p, tgt);
    z1 = __td._0;
    bw2 = __td._1;
  }
  z1_shifted = generic_shift_left(z1, half);
  z2_shifted = generic_shift_left(z2, (2u * half));
  rlen = (2u * n);
  z0_f = generic_pad_to_length(z0, rlen);
  z1_f = generic_pad_to_length(z1_shifted, rlen);
  z2_f = generic_pad_to_length(z2_shifted, rlen);
  {
    var __td = generic_add_limbs(z0_f, z1_f, rlen);
    s1 = __td._0;
    c1 = __td._1;
  }
  {
    var __td = generic_add_limbs(s1, z2_f, rlen);
    s2 = __td._0;
    c2 = __td._1;
  }
  __ret = R2(s2, fn_21((fn_20(c1) + fn_20(c2))));
  return __ret;
}

fn generic_mul_karatsuba_d2(a: u32, b: u32, n: u32) -> R2 {
  var half: u32;
  var upper: u32;
  var a_lo: u32;
  var a_hi: u32;
  var b_lo: u32;
  var b_hi: u32;
  var a_lo_p: u32;
  var b_lo_p: u32;
  var z0: u32;
  var gz0: u32;
  var z2: u32;
  var gz2: u32;
  var a_sum_body: u32;
  var a_carry: u32;
  var b_sum_body: u32;
  var b_carry: u32;
  var a_sum: u32;
  var b_sum: u32;
  var z1_full: u32;
  var gz1f: u32;
  var tgt: u32;
  var z0_p: u32;
  var z2_p: u32;
  var z1_tmp: u32;
  var bw1: u32;
  var z1: u32;
  var bw2: u32;
  var z1_shifted: u32;
  var z2_shifted: u32;
  var rlen: u32;
  var z0_f: u32;
  var z1_f: u32;
  var z2_f: u32;
  var s1: u32;
  var c1: u32;
  var s2: u32;
  var c2: u32;
  var __ret: R2;
  if ((n <= 4u)) {
    return;
  } else {
  }
  half = (n / 2u);
  upper = (n - half);
  a_lo = generic_slice_vec(a, 0u, half);
  a_hi = generic_slice_vec(a, half, n);
  b_lo = generic_slice_vec(b, 0u, half);
  b_hi = generic_slice_vec(b, half, n);
  a_lo_p = generic_pad_to_length(a_lo, upper);
  b_lo_p = generic_pad_to_length(b_lo, upper);
  {
    var __td = generic_mul_karatsuba_d1(a_lo_p, b_lo_p, upper);
    z0 = __td._0;
    gz0 = __td._1;
  }
  {
    var __td = generic_mul_karatsuba_d1(a_hi, b_hi, upper);
    z2 = __td._0;
    gz2 = __td._1;
  }
  {
    var __td = generic_add_limbs(a_lo_p, a_hi, upper);
    a_sum_body = __td._0;
    a_carry = __td._1;
  }
  {
    var __td = generic_add_limbs(b_lo_p, b_hi, upper);
    b_sum_body = __td._0;
    b_carry = __td._1;
  }
  a_sum = a_sum_body;
  __call_tmp = fn_18(a_carry);
  b_sum = b_sum_body;
  __call_tmp = fn_19(b_carry);
  {
    var __td = generic_mul_karatsuba_d1(a_sum, b_sum, (upper + 1u));
    z1_full = __td._0;
    gz1f = __td._1;
  }
  tgt = (2u * (upper + 1u));
  z0_p = generic_pad_to_length(z0, tgt);
  z2_p = generic_pad_to_length(z2, tgt);
  {
    var __td = generic_sub_limbs_params(z1_full, z0_p, tgt);
    z1_tmp = __td._0;
    bw1 = __td._1;
  }
  {
    var __td = generic_sub_limbs_params(z1_tmp, z2_p, tgt);
    z1 = __td._0;
    bw2 = __td._1;
  }
  z1_shifted = generic_shift_left(z1, half);
  z2_shifted = generic_shift_left(z2, (2u * half));
  rlen = (2u * n);
  z0_f = generic_pad_to_length(z0, rlen);
  z1_f = generic_pad_to_length(z1_shifted, rlen);
  z2_f = generic_pad_to_length(z2_shifted, rlen);
  {
    var __td = generic_add_limbs(z0_f, z1_f, rlen);
    s1 = __td._0;
    c1 = __td._1;
  }
  {
    var __td = generic_add_limbs(s1, z2_f, rlen);
    s2 = __td._0;
    c2 = __td._1;
  }
  __ret = R2(s2, fn_21((fn_20(c1) + fn_20(c2))));
  return __ret;
}

fn generic_mul_karatsuba_d3(a: u32, b: u32, n: u32) -> R2 {
  var half: u32;
  var upper: u32;
  var a_lo: u32;
  var a_hi: u32;
  var b_lo: u32;
  var b_hi: u32;
  var a_lo_p: u32;
  var b_lo_p: u32;
  var z0: u32;
  var gz0: u32;
  var z2: u32;
  var gz2: u32;
  var a_sum_body: u32;
  var a_carry: u32;
  var b_sum_body: u32;
  var b_carry: u32;
  var a_sum: u32;
  var b_sum: u32;
  var z1_full: u32;
  var gz1f: u32;
  var tgt: u32;
  var z0_p: u32;
  var z2_p: u32;
  var z1_tmp: u32;
  var bw1: u32;
  var z1: u32;
  var bw2: u32;
  var z1_shifted: u32;
  var z2_shifted: u32;
  var rlen: u32;
  var z0_f: u32;
  var z1_f: u32;
  var z2_f: u32;
  var s1: u32;
  var c1: u32;
  var s2: u32;
  var c2: u32;
  var __ret: R2;
  if ((n <= 4u)) {
    return;
  } else {
  }
  half = (n / 2u);
  upper = (n - half);
  a_lo = generic_slice_vec(a, 0u, half);
  a_hi = generic_slice_vec(a, half, n);
  b_lo = generic_slice_vec(b, 0u, half);
  b_hi = generic_slice_vec(b, half, n);
  a_lo_p = generic_pad_to_length(a_lo, upper);
  b_lo_p = generic_pad_to_length(b_lo, upper);
  {
    var __td = generic_mul_karatsuba_d2(a_lo_p, b_lo_p, upper);
    z0 = __td._0;
    gz0 = __td._1;
  }
  {
    var __td = generic_mul_karatsuba_d2(a_hi, b_hi, upper);
    z2 = __td._0;
    gz2 = __td._1;
  }
  {
    var __td = generic_add_limbs(a_lo_p, a_hi, upper);
    a_sum_body = __td._0;
    a_carry = __td._1;
  }
  {
    var __td = generic_add_limbs(b_lo_p, b_hi, upper);
    b_sum_body = __td._0;
    b_carry = __td._1;
  }
  a_sum = a_sum_body;
  __call_tmp = fn_18(a_carry);
  b_sum = b_sum_body;
  __call_tmp = fn_19(b_carry);
  {
    var __td = generic_mul_karatsuba_d2(a_sum, b_sum, (upper + 1u));
    z1_full = __td._0;
    gz1f = __td._1;
  }
  tgt = (2u * (upper + 1u));
  z0_p = generic_pad_to_length(z0, tgt);
  z2_p = generic_pad_to_length(z2, tgt);
  {
    var __td = generic_sub_limbs_params(z1_full, z0_p, tgt);
    z1_tmp = __td._0;
    bw1 = __td._1;
  }
  {
    var __td = generic_sub_limbs_params(z1_tmp, z2_p, tgt);
    z1 = __td._0;
    bw2 = __td._1;
  }
  z1_shifted = generic_shift_left(z1, half);
  z2_shifted = generic_shift_left(z2, (2u * half));
  rlen = (2u * n);
  z0_f = generic_pad_to_length(z0, rlen);
  z1_f = generic_pad_to_length(z1_shifted, rlen);
  z2_f = generic_pad_to_length(z2_shifted, rlen);
  {
    var __td = generic_add_limbs(z0_f, z1_f, rlen);
    s1 = __td._0;
    c1 = __td._1;
  }
  {
    var __td = generic_add_limbs(s1, z2_f, rlen);
    s2 = __td._0;
    c2 = __td._1;
  }
  __ret = R2(s2, fn_21((fn_20(c1) + fn_20(c2))));
  return __ret;
}

fn generic_mul_karatsuba_d4(a: u32, b: u32, n: u32) -> R2 {
  var half: u32;
  var upper: u32;
  var a_lo: u32;
  var a_hi: u32;
  var b_lo: u32;
  var b_hi: u32;
  var a_lo_p: u32;
  var b_lo_p: u32;
  var z0: u32;
  var gz0: u32;
  var z2: u32;
  var gz2: u32;
  var a_sum_body: u32;
  var a_carry: u32;
  var b_sum_body: u32;
  var b_carry: u32;
  var a_sum: u32;
  var b_sum: u32;
  var z1_full: u32;
  var gz1f: u32;
  var tgt: u32;
  var z0_p: u32;
  var z2_p: u32;
  var z1_tmp: u32;
  var bw1: u32;
  var z1: u32;
  var bw2: u32;
  var z1_shifted: u32;
  var z2_shifted: u32;
  var rlen: u32;
  var z0_f: u32;
  var z1_f: u32;
  var z2_f: u32;
  var s1: u32;
  var c1: u32;
  var s2: u32;
  var c2: u32;
  var __ret: R2;
  if ((n <= 4u)) {
    return;
  } else {
  }
  half = (n / 2u);
  upper = (n - half);
  a_lo = generic_slice_vec(a, 0u, half);
  a_hi = generic_slice_vec(a, half, n);
  b_lo = generic_slice_vec(b, 0u, half);
  b_hi = generic_slice_vec(b, half, n);
  a_lo_p = generic_pad_to_length(a_lo, upper);
  b_lo_p = generic_pad_to_length(b_lo, upper);
  {
    var __td = generic_mul_karatsuba_d3(a_lo_p, b_lo_p, upper);
    z0 = __td._0;
    gz0 = __td._1;
  }
  {
    var __td = generic_mul_karatsuba_d3(a_hi, b_hi, upper);
    z2 = __td._0;
    gz2 = __td._1;
  }
  {
    var __td = generic_add_limbs(a_lo_p, a_hi, upper);
    a_sum_body = __td._0;
    a_carry = __td._1;
  }
  {
    var __td = generic_add_limbs(b_lo_p, b_hi, upper);
    b_sum_body = __td._0;
    b_carry = __td._1;
  }
  a_sum = a_sum_body;
  __call_tmp = fn_18(a_carry);
  b_sum = b_sum_body;
  __call_tmp = fn_19(b_carry);
  {
    var __td = generic_mul_karatsuba_d3(a_sum, b_sum, (upper + 1u));
    z1_full = __td._0;
    gz1f = __td._1;
  }
  tgt = (2u * (upper + 1u));
  z0_p = generic_pad_to_length(z0, tgt);
  z2_p = generic_pad_to_length(z2, tgt);
  {
    var __td = generic_sub_limbs_params(z1_full, z0_p, tgt);
    z1_tmp = __td._0;
    bw1 = __td._1;
  }
  {
    var __td = generic_sub_limbs_params(z1_tmp, z2_p, tgt);
    z1 = __td._0;
    bw2 = __td._1;
  }
  z1_shifted = generic_shift_left(z1, half);
  z2_shifted = generic_shift_left(z2, (2u * half));
  rlen = (2u * n);
  z0_f = generic_pad_to_length(z0, rlen);
  z1_f = generic_pad_to_length(z1_shifted, rlen);
  z2_f = generic_pad_to_length(z2_shifted, rlen);
  {
    var __td = generic_add_limbs(z0_f, z1_f, rlen);
    s1 = __td._0;
    c1 = __td._1;
  }
  {
    var __td = generic_add_limbs(s1, z2_f, rlen);
    s2 = __td._0;
    c2 = __td._1;
  }
  __ret = R2(s2, fn_21((fn_20(c1) + fn_20(c2))));
  return __ret;
}

fn generic_mul_karatsuba_d5(a: u32, b: u32, n: u32) -> R2 {
  var half: u32;
  var upper: u32;
  var a_lo: u32;
  var a_hi: u32;
  var b_lo: u32;
  var b_hi: u32;
  var a_lo_p: u32;
  var b_lo_p: u32;
  var z0: u32;
  var gz0: u32;
  var z2: u32;
  var gz2: u32;
  var a_sum_body: u32;
  var a_carry: u32;
  var b_sum_body: u32;
  var b_carry: u32;
  var a_sum: u32;
  var b_sum: u32;
  var z1_full: u32;
  var gz1f: u32;
  var tgt: u32;
  var z0_p: u32;
  var z2_p: u32;
  var z1_tmp: u32;
  var bw1: u32;
  var z1: u32;
  var bw2: u32;
  var z1_shifted: u32;
  var z2_shifted: u32;
  var rlen: u32;
  var z0_f: u32;
  var z1_f: u32;
  var z2_f: u32;
  var s1: u32;
  var c1: u32;
  var s2: u32;
  var c2: u32;
  var __ret: R2;
  if ((n <= 4u)) {
    return;
  } else {
  }
  half = (n / 2u);
  upper = (n - half);
  a_lo = generic_slice_vec(a, 0u, half);
  a_hi = generic_slice_vec(a, half, n);
  b_lo = generic_slice_vec(b, 0u, half);
  b_hi = generic_slice_vec(b, half, n);
  a_lo_p = generic_pad_to_length(a_lo, upper);
  b_lo_p = generic_pad_to_length(b_lo, upper);
  {
    var __td = generic_mul_karatsuba_d4(a_lo_p, b_lo_p, upper);
    z0 = __td._0;
    gz0 = __td._1;
  }
  {
    var __td = generic_mul_karatsuba_d4(a_hi, b_hi, upper);
    z2 = __td._0;
    gz2 = __td._1;
  }
  {
    var __td = generic_add_limbs(a_lo_p, a_hi, upper);
    a_sum_body = __td._0;
    a_carry = __td._1;
  }
  {
    var __td = generic_add_limbs(b_lo_p, b_hi, upper);
    b_sum_body = __td._0;
    b_carry = __td._1;
  }
  a_sum = a_sum_body;
  __call_tmp = fn_18(a_carry);
  b_sum = b_sum_body;
  __call_tmp = fn_19(b_carry);
  {
    var __td = generic_mul_karatsuba_d4(a_sum, b_sum, (upper + 1u));
    z1_full = __td._0;
    gz1f = __td._1;
  }
  tgt = (2u * (upper + 1u));
  z0_p = generic_pad_to_length(z0, tgt);
  z2_p = generic_pad_to_length(z2, tgt);
  {
    var __td = generic_sub_limbs_params(z1_full, z0_p, tgt);
    z1_tmp = __td._0;
    bw1 = __td._1;
  }
  {
    var __td = generic_sub_limbs_params(z1_tmp, z2_p, tgt);
    z1 = __td._0;
    bw2 = __td._1;
  }
  z1_shifted = generic_shift_left(z1, half);
  z2_shifted = generic_shift_left(z2, (2u * half));
  rlen = (2u * n);
  z0_f = generic_pad_to_length(z0, rlen);
  z1_f = generic_pad_to_length(z1_shifted, rlen);
  z2_f = generic_pad_to_length(z2_shifted, rlen);
  {
    var __td = generic_add_limbs(z0_f, z1_f, rlen);
    s1 = __td._0;
    c1 = __td._1;
  }
  {
    var __td = generic_add_limbs(s1, z2_f, rlen);
    s2 = __td._0;
    c2 = __td._1;
  }
  __ret = R2(s2, fn_21((fn_20(c1) + fn_20(c2))));
  return __ret;
}

fn generic_mul_karatsuba_d6(a: u32, b: u32, n: u32) -> R2 {
  var half: u32;
  var upper: u32;
  var a_lo: u32;
  var a_hi: u32;
  var b_lo: u32;
  var b_hi: u32;
  var a_lo_p: u32;
  var b_lo_p: u32;
  var z0: u32;
  var gz0: u32;
  var z2: u32;
  var gz2: u32;
  var a_sum_body: u32;
  var a_carry: u32;
  var b_sum_body: u32;
  var b_carry: u32;
  var a_sum: u32;
  var b_sum: u32;
  var z1_full: u32;
  var gz1f: u32;
  var tgt: u32;
  var z0_p: u32;
  var z2_p: u32;
  var z1_tmp: u32;
  var bw1: u32;
  var z1: u32;
  var bw2: u32;
  var z1_shifted: u32;
  var z2_shifted: u32;
  var rlen: u32;
  var z0_f: u32;
  var z1_f: u32;
  var z2_f: u32;
  var s1: u32;
  var c1: u32;
  var s2: u32;
  var c2: u32;
  var __ret: R2;
  if ((n <= 4u)) {
    return;
  } else {
  }
  half = (n / 2u);
  upper = (n - half);
  a_lo = generic_slice_vec(a, 0u, half);
  a_hi = generic_slice_vec(a, half, n);
  b_lo = generic_slice_vec(b, 0u, half);
  b_hi = generic_slice_vec(b, half, n);
  a_lo_p = generic_pad_to_length(a_lo, upper);
  b_lo_p = generic_pad_to_length(b_lo, upper);
  {
    var __td = generic_mul_karatsuba_d5(a_lo_p, b_lo_p, upper);
    z0 = __td._0;
    gz0 = __td._1;
  }
  {
    var __td = generic_mul_karatsuba_d5(a_hi, b_hi, upper);
    z2 = __td._0;
    gz2 = __td._1;
  }
  {
    var __td = generic_add_limbs(a_lo_p, a_hi, upper);
    a_sum_body = __td._0;
    a_carry = __td._1;
  }
  {
    var __td = generic_add_limbs(b_lo_p, b_hi, upper);
    b_sum_body = __td._0;
    b_carry = __td._1;
  }
  a_sum = a_sum_body;
  __call_tmp = fn_18(a_carry);
  b_sum = b_sum_body;
  __call_tmp = fn_19(b_carry);
  {
    var __td = generic_mul_karatsuba_d5(a_sum, b_sum, (upper + 1u));
    z1_full = __td._0;
    gz1f = __td._1;
  }
  tgt = (2u * (upper + 1u));
  z0_p = generic_pad_to_length(z0, tgt);
  z2_p = generic_pad_to_length(z2, tgt);
  {
    var __td = generic_sub_limbs_params(z1_full, z0_p, tgt);
    z1_tmp = __td._0;
    bw1 = __td._1;
  }
  {
    var __td = generic_sub_limbs_params(z1_tmp, z2_p, tgt);
    z1 = __td._0;
    bw2 = __td._1;
  }
  z1_shifted = generic_shift_left(z1, half);
  z2_shifted = generic_shift_left(z2, (2u * half));
  rlen = (2u * n);
  z0_f = generic_pad_to_length(z0, rlen);
  z1_f = generic_pad_to_length(z1_shifted, rlen);
  z2_f = generic_pad_to_length(z2_shifted, rlen);
  {
    var __td = generic_add_limbs(z0_f, z1_f, rlen);
    s1 = __td._0;
    c1 = __td._1;
  }
  {
    var __td = generic_add_limbs(s1, z2_f, rlen);
    s2 = __td._0;
    c2 = __td._1;
  }
  __ret = R2(s2, fn_21((fn_20(c1) + fn_20(c2))));
  return __ret;
}

fn generic_slice_vec(a: u32, start: u32, end: u32) -> u32 {
  var out_len: u32;
  var i: u32;
  var __ret: u32;
  out_len = 0u;
  for (var i: u32 = start; i < end; i++) {
    scratch[(out + out_len)] = clone_limb(scratch[(a + i)]);
    out_len = out_len + 1u;
  }
  __ret = out;
  return __ret;
}

fn sub_borrow(self_val: u32, b: u32, borrow: u32) -> R2 {
  var borrow: u32;
  var ab: u32;
  var bw1: u32;
  var result: u32;
  var bw2: u32;
  var __ret: R2;
  ab = (self_val - b);
  bw1 = select(0u, 1u, (self_val < b));
  result = (ab - borrow);
  bw2 = select(0u, 1u, (ab < borrow));
  __ret = R2(result, (bw1 + bw2));
  return __ret;
}

fn mul2(self_val: u32, b: u32) -> R2 {
  var b: u32;
  var lo: u32;
  var a_lo: u32;
  var a_hi: u32;
  var b_lo: u32;
  var b_hi: u32;
  var p0: u32;
  var p1: u32;
  var p2: u32;
  var p3: u32;
  var p0_hi: u32;
  var mid: u32;
  var hi: u32;
  var __ret: R2;
  lo = (self_val * b);
  a_lo = (self_val & 0u);
  a_hi = (self_val >> 16u);
  b_lo = (b & 0u);
  b_hi = (b >> 16u);
  p0 = (a_lo * b_lo);
  p1 = (a_lo * b_hi);
  p2 = (a_hi * b_lo);
  p3 = (a_hi * b_hi);
  p0_hi = (p0 >> 16u);
  mid = ((p0_hi + (p1 & 0u)) + (p2 & 0u));
  hi = (((p3 + (p1 >> 16u)) + (p2 >> 16u)) + (mid >> 16u));
  __ret = R2(lo, hi);
  return __ret;
}

fn generic_select_vec(cond: u32, if_zero: u32, if_nonzero: u32, n: u32) -> u32 {
  var out_len: u32;
  var i: u32;
  var selected: u32;
  var __ret: u32;
  out_len = 0u;
  for (var i: u32 = 0u; i < n; i++) {
    selected = select_limb(cond, clone_limb(scratch[(if_zero + i)]), clone_limb(scratch[(if_nonzero + i)]));
    scratch[(out + out_len)] = selected;
    out_len = out_len + 1u;
  }
  __ret = out;
  return __ret;
}

fn generic_add_limbs(a: u32, b: u32, n: u32) -> R2 {
  var out_len: u32;
  var carry: u32;
  var i: u32;
  var digit: u32;
  var next_carry: u32;
  var __ret: R2;
  out_len = 0u;
  carry = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var __td = add3(scratch[(a + i)], scratch[(b + i)], carry);
      digit = __td._0;
      next_carry = __td._1;
    }
    scratch[(out + out_len)] = digit;
    out_len = out_len + 1u;
    carry = next_carry;
  }
  __ret = R2(out, carry);
  return __ret;
}

fn is_zero_limb(self_val: u32) -> u32 {
  var self: u32;
  var __ret: u32;
  if ((self_val == 0u)) {
    __ret = 1u;
  } else {
    __ret = 0u;
  }
  return __ret;
}

fn zero_val() -> u32 {
  var __ret: u32;
  __ret = 0u;
  return __ret;
}

fn generic_pad_to_length(a: u32, target: u32) -> u32 {
  var out_len: u32;
  var i: u32;
  var __ret: u32;
  out_len = 0u;
  for (var i: u32 = 0u; i < fn_18(a); i++) {
    scratch[(out + out_len)] = clone_limb(scratch[(a + i)]);
    out_len = out_len + 1u;
  }
  for (var i: u32 = fn_18(a); i < target; i++) {
    scratch[(out + out_len)] = zero_val();
    out_len = out_len + 1u;
  }
  __ret = out;
  return __ret;
}

fn generic_shift_left(a: u32, offset: u32) -> u32 {
  var out_len: u32;
  var i: u32;
  var k: u32;
  var __ret: u32;
  out_len = 0u;
  for (var i: u32 = 0u; i < offset; i++) {
    scratch[(out + out_len)] = zero_val();
    out_len = out_len + 1u;
  }
  for (var k: u32 = 0u; k < fn_18(a); k++) {
    scratch[(out + out_len)] = clone_limb(scratch[(a + k)]);
    out_len = out_len + 1u;
  }
  __ret = out;
  return __ret;
}

fn clone_limb(self_val: u32) -> u32 {
  var self: u32;
  var __ret: u32;
  __ret = self_val;
  return __ret;
}

fn add3(self_val: u32, b: u32, carry: u32) -> R2 {
  var carry: u32;
  var ab: u32;
  var c1: u32;
  var abc: u32;
  var c2: u32;
  var __ret: R2;
  ab = (self_val + b);
  c1 = select(0u, 1u, (ab < self_val));
  abc = (ab + carry);
  c2 = select(0u, 1u, (abc < ab));
  __ret = R2(abc, (c1 + c2));
  return __ret;
}

@compute @workgroup_size(16, 16, 1)
fn mandelbrot_fixedpoint(
  @builtin(global_invocation_id) gid: vec3<u32>,
) {
  let gid_x = gid.x;
  let gid_y = gid.y;
  var width: u32;
  var height: u32;
  var max_iters: u32;
  var n: u32;
  var frac_limbs: u32;
  var tid: u32;
  var stride: u32;
  var c_base: u32;
  var words_per_thread: u32;
  var sb: u32;
  var zr_off: u32;
  var zr_sign_off: u32;
  var zi_off: u32;
  var zi_sign_off: u32;
  var i: u32;
  var escaped_iter: u32;
  var iter: u32;
  var re2: u32;
  var re2_sign: u32;
  var im2: u32;
  var im2_sign: u32;
  var re_plus_im: u32;
  var rpi_sign: u32;
  var sum2: u32;
  var sum2_sign: u32;
  var re_diff: u32;
  var re_diff_sign: u32;
  var new_re: u32;
  var new_re_sign: u32;
  var t1: u32;
  var t1_sign: u32;
  var t2: u32;
  var t2_sign: u32;
  var c_im_base: u32;
  var new_im: u32;
  var new_im_sign: u32;
  var mag: u32;
  var _mag_sign: u32;
  var thresh_off: u32;
  var _diff: u32;
  var borrow: u32;
  width = params[0u];
  height = params[1u];
  max_iters = params[2u];
  n = params[3u];
  frac_limbs = params[4u];
  if ((gid_x >= width)) {
    return;
  } else {
  }
  if ((gid_y >= height)) {
    return;
  } else {
  }
  tid = ((gid_y * width) + gid_x);
  stride = ((2u * n) + 2u);
  c_base = (tid * stride);
  words_per_thread = ((7u * n) + 3u);
  sb = (tid * words_per_thread);
  zr_off = sb;
  zr_sign_off = (sb + n);
  zi_off = ((sb + n) + 1u);
  zi_sign_off = ((sb + (2u * n)) + 1u);
  for (var i: u32 = 0u; i < n; i++) {
    scratch[(zr_off + i)] = 0u;
    scratch[(zi_off + i)] = 0u;
  }
  scratch[zr_sign_off] = 0u;
  scratch[zi_sign_off] = 0u;
  escaped_iter = max_iters;
  for (var iter: u32 = 0u; iter < max_iters; iter++) {
    {
      var __td = fp_mul_scratch_scratch(zr_off, scratch[zr_sign_off], zr_off, scratch[zr_sign_off], n, frac_limbs);
      re2 = __td._0;
      re2_sign = __td._1;
    }
    {
      var __td = fp_mul_scratch_scratch(zi_off, scratch[zi_sign_off], zi_off, scratch[zi_sign_off], n, frac_limbs);
      im2 = __td._0;
      im2_sign = __td._1;
    }
    {
      var __td = fp_signed_add_c_data(zr_off, scratch[zr_sign_off], zi_off, scratch[zi_sign_off], n);
      re_plus_im = __td._0;
      rpi_sign = __td._1;
    }
    {
      var __td = fp_mul_scratch_scratch(re_plus_im, rpi_sign, re_plus_im, rpi_sign, n, frac_limbs);
      sum2 = __td._0;
      sum2_sign = __td._1;
    }
    {
      var __td = fp_signed_sub(re2, re2_sign, im2, im2_sign, n);
      re_diff = __td._0;
      re_diff_sign = __td._1;
    }
    {
      var __td = fp_signed_add_c_data(re_diff, re_diff_sign, c_base, c_data[(c_base + n)], n);
      new_re = __td._0;
      new_re_sign = __td._1;
    }
    {
      var __td = fp_signed_sub(sum2, sum2_sign, re2, re2_sign, n);
      t1 = __td._0;
      t1_sign = __td._1;
    }
    {
      var __td = fp_signed_sub(t1, t1_sign, im2, im2_sign, n);
      t2 = __td._0;
      t2_sign = __td._1;
    }
    c_im_base = ((c_base + n) + 1u);
    {
      var __td = fp_signed_add_c_data(t2, t2_sign, c_im_base, c_data[(c_im_base + n)], n);
      new_im = __td._0;
      new_im_sign = __td._1;
    }
    for (var i: u32 = 0u; i < n; i++) {
      scratch[(zr_off + i)] = new_re;
      scratch[(zi_off + i)] = new_im;
    }
    scratch[zr_sign_off] = new_re_sign;
    scratch[zi_sign_off] = new_im_sign;
    {
      var __td = fp_mag_squared(new_re, new_re_sign, new_im, new_im_sign, n, frac_limbs);
      mag = __td._0;
      _mag_sign = __td._1;
    }
    thresh_off = 5u;
    {
      var __td = generic_sub_limbs_params(mag, thresh_off, n);
      _diff = __td._0;
      borrow = __td._1;
    }
    if ((borrow == 0u)) {
      if ((escaped_iter == max_iters)) {
        escaped_iter = iter;
      } else {
      }
    } else {
    }
  }
  iter_counts[tid] = escaped_iter;
}

