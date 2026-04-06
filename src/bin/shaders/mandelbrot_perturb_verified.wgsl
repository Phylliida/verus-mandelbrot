struct R2 {
  _0: u32,
  _1: u32,
}

struct R3 {
  _0: u32,
  _1: u32,
  _2: u32,
}

@group(0) @binding(0) var<storage, read> orbit_re: array<u32>;
@group(0) @binding(1) var<storage, read> orbit_im: array<u32>;
@group(0) @binding(2) var<storage, read> delta_c: array<u32>;
@group(0) @binding(3) var<storage, read> params: array<u32>;
@group(0) @binding(4) var<storage, read_write> scratch: array<u32>;
@group(0) @binding(5) var<storage, read_write> iter_counts: array<u32>;

fn generic_mul_karatsuba_scratch_scratch_scratch_d0(a: u32, b: u32, n: u32, out: u32) -> u32 {
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
  var __ret: u32;
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
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d0(a_lo_p, b_lo_p, upper);
    z0 = __td._0;
    gz0 = __td._1;
  }
  {
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d0(a_hi, b_hi, upper);
    z2 = __td._0;
    gz2 = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(a_lo_p, a_hi, upper);
    a_sum_body = __td._0;
    a_carry = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(b_lo_p, b_hi, upper);
    b_sum_body = __td._0;
    b_carry = __td._1;
  }
  a_sum = a_sum_body;
  __call_tmp = fn_23(a_carry);
  b_sum = b_sum_body;
  __call_tmp = fn_24(b_carry);
  {
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d0(a_sum, b_sum, (upper + 1u));
    z1_full = __td._0;
    gz1f = __td._1;
  }
  tgt = (2u * (upper + 1u));
  z0_p = generic_pad_to_length(z0, tgt);
  z2_p = generic_pad_to_length(z2, tgt);
  {
    var __td = generic_sub_limbs_scratch_params_scratch(z1_full, z0_p, tgt);
    z1_tmp = __td._0;
    bw1 = __td._1;
  }
  {
    var __td = generic_sub_limbs_scratch_params_scratch(z1_tmp, z2_p, tgt);
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
    var __td = generic_add_limbs_scratch_scratch_scratch(z0_f, z1_f, rlen);
    s1 = __td._0;
    c1 = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(s1, z2_f, rlen);
    s2 = __td._0;
    c2 = __td._1;
  }
  __ret = fn_26((fn_25(c1) + fn_25(c2)));
  return __ret;
}

fn generic_mul_karatsuba_scratch_scratch_scratch_d1(a: u32, b: u32, n: u32, out: u32) -> u32 {
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
  var __ret: u32;
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
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d0(a_lo_p, b_lo_p, upper);
    z0 = __td._0;
    gz0 = __td._1;
  }
  {
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d0(a_hi, b_hi, upper);
    z2 = __td._0;
    gz2 = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(a_lo_p, a_hi, upper);
    a_sum_body = __td._0;
    a_carry = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(b_lo_p, b_hi, upper);
    b_sum_body = __td._0;
    b_carry = __td._1;
  }
  a_sum = a_sum_body;
  __call_tmp = fn_23(a_carry);
  b_sum = b_sum_body;
  __call_tmp = fn_24(b_carry);
  {
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d0(a_sum, b_sum, (upper + 1u));
    z1_full = __td._0;
    gz1f = __td._1;
  }
  tgt = (2u * (upper + 1u));
  z0_p = generic_pad_to_length(z0, tgt);
  z2_p = generic_pad_to_length(z2, tgt);
  {
    var __td = generic_sub_limbs_scratch_params_scratch(z1_full, z0_p, tgt);
    z1_tmp = __td._0;
    bw1 = __td._1;
  }
  {
    var __td = generic_sub_limbs_scratch_params_scratch(z1_tmp, z2_p, tgt);
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
    var __td = generic_add_limbs_scratch_scratch_scratch(z0_f, z1_f, rlen);
    s1 = __td._0;
    c1 = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(s1, z2_f, rlen);
    s2 = __td._0;
    c2 = __td._1;
  }
  __ret = fn_26((fn_25(c1) + fn_25(c2)));
  return __ret;
}

fn generic_mul_karatsuba_scratch_scratch_scratch_d2(a: u32, b: u32, n: u32, out: u32) -> u32 {
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
  var __ret: u32;
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
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d1(a_lo_p, b_lo_p, upper);
    z0 = __td._0;
    gz0 = __td._1;
  }
  {
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d1(a_hi, b_hi, upper);
    z2 = __td._0;
    gz2 = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(a_lo_p, a_hi, upper);
    a_sum_body = __td._0;
    a_carry = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(b_lo_p, b_hi, upper);
    b_sum_body = __td._0;
    b_carry = __td._1;
  }
  a_sum = a_sum_body;
  __call_tmp = fn_23(a_carry);
  b_sum = b_sum_body;
  __call_tmp = fn_24(b_carry);
  {
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d1(a_sum, b_sum, (upper + 1u));
    z1_full = __td._0;
    gz1f = __td._1;
  }
  tgt = (2u * (upper + 1u));
  z0_p = generic_pad_to_length(z0, tgt);
  z2_p = generic_pad_to_length(z2, tgt);
  {
    var __td = generic_sub_limbs_scratch_params_scratch(z1_full, z0_p, tgt);
    z1_tmp = __td._0;
    bw1 = __td._1;
  }
  {
    var __td = generic_sub_limbs_scratch_params_scratch(z1_tmp, z2_p, tgt);
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
    var __td = generic_add_limbs_scratch_scratch_scratch(z0_f, z1_f, rlen);
    s1 = __td._0;
    c1 = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(s1, z2_f, rlen);
    s2 = __td._0;
    c2 = __td._1;
  }
  __ret = fn_26((fn_25(c1) + fn_25(c2)));
  return __ret;
}

fn generic_mul_karatsuba_scratch_scratch_scratch_d3(a: u32, b: u32, n: u32, out: u32) -> u32 {
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
  var __ret: u32;
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
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d2(a_lo_p, b_lo_p, upper);
    z0 = __td._0;
    gz0 = __td._1;
  }
  {
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d2(a_hi, b_hi, upper);
    z2 = __td._0;
    gz2 = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(a_lo_p, a_hi, upper);
    a_sum_body = __td._0;
    a_carry = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(b_lo_p, b_hi, upper);
    b_sum_body = __td._0;
    b_carry = __td._1;
  }
  a_sum = a_sum_body;
  __call_tmp = fn_23(a_carry);
  b_sum = b_sum_body;
  __call_tmp = fn_24(b_carry);
  {
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d2(a_sum, b_sum, (upper + 1u));
    z1_full = __td._0;
    gz1f = __td._1;
  }
  tgt = (2u * (upper + 1u));
  z0_p = generic_pad_to_length(z0, tgt);
  z2_p = generic_pad_to_length(z2, tgt);
  {
    var __td = generic_sub_limbs_scratch_params_scratch(z1_full, z0_p, tgt);
    z1_tmp = __td._0;
    bw1 = __td._1;
  }
  {
    var __td = generic_sub_limbs_scratch_params_scratch(z1_tmp, z2_p, tgt);
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
    var __td = generic_add_limbs_scratch_scratch_scratch(z0_f, z1_f, rlen);
    s1 = __td._0;
    c1 = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(s1, z2_f, rlen);
    s2 = __td._0;
    c2 = __td._1;
  }
  __ret = fn_26((fn_25(c1) + fn_25(c2)));
  return __ret;
}

fn generic_mul_karatsuba_scratch_scratch_scratch_d4(a: u32, b: u32, n: u32, out: u32) -> u32 {
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
  var __ret: u32;
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
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d3(a_lo_p, b_lo_p, upper);
    z0 = __td._0;
    gz0 = __td._1;
  }
  {
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d3(a_hi, b_hi, upper);
    z2 = __td._0;
    gz2 = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(a_lo_p, a_hi, upper);
    a_sum_body = __td._0;
    a_carry = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(b_lo_p, b_hi, upper);
    b_sum_body = __td._0;
    b_carry = __td._1;
  }
  a_sum = a_sum_body;
  __call_tmp = fn_23(a_carry);
  b_sum = b_sum_body;
  __call_tmp = fn_24(b_carry);
  {
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d3(a_sum, b_sum, (upper + 1u));
    z1_full = __td._0;
    gz1f = __td._1;
  }
  tgt = (2u * (upper + 1u));
  z0_p = generic_pad_to_length(z0, tgt);
  z2_p = generic_pad_to_length(z2, tgt);
  {
    var __td = generic_sub_limbs_scratch_params_scratch(z1_full, z0_p, tgt);
    z1_tmp = __td._0;
    bw1 = __td._1;
  }
  {
    var __td = generic_sub_limbs_scratch_params_scratch(z1_tmp, z2_p, tgt);
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
    var __td = generic_add_limbs_scratch_scratch_scratch(z0_f, z1_f, rlen);
    s1 = __td._0;
    c1 = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(s1, z2_f, rlen);
    s2 = __td._0;
    c2 = __td._1;
  }
  __ret = fn_26((fn_25(c1) + fn_25(c2)));
  return __ret;
}

fn generic_mul_karatsuba_scratch_scratch_scratch_d5(a: u32, b: u32, n: u32, out: u32) -> u32 {
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
  var __ret: u32;
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
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d4(a_lo_p, b_lo_p, upper);
    z0 = __td._0;
    gz0 = __td._1;
  }
  {
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d4(a_hi, b_hi, upper);
    z2 = __td._0;
    gz2 = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(a_lo_p, a_hi, upper);
    a_sum_body = __td._0;
    a_carry = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(b_lo_p, b_hi, upper);
    b_sum_body = __td._0;
    b_carry = __td._1;
  }
  a_sum = a_sum_body;
  __call_tmp = fn_23(a_carry);
  b_sum = b_sum_body;
  __call_tmp = fn_24(b_carry);
  {
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d4(a_sum, b_sum, (upper + 1u));
    z1_full = __td._0;
    gz1f = __td._1;
  }
  tgt = (2u * (upper + 1u));
  z0_p = generic_pad_to_length(z0, tgt);
  z2_p = generic_pad_to_length(z2, tgt);
  {
    var __td = generic_sub_limbs_scratch_params_scratch(z1_full, z0_p, tgt);
    z1_tmp = __td._0;
    bw1 = __td._1;
  }
  {
    var __td = generic_sub_limbs_scratch_params_scratch(z1_tmp, z2_p, tgt);
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
    var __td = generic_add_limbs_scratch_scratch_scratch(z0_f, z1_f, rlen);
    s1 = __td._0;
    c1 = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(s1, z2_f, rlen);
    s2 = __td._0;
    c2 = __td._1;
  }
  __ret = fn_26((fn_25(c1) + fn_25(c2)));
  return __ret;
}

fn generic_mul_karatsuba_scratch_scratch_scratch_d6(a: u32, b: u32, n: u32, out: u32) -> u32 {
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
  var __ret: u32;
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
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d5(a_lo_p, b_lo_p, upper);
    z0 = __td._0;
    gz0 = __td._1;
  }
  {
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d5(a_hi, b_hi, upper);
    z2 = __td._0;
    gz2 = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(a_lo_p, a_hi, upper);
    a_sum_body = __td._0;
    a_carry = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(b_lo_p, b_hi, upper);
    b_sum_body = __td._0;
    b_carry = __td._1;
  }
  a_sum = a_sum_body;
  __call_tmp = fn_23(a_carry);
  b_sum = b_sum_body;
  __call_tmp = fn_24(b_carry);
  {
    var __td = generic_mul_karatsuba_scratch_scratch_scratch_d5(a_sum, b_sum, (upper + 1u));
    z1_full = __td._0;
    gz1f = __td._1;
  }
  tgt = (2u * (upper + 1u));
  z0_p = generic_pad_to_length(z0, tgt);
  z2_p = generic_pad_to_length(z2, tgt);
  {
    var __td = generic_sub_limbs_scratch_params_scratch(z1_full, z0_p, tgt);
    z1_tmp = __td._0;
    bw1 = __td._1;
  }
  {
    var __td = generic_sub_limbs_scratch_params_scratch(z1_tmp, z2_p, tgt);
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
    var __td = generic_add_limbs_scratch_scratch_scratch(z0_f, z1_f, rlen);
    s1 = __td._0;
    c1 = __td._1;
  }
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(s1, z2_f, rlen);
    s2 = __td._0;
    c2 = __td._1;
  }
  __ret = fn_26((fn_25(c1) + fn_25(c2)));
  return __ret;
}

fn generic_add_limbs_scratch_scratch_scratch(a: u32, b: u32, n: u32, out: u32) -> u32 {
  var out_len: u32;
  var carry: u32;
  var i: u32;
  var digit: u32;
  var next_carry: u32;
  var __ret: u32;
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
  __ret = carry;
  return __ret;
}

fn mersenne_reduce_exec_scratch_scratch(product: u32, n: u32, c: u32, out: u32) -> u32 {
  var c_limb: u32;
  var lo: u32;
  var hi: u32;
  var hi_c: u32;
  var lo_pad: u32;
  var wide: u32;
  var wide_cy: u32;
  var wide_lo: u32;
  var wide_top: u32;
  var wt_lo: u32;
  var wt_hi: u32;
  var wt_vec: u32;
  var fold2: u32;
  var cy2: u32;
  var r: u32;
  var __ret: u32;
  c_limb = const_u32(c);
  lo = generic_slice_vec(product, 0u, n);
  hi = generic_slice_vec(product, n, (2u * n));
  hi_c = generic_mul_by_limb(hi, c_limb, n);
  lo_pad = generic_pad_to_length(lo, (n + 1u));
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(lo_pad, hi_c, (n + 1u));
    wide = __td._0;
    wide_cy = __td._1;
  }
  wide_lo = generic_slice_vec(wide, 0u, n);
  wide_top = clone_limb(wide);
  {
    var __td = mul2(wide_top, c_limb);
    wt_lo = __td._0;
    wt_hi = __td._1;
  }
  wt_vec = pair_to_padded_vec(wt_lo, wt_hi, n);
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(wide_lo, wt_vec, n);
    fold2 = __td._0;
    cy2 = __td._1;
  }
  r = mersenne_carry_folds(fold2, cy2, wide_cy, n, c);
  __ret = r;
  return __ret;
}

fn generic_sub_limbs_scratch_params_scratch(a: u32, b: u32, n: u32, out: u32) -> u32 {
  var out_len: u32;
  var borrow: u32;
  var i: u32;
  var digit: u32;
  var next_borrow: u32;
  var __ret: u32;
  out_len = 0u;
  borrow = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var __td = sub_borrow(scratch[(a + i)], params[(b + i)], borrow);
      digit = __td._0;
      next_borrow = __td._1;
    }
    scratch[(out + out_len)] = digit;
    out_len = out_len + 1u;
    borrow = next_borrow;
  }
  __ret = borrow;
  return __ret;
}

fn generic_pad_to_length(a: u32, target: u32) -> u32 {
  var out_len: u32;
  var i: u32;
  var __ret: u32;
  out_len = 0u;
  for (var i: u32 = 0u; i < fn_23(a); i++) {
    scratch[(out + out_len)] = clone_limb(scratch[(a + i)]);
    out_len = out_len + 1u;
  }
  for (var i: u32 = fn_23(a); i < target; i++) {
    scratch[(out + out_len)] = zero_val();
    out_len = out_len + 1u;
  }
  __ret = out;
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
  for (var k: u32 = 0u; k < fn_23(a); k++) {
    scratch[(out + out_len)] = clone_limb(scratch[(a + k)]);
    out_len = out_len + 1u;
  }
  __ret = out;
  return __ret;
}

fn zero_val() -> u32 {
  var __ret: u32;
  __ret = 0u;
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

fn mersenne_carry_folds(fold2: u32, cy2: u32, wide_cy: u32, n: u32, c: u32) -> u32 {
  var fold5: u32;
  var cy4: u32;
  var cy5: u32;
  var __ret: u32;
  {
    var __td = mersenne_carry_early(fold2, cy2, wide_cy, n, c);
    fold5 = __td._0;
    cy4 = __td._1;
    cy5 = __td._2;
  }
  __ret = mersenne_carry_late(fold5, cy4, cy5, n, c);
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

fn const_u32(c: u32) -> u32 {
  var __ret: u32;
  __ret = c;
  return __ret;
}

fn generic_mul_by_limb(a: u32, scalar: u32, n: u32) -> u32 {
  var out_len: u32;
  var carry: u32;
  var i: u32;
  var digit: u32;
  var next_carry: u32;
  var __ret: u32;
  out_len = 0u;
  carry = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var __td = mul_add_carry(scratch[(a + i)], scalar, zero_val(), carry);
      digit = __td._0;
      next_carry = __td._1;
    }
    scratch[(out + out_len)] = digit;
    out_len = out_len + 1u;
    carry = next_carry;
  }
  scratch[(out + out_len)] = carry;
  out_len = out_len + 1u;
  __ret = out;
  return __ret;
}

fn clone_limb(self_val: u32) -> u32 {
  var self: u32;
  var __ret: u32;
  __ret = self_val;
  return __ret;
}

fn pair_to_padded_vec(lo: u32, hi: u32, n: u32) -> u32 {
  var v: u32;
  var v_len: u32;
  var result: u32;
  var __ret: u32;
  v_len = 0u;
  scratch[(v + v_len)] = lo;
  v_len = v_len + 1u;
  scratch[(v + v_len)] = hi;
  v_len = v_len + 1u;
  result = generic_pad_to_length(v, n);
  __ret = result;
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

fn mersenne_carry_late(fold5: u32, cy4: u32, cy5: u32, n: u32, c: u32) -> u32 {
  var c_limb: u32;
  var cy4_c: u32;
  var cy4_vec: u32;
  var fold6: u32;
  var _cy6: u32;
  var cy5_c: u32;
  var cy5_vec: u32;
  var fold7: u32;
  var cy7: u32;
  var _cy6_c: u32;
  var cy7_c: u32;
  var final_c: u32;
  var final_c_carry: u32;
  var final_vec: u32;
  var fold8: u32;
  var _cy8: u32;
  var cy8_c: u32;
  var cy8_vec: u32;
  var fold9: u32;
  var _cy9: u32;
  var p_limbs: u32;
  var d1: u32;
  var bw1: u32;
  var r1: u32;
  var d2: u32;
  var bw2: u32;
  var __ret: u32;
  c_limb = const_u32(c);
  cy4_c = fn_23(cy4, c_limb, c);
  cy4_vec = scalar_to_padded_vec(cy4_c, n);
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(fold5, cy4_vec, n);
    fold6 = __td._0;
    _cy6 = __td._1;
  }
  cy5_c = fn_23(cy5, c_limb, c);
  cy5_vec = scalar_to_padded_vec(cy5_c, n);
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(fold6, cy5_vec, n);
    fold7 = __td._0;
    cy7 = __td._1;
  }
  _cy6_c = fn_23(_cy6, c_limb, c);
  cy7_c = fn_23(cy7, c_limb, c);
  {
    var __td = add3(_cy6_c, cy7_c, zero_val());
    final_c = __td._0;
    final_c_carry = __td._1;
  }
  final_vec = scalar_to_padded_vec(final_c, n);
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(fold7, final_vec, n);
    fold8 = __td._0;
    _cy8 = __td._1;
  }
  cy8_c = fn_23(_cy8, c_limb, c);
  cy8_vec = scalar_to_padded_vec(cy8_c, n);
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(fold8, cy8_vec, n);
    fold9 = __td._0;
    _cy9 = __td._1;
  }
  p_limbs = make_p_limbs(n, c);
  {
    var __td = generic_sub_limbs_scratch_params_scratch(fold9, p_limbs, n);
    d1 = __td._0;
    bw1 = __td._1;
  }
  r1 = generic_select_vec(bw1, d1, fold9, n);
  {
    var __td = generic_sub_limbs_scratch_params_scratch(r1, p_limbs, n);
    d2 = __td._0;
    bw2 = __td._1;
  }
  __ret = generic_select_vec(bw2, d2, r1, n);
  return __ret;
}

fn mersenne_carry_early(fold2: u32, cy2: u32, wide_cy: u32, n: u32, c: u32) -> R3 {
  var c_limb: u32;
  var wcy_c: u32;
  var wcy_vec: u32;
  var fold3: u32;
  var cy3: u32;
  var cy2_c: u32;
  var cy2_vec: u32;
  var fold4: u32;
  var cy4: u32;
  var cy3_c: u32;
  var cy3_vec: u32;
  var fold5: u32;
  var cy5: u32;
  var __ret: R3;
  c_limb = const_u32(c);
  wcy_c = fn_23(wide_cy, c_limb, c);
  wcy_vec = pair_to_padded_vec(zero_val(), wcy_c, n);
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(fold2, wcy_vec, n);
    fold3 = __td._0;
    cy3 = __td._1;
  }
  cy2_c = fn_23(cy2, c_limb, c);
  cy2_vec = scalar_to_padded_vec(cy2_c, n);
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(fold3, cy2_vec, n);
    fold4 = __td._0;
    cy4 = __td._1;
  }
  cy3_c = fn_23(cy3, c_limb, c);
  cy3_vec = scalar_to_padded_vec(cy3_c, n);
  {
    var __td = generic_add_limbs_scratch_scratch_scratch(fold4, cy3_vec, n);
    fold5 = __td._0;
    cy5 = __td._1;
  }
  __ret = R3(fold5, cy4, cy5);
  return __ret;
}

fn mul_add_carry(self_val: u32, b: u32, accum: u32, carry: u32) -> R2 {
  var carry: u32;
  var mul_lo: u32;
  var mul_hi: u32;
  var sum1: u32;
  var c1: u32;
  var sum2: u32;
  var c2: u32;
  var carry_out: u32;
  var __ret: R2;
  {
    var __td = mul2(self_val, b);
    mul_lo = __td._0;
    mul_hi = __td._1;
  }
  sum1 = (mul_lo + accum);
  c1 = select(0u, 1u, (sum1 < mul_lo));
  sum2 = (sum1 + carry);
  c2 = select(0u, 1u, (sum2 < sum1));
  carry_out = ((mul_hi + c1) + c2);
  __ret = R2(sum2, carry_out);
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

fn scalar_to_padded_vec(scalar: u32, n: u32) -> u32 {
  var v: u32;
  var v_len: u32;
  var result: u32;
  var __ret: u32;
  v_len = 0u;
  scratch[(v + v_len)] = scalar;
  v_len = v_len + 1u;
  result = generic_pad_to_length(v, n);
  __ret = result;
  return __ret;
}

fn make_p_limbs(n: u32, c: u32) -> u32 {
  var first: u32;
  var p: u32;
  var p_len: u32;
  var max_limb: u32;
  var i: u32;
  var pushed: u32;
  var __ret: u32;
  first = const_u32(((0u - c) + 1u));
  p_len = 0u;
  scratch[(p + p_len)] = first;
  p_len = p_len + 1u;
  max_limb = const_u32(0u);
  for (var i: u32 = 1u; i < n; i++) {
    pushed = clone_limb(max_limb);
    scratch[(p + p_len)] = pushed;
    p_len = p_len + 1u;
  }
  __ret = p;
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

@compute @workgroup_size(16, 16, 1)
fn mandelbrot_perturb_kernel(
  @builtin(global_invocation_id) gid: vec3<u32>,
) {
  let gid_x = gid.x;
  let gid_y = gid.y;
  var width: u32;
  var max_iters: u32;
  var n: u32;
  var c_val: u32;
  var p_off: u32;
  var tid: u32;
  var scratch_per_thread: u32;
  var sb: u32;
  var dr: u32;
  var di: u32;
  var dc_re_off: u32;
  var dc_im_off: u32;
  var i: u32;
  var escaped_iter: u32;
  var iter: u32;
  var orbit_off: u32;
  var prod1: u32;
  var k1: u32;
  var prod2: u32;
  var k2: u32;
  var k3: u32;
  var k4: u32;
  var zd_re: u32;
  var zd_im: u32;
  var tzd_re: u32;
  var tzd_im: u32;
  var dsq_prod: u32;
  var dr2: u32;
  var dsq_prod2: u32;
  var di2: u32;
  var dsum: u32;
  var dsum2: u32;
  var dsq_re: u32;
  var dsq_im: u32;
  var new_dr: u32;
  var new_di: u32;
  var full_re: u32;
  var full_im: u32;
  var mag_re2: u32;
  var mag_im2: u32;
  var mag2: u32;
  var escape_off: u32;
  var diff_off: u32;
  var borrow: u32;
  width = params[0u];
  max_iters = params[2u];
  n = params[3u];
  c_val = params[4u];
  p_off = 5u;
  tid = ((gid_y * width) + gid_x);
  scratch_per_thread = (20u * n);
  sb = (tid * scratch_per_thread);
  dr = sb;
  di = (sb + n);
  dc_re_off = ((tid * 2u) * n);
  dc_im_off = (dc_re_off + n);
  for (var i: u32 = 0u; i < n; i++) {
    scratch[(dr + i)] = delta_c[(dc_re_off + i)];
    scratch[(di + i)] = delta_c[(dc_im_off + i)];
  }
  escaped_iter = max_iters;
  for (var iter: u32 = 0u; iter < max_iters; iter++) {
    orbit_off = (iter * n);
    prod1 = (sb + (2u * n));
    __call_tmp = generic_mul_karatsuba_scratch_scratch_scratch_d6(orbit_off, dr, n, prod1);
    k1 = (sb + (8u * n));
    __call_tmp = mersenne_reduce_exec_scratch_scratch(prod1, n, c_val, k1);
    prod2 = (sb + (4u * n));
    __call_tmp = generic_mul_karatsuba_scratch_scratch_scratch_d6(orbit_off, di, n, prod2);
    k2 = (sb + (9u * n));
    __call_tmp = mersenne_reduce_exec_scratch_scratch(prod2, n, c_val, k2);
    __call_tmp = generic_mul_karatsuba_scratch_scratch_scratch_d6(orbit_off, di, n, prod1);
    k3 = (sb + (10u * n));
    __call_tmp = mersenne_reduce_exec_scratch_scratch(prod1, n, c_val, k3);
    __call_tmp = generic_mul_karatsuba_scratch_scratch_scratch_d6(orbit_off, dr, n, prod2);
    k4 = (sb + (11u * n));
    __call_tmp = mersenne_reduce_exec_scratch_scratch(prod2, n, c_val, k4);
    zd_re = (sb + (12u * n));
    zd_im = (sb + (13u * n));
    __call_tmp = generic_sub_limbs_scratch_params_scratch(k1, k2, n, zd_re);
    __call_tmp = generic_add_limbs_scratch_scratch_scratch(k3, k4, n, zd_im);
    tzd_re = (sb + (8u * n));
    tzd_im = (sb + (9u * n));
    __call_tmp = generic_add_limbs_scratch_scratch_scratch(zd_re, zd_re, n, tzd_re);
    __call_tmp = generic_add_limbs_scratch_scratch_scratch(zd_im, zd_im, n, tzd_im);
    dsq_prod = (sb + (2u * n));
    __call_tmp = generic_mul_karatsuba_scratch_scratch_scratch_d6(dr, dr, n, dsq_prod);
    dr2 = (sb + (10u * n));
    __call_tmp = mersenne_reduce_exec_scratch_scratch(dsq_prod, n, c_val, dr2);
    dsq_prod2 = (sb + (4u * n));
    __call_tmp = generic_mul_karatsuba_scratch_scratch_scratch_d6(di, di, n, dsq_prod2);
    di2 = (sb + (11u * n));
    __call_tmp = mersenne_reduce_exec_scratch_scratch(dsq_prod2, n, c_val, di2);
    dsum = (sb + (12u * n));
    __call_tmp = generic_add_limbs_scratch_scratch_scratch(dr, di, n, dsum);
    __call_tmp = generic_mul_karatsuba_scratch_scratch_scratch_d6(dsum, dsum, n, dsq_prod);
    dsum2 = (sb + (13u * n));
    __call_tmp = mersenne_reduce_exec_scratch_scratch(dsq_prod, n, c_val, dsum2);
    dsq_re = (sb + (12u * n));
    __call_tmp = generic_sub_limbs_scratch_params_scratch(dr2, di2, n, dsq_re);
    dsq_im = (sb + (13u * n));
    __call_tmp = generic_sub_limbs_scratch_params_scratch(dsum2, dr2, n, dsq_im);
    __call_tmp = generic_sub_limbs_scratch_params_scratch(dsq_im, di2, n, dsq_im);
    new_dr = (sb + (10u * n));
    __call_tmp = generic_add_limbs_scratch_scratch_scratch(tzd_re, dsq_re, n, new_dr);
    __call_tmp = generic_add_limbs_scratch_scratch_scratch(new_dr, dc_re_off, n, new_dr);
    new_di = (sb + (11u * n));
    __call_tmp = generic_add_limbs_scratch_scratch_scratch(tzd_im, dsq_im, n, new_di);
    __call_tmp = generic_add_limbs_scratch_scratch_scratch(new_di, dc_im_off, n, new_di);
    for (var i: u32 = 0u; i < n; i++) {
      scratch[(dr + i)] = scratch[(new_dr + i)];
      scratch[(di + i)] = scratch[(new_di + i)];
    }
    full_re = (sb + (8u * n));
    full_im = (sb + (9u * n));
    __call_tmp = generic_add_limbs_scratch_scratch_scratch(orbit_off, dr, n, full_re);
    __call_tmp = generic_add_limbs_scratch_scratch_scratch(orbit_off, di, n, full_im);
    __call_tmp = generic_mul_karatsuba_scratch_scratch_scratch_d6(full_re, full_re, n, dsq_prod);
    mag_re2 = (sb + (10u * n));
    __call_tmp = mersenne_reduce_exec_scratch_scratch(dsq_prod, n, c_val, mag_re2);
    __call_tmp = generic_mul_karatsuba_scratch_scratch_scratch_d6(full_im, full_im, n, dsq_prod2);
    mag_im2 = (sb + (11u * n));
    __call_tmp = mersenne_reduce_exec_scratch_scratch(dsq_prod2, n, c_val, mag_im2);
    mag2 = (sb + (12u * n));
    __call_tmp = generic_add_limbs_scratch_scratch_scratch(mag_re2, mag_im2, n, mag2);
    escape_off = (p_off + n);
    diff_off = (sb + (13u * n));
    borrow = generic_sub_limbs_scratch_params_scratch(mag2, escape_off, n, diff_off);
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

