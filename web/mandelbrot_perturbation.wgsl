struct R2 {
  f0: u32,
  f1: u32,
}

var<workgroup> wg_mem: array<u32, 8192>;
@group(0) @binding(0) var<storage, read> c_data: array<u32>;
@group(0) @binding(2) var<storage, read_write> iter_counts: array<u32>;
@group(0) @binding(3) var<storage, read> params: array<u32>;

fn signed_mul_to___local_4___local_4___local_4___local_8(a: ptr<function, array<u32, 4>>, a_sign: u32, b: ptr<function, array<u32, 4>>, b_sign: u32, out: ptr<function, array<u32, 4>>, prod: ptr<function, array<u32, 8>>, n: u32, frac_limbs: u32) -> u32 {
  var _call_tmp: u32;
  var sign_b_flipped: u32;
  var _ret: u32;
  _call_tmp = mul_schoolbook_to___local_4___local_4___local_8(a, b, prod, n);
  _call_tmp = slice_vec_to___local_8___local_4(prod, frac_limbs, (frac_limbs + n), out, 0u);
  sign_b_flipped = select_limb(b_sign, const_u32(1u), zero_val());
  _ret = select_limb(a_sign, clone_limb(b_sign), sign_b_flipped);
  return _ret;
}

fn signed_sub_to___local_4___local_4___local_4___local_4___local_4(a: ptr<function, array<u32, 4>>, a_sign: u32, b: ptr<function, array<u32, 4>>, b_sign: u32, out: ptr<function, array<u32, 4>>, tmp1: ptr<function, array<u32, 4>>, tmp2: ptr<function, array<u32, 4>>, n: u32) -> u32 {
  var neg_b_sign: u32;
  var _ret: u32;
  neg_b_sign = select_limb(b_sign, const_u32(1u), zero_val());
  _ret = signed_add_to___local_4___local_4___local_4___local_4___local_4(a, a_sign, b, neg_b_sign, out, tmp1, tmp2, n);
  return _ret;
}

fn signed_add_to___local_4___local_4___local_4___local_4___local_4(a: ptr<function, array<u32, 4>>, a_sign: u32, b: ptr<function, array<u32, 4>>, b_sign: u32, out: ptr<function, array<u32, 4>>, tmp1: ptr<function, array<u32, 4>>, tmp2: ptr<function, array<u32, 4>>, n: u32) -> u32 {
  var _sum_carry: u32;
  var borrow_ab: u32;
  var _borrow_ba: u32;
  var sign_diff: u32;
  var sign_borrow: u32;
  var diff_zero: u32;
  var borrow_zero: u32;
  var same_sign: u32;
  var _unused_17: u32;
  var diff_sign: u32;
  var result_sign: u32;
  var i: u32;
  var diff_val: u32;
  var final_val: u32;
  var _ret: u32;
  _sum_carry = add_limbs_to___local_4___local_4___local_4(a, b, tmp1, n);
  borrow_ab = sub_limbs_to___local_4___local_4___local_4(a, b, tmp2, n);
  _borrow_ba = sub_limbs_to___local_4___local_4___local_4(b, a, out, n);
  {
    var _td = sub_borrow(a_sign, b_sign, zero_val());
    sign_diff = _td.f0;
    sign_borrow = _td.f1;
  }
  diff_zero = is_zero_limb(sign_diff);
  borrow_zero = is_zero_limb(sign_borrow);
  {
    var _td = mul2(diff_zero, borrow_zero);
    same_sign = _td.f0;
    _unused_17 = _td.f1;
  }
  diff_sign = select_limb(borrow_ab, clone_limb(a_sign), clone_limb(b_sign));
  result_sign = select_limb(same_sign, diff_sign, clone_limb(a_sign));
  for (var i: u32 = 0u; i < n; i++) {
    diff_val = select_limb(borrow_ab, clone_limb((*tmp2)[i]), clone_limb((*out)[i]));
    final_val = select_limb(same_sign, diff_val, clone_limb((*tmp1)[i]));
    (*out)[i] = final_val;
  }
  _ret = result_sign;
  return _ret;
}

fn sub_limbs_to___local_4___local_4___local_4(a: ptr<function, array<u32, 4>>, b: ptr<function, array<u32, 4>>, out: ptr<function, array<u32, 4>>, n: u32) -> u32 {
  var borrow: u32;
  var i: u32;
  var digit: u32;
  var next_borrow: u32;
  var _ret: u32;
  borrow = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = sub_borrow((*a)[i], (*b)[i], borrow);
      digit = _td.f0;
      next_borrow = _td.f1;
    }
    (*out)[i] = digit;
    borrow = next_borrow;
  }
  _ret = borrow;
  return _ret;
}

fn add_limbs_to___local_4___local_4___local_4(a: ptr<function, array<u32, 4>>, b: ptr<function, array<u32, 4>>, out: ptr<function, array<u32, 4>>, n: u32) -> u32 {
  var carry: u32;
  var i: u32;
  var digit: u32;
  var next_carry: u32;
  var _ret: u32;
  carry = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = add3((*a)[i], (*b)[i], carry);
      digit = _td.f0;
      next_carry = _td.f1;
    }
    (*out)[i] = digit;
    carry = next_carry;
  }
  _ret = carry;
  return _ret;
}

fn clone_limb(self_val: u32) -> u32 {
  var _ret: u32;
  _ret = self_val;
  return _ret;
}

fn const_u32(c: u32) -> u32 {
  var _ret: u32;
  _ret = c;
  return _ret;
}

fn mul_schoolbook_to___local_4___local_4___local_8(a: ptr<function, array<u32, 4>>, b: ptr<function, array<u32, 4>>, out: ptr<function, array<u32, 8>>, n: u32) -> u32 {
  var nn: u32;
  var i: u32;
  var carry: u32;
  var j: u32;
  var prod_lo: u32;
  var prod_hi: u32;
  var sum1: u32;
  var c1: u32;
  var new_carry: u32;
  var _c2: u32;
  var _ret: u32;
  nn = (2u * n);
  for (var i: u32 = 0u; i < nn; i++) {
    (*out)[i] = zero_val();
  }
  for (var i: u32 = 0u; i < n; i++) {
    carry = zero_val();
    for (var j: u32 = 0u; j < n; j++) {
      {
        var _td = mul2((*a)[j], (*b)[i]);
        prod_lo = _td.f0;
        prod_hi = _td.f1;
      }
      {
        var _td = add3(prod_lo, (*out)[(i + j)], carry);
        sum1 = _td.f0;
        c1 = _td.f1;
      }
      {
        var _td = add3(prod_hi, c1, zero_val());
        new_carry = _td.f0;
        _c2 = _td.f1;
      }
      (*out)[(i + j)] = sum1;
      carry = new_carry;
    }
    (*out)[(i + n)] = carry;
  }
  return _ret;
}

fn slice_vec_to___local_8___local_4(a: ptr<function, array<u32, 8>>, start: u32, end: u32, out: ptr<function, array<u32, 4>>, out_off: u32) -> u32 {
  var len: u32;
  var si: u32;
  var di: u32;
  var idx: u32;
  var _ret: u32;
  len = (end - start);
  si = start;
  di = out_off;
  for (var idx: u32 = 0u; idx < len; idx++) {
    (*out)[di] = clone_limb((*a)[si]);
    si = (si + 1u);
    di = (di + 1u);
  }
  return _ret;
}

fn select_limb(cond: u32, if_zero: u32, if_nonzero: u32) -> u32 {
  var _ret: u32;
  if ((cond == 0u)) {
    _ret = if_zero;
  } else {
    _ret = if_nonzero;
  }
  return _ret;
}

fn zero_val() -> u32 {
  var _ret: u32;
  _ret = 0u;
  return _ret;
}

fn mul2(self_val: u32, b: u32) -> R2 {
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
  var _ret: R2;
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
  _ret = R2(lo, hi);
  return _ret;
}

fn sub_borrow(self_val: u32, b: u32, borrow: u32) -> R2 {
  var ab: u32;
  var bw1: u32;
  var result: u32;
  var bw2: u32;
  var _ret: R2;
  ab = (self_val - b);
  bw1 = select(0u, 1u, (self_val < b));
  result = (ab - borrow);
  bw2 = select(0u, 1u, (ab < borrow));
  _ret = R2(result, (bw1 + bw2));
  return _ret;
}

fn is_zero_limb(self_val: u32) -> u32 {
  var _ret: u32;
  if ((self_val == 0u)) {
    _ret = 1u;
  } else {
    _ret = 0u;
  }
  return _ret;
}

fn add3(self_val: u32, b: u32, carry: u32) -> R2 {
  var ab: u32;
  var c1: u32;
  var abc: u32;
  var c2: u32;
  var _ret: R2;
  ab = (self_val + b);
  c1 = select(0u, 1u, (ab < self_val));
  abc = (ab + carry);
  c2 = select(0u, 1u, (abc < ab));
  _ret = R2(abc, (c1 + c2));
  return _ret;
}

fn signed_mul_to_wg_mem___local_4___local_4___local_8(a: u32, a_sign: u32, b: ptr<function, array<u32, 4>>, b_sign: u32, out: ptr<function, array<u32, 4>>, prod: ptr<function, array<u32, 8>>, n: u32, frac_limbs: u32) -> u32 {
  var _call_tmp: u32;
  var sign_b_flipped: u32;
  var _ret: u32;
  _call_tmp = mul_schoolbook_to_wg_mem___local_4___local_8(a, b, prod, n);
  _call_tmp = slice_vec_to___local_8___local_4(prod, frac_limbs, (frac_limbs + n), out, 0u);
  sign_b_flipped = select_limb(b_sign, const_u32(1u), zero_val());
  _ret = select_limb(a_sign, clone_limb(b_sign), sign_b_flipped);
  return _ret;
}

fn signed_mul_to_wg_mem_wg_mem_wg_mem_wg_mem(a: u32, a_sign: u32, b: u32, b_sign: u32, out: u32, prod: u32, n: u32, frac_limbs: u32) -> u32 {
  var _call_tmp: u32;
  var sign_b_flipped: u32;
  var _ret: u32;
  _call_tmp = mul_schoolbook_to_wg_mem_wg_mem_wg_mem(a, b, prod, n);
  _call_tmp = slice_vec_to_wg_mem_wg_mem(prod, frac_limbs, (frac_limbs + n), out, 0u);
  sign_b_flipped = select_limb(b_sign, const_u32(1u), zero_val());
  _ret = select_limb(a_sign, clone_limb(b_sign), sign_b_flipped);
  return _ret;
}

fn signed_sub_to_c_data_wg_mem___local_4___local_4___local_4(a: u32, a_sign: u32, b: u32, b_sign: u32, out: ptr<function, array<u32, 4>>, tmp1: ptr<function, array<u32, 4>>, tmp2: ptr<function, array<u32, 4>>, n: u32) -> u32 {
  var neg_b_sign: u32;
  var _ret: u32;
  neg_b_sign = select_limb(b_sign, const_u32(1u), zero_val());
  _ret = signed_add_to_c_data_wg_mem___local_4___local_4___local_4(a, a_sign, b, neg_b_sign, out, tmp1, tmp2, n);
  return _ret;
}

fn signed_sub_to_wg_mem_wg_mem_wg_mem_wg_mem_wg_mem(a: u32, a_sign: u32, b: u32, b_sign: u32, out: u32, tmp1: u32, tmp2: u32, n: u32) -> u32 {
  var neg_b_sign: u32;
  var _ret: u32;
  neg_b_sign = select_limb(b_sign, const_u32(1u), zero_val());
  _ret = signed_add_to_wg_mem_wg_mem_wg_mem_wg_mem_wg_mem(a, a_sign, b, neg_b_sign, out, tmp1, tmp2, n);
  return _ret;
}

fn signed_add_to_c_data_wg_mem___local_4___local_4___local_4(a: u32, a_sign: u32, b: u32, b_sign: u32, out: ptr<function, array<u32, 4>>, tmp1: ptr<function, array<u32, 4>>, tmp2: ptr<function, array<u32, 4>>, n: u32) -> u32 {
  var _sum_carry: u32;
  var borrow_ab: u32;
  var _borrow_ba: u32;
  var sign_diff: u32;
  var sign_borrow: u32;
  var diff_zero: u32;
  var borrow_zero: u32;
  var same_sign: u32;
  var _unused_17: u32;
  var diff_sign: u32;
  var result_sign: u32;
  var i: u32;
  var diff_val: u32;
  var final_val: u32;
  var _ret: u32;
  _sum_carry = add_limbs_to_c_data_wg_mem___local_4(a, b, tmp1, n);
  borrow_ab = sub_limbs_to_c_data_wg_mem___local_4(a, b, tmp2, n);
  _borrow_ba = sub_limbs_to_wg_mem_c_data___local_4(b, a, out, n);
  {
    var _td = sub_borrow(a_sign, b_sign, zero_val());
    sign_diff = _td.f0;
    sign_borrow = _td.f1;
  }
  diff_zero = is_zero_limb(sign_diff);
  borrow_zero = is_zero_limb(sign_borrow);
  {
    var _td = mul2(diff_zero, borrow_zero);
    same_sign = _td.f0;
    _unused_17 = _td.f1;
  }
  diff_sign = select_limb(borrow_ab, clone_limb(a_sign), clone_limb(b_sign));
  result_sign = select_limb(same_sign, diff_sign, clone_limb(a_sign));
  for (var i: u32 = 0u; i < n; i++) {
    diff_val = select_limb(borrow_ab, clone_limb((*tmp2)[i]), clone_limb((*out)[i]));
    final_val = select_limb(same_sign, diff_val, clone_limb((*tmp1)[i]));
    (*out)[i] = final_val;
  }
  _ret = result_sign;
  return _ret;
}

fn signed_add_to_wg_mem___local_4___local_4___local_4___local_4(a: u32, a_sign: u32, b: ptr<function, array<u32, 4>>, b_sign: u32, out: ptr<function, array<u32, 4>>, tmp1: ptr<function, array<u32, 4>>, tmp2: ptr<function, array<u32, 4>>, n: u32) -> u32 {
  var _sum_carry: u32;
  var borrow_ab: u32;
  var _borrow_ba: u32;
  var sign_diff: u32;
  var sign_borrow: u32;
  var diff_zero: u32;
  var borrow_zero: u32;
  var same_sign: u32;
  var _unused_17: u32;
  var diff_sign: u32;
  var result_sign: u32;
  var i: u32;
  var diff_val: u32;
  var final_val: u32;
  var _ret: u32;
  _sum_carry = add_limbs_to_wg_mem___local_4___local_4(a, b, tmp1, n);
  borrow_ab = sub_limbs_to_wg_mem___local_4___local_4(a, b, tmp2, n);
  _borrow_ba = sub_limbs_to___local_4_wg_mem___local_4(b, a, out, n);
  {
    var _td = sub_borrow(a_sign, b_sign, zero_val());
    sign_diff = _td.f0;
    sign_borrow = _td.f1;
  }
  diff_zero = is_zero_limb(sign_diff);
  borrow_zero = is_zero_limb(sign_borrow);
  {
    var _td = mul2(diff_zero, borrow_zero);
    same_sign = _td.f0;
    _unused_17 = _td.f1;
  }
  diff_sign = select_limb(borrow_ab, clone_limb(a_sign), clone_limb(b_sign));
  result_sign = select_limb(same_sign, diff_sign, clone_limb(a_sign));
  for (var i: u32 = 0u; i < n; i++) {
    diff_val = select_limb(borrow_ab, clone_limb((*tmp2)[i]), clone_limb((*out)[i]));
    final_val = select_limb(same_sign, diff_val, clone_limb((*tmp1)[i]));
    (*out)[i] = final_val;
  }
  _ret = result_sign;
  return _ret;
}

fn signed_add_to_wg_mem_wg_mem_wg_mem_wg_mem_wg_mem(a: u32, a_sign: u32, b: u32, b_sign: u32, out: u32, tmp1: u32, tmp2: u32, n: u32) -> u32 {
  var _sum_carry: u32;
  var borrow_ab: u32;
  var _borrow_ba: u32;
  var sign_diff: u32;
  var sign_borrow: u32;
  var diff_zero: u32;
  var borrow_zero: u32;
  var same_sign: u32;
  var _unused_17: u32;
  var diff_sign: u32;
  var result_sign: u32;
  var i: u32;
  var diff_val: u32;
  var final_val: u32;
  var _ret: u32;
  _sum_carry = add_limbs_to_wg_mem_wg_mem_wg_mem(a, b, tmp1, n);
  borrow_ab = sub_limbs_to_wg_mem_wg_mem_wg_mem(a, b, tmp2, n);
  _borrow_ba = sub_limbs_to_wg_mem_wg_mem_wg_mem(b, a, out, n);
  {
    var _td = sub_borrow(a_sign, b_sign, zero_val());
    sign_diff = _td.f0;
    sign_borrow = _td.f1;
  }
  diff_zero = is_zero_limb(sign_diff);
  borrow_zero = is_zero_limb(sign_borrow);
  {
    var _td = mul2(diff_zero, borrow_zero);
    same_sign = _td.f0;
    _unused_17 = _td.f1;
  }
  diff_sign = select_limb(borrow_ab, clone_limb(a_sign), clone_limb(b_sign));
  result_sign = select_limb(same_sign, diff_sign, clone_limb(a_sign));
  for (var i: u32 = 0u; i < n; i++) {
    diff_val = select_limb(borrow_ab, clone_limb(wg_mem[(tmp2 + i)]), clone_limb(wg_mem[(out + i)]));
    final_val = select_limb(same_sign, diff_val, clone_limb(wg_mem[(tmp1 + i)]));
    wg_mem[(out + i)] = final_val;
  }
  _ret = result_sign;
  return _ret;
}

fn sub_limbs_to___local_4_params___local_4(a: ptr<function, array<u32, 4>>, b: u32, out: ptr<function, array<u32, 4>>, n: u32) -> u32 {
  var borrow: u32;
  var i: u32;
  var digit: u32;
  var next_borrow: u32;
  var _ret: u32;
  borrow = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = sub_borrow((*a)[i], params[(b + i)], borrow);
      digit = _td.f0;
      next_borrow = _td.f1;
    }
    (*out)[i] = digit;
    borrow = next_borrow;
  }
  _ret = borrow;
  return _ret;
}

fn sub_limbs_to___local_4_wg_mem___local_4(a: ptr<function, array<u32, 4>>, b: u32, out: ptr<function, array<u32, 4>>, n: u32) -> u32 {
  var borrow: u32;
  var i: u32;
  var digit: u32;
  var next_borrow: u32;
  var _ret: u32;
  borrow = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = sub_borrow((*a)[i], wg_mem[(b + i)], borrow);
      digit = _td.f0;
      next_borrow = _td.f1;
    }
    (*out)[i] = digit;
    borrow = next_borrow;
  }
  _ret = borrow;
  return _ret;
}

fn sub_limbs_to_c_data_wg_mem___local_4(a: u32, b: u32, out: ptr<function, array<u32, 4>>, n: u32) -> u32 {
  var borrow: u32;
  var i: u32;
  var digit: u32;
  var next_borrow: u32;
  var _ret: u32;
  borrow = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = sub_borrow(c_data[(a + i)], wg_mem[(b + i)], borrow);
      digit = _td.f0;
      next_borrow = _td.f1;
    }
    (*out)[i] = digit;
    borrow = next_borrow;
  }
  _ret = borrow;
  return _ret;
}

fn sub_limbs_to_wg_mem___local_4___local_4(a: u32, b: ptr<function, array<u32, 4>>, out: ptr<function, array<u32, 4>>, n: u32) -> u32 {
  var borrow: u32;
  var i: u32;
  var digit: u32;
  var next_borrow: u32;
  var _ret: u32;
  borrow = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = sub_borrow(wg_mem[(a + i)], (*b)[i], borrow);
      digit = _td.f0;
      next_borrow = _td.f1;
    }
    (*out)[i] = digit;
    borrow = next_borrow;
  }
  _ret = borrow;
  return _ret;
}

fn sub_limbs_to_wg_mem_c_data___local_4(a: u32, b: u32, out: ptr<function, array<u32, 4>>, n: u32) -> u32 {
  var borrow: u32;
  var i: u32;
  var digit: u32;
  var next_borrow: u32;
  var _ret: u32;
  borrow = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = sub_borrow(wg_mem[(a + i)], c_data[(b + i)], borrow);
      digit = _td.f0;
      next_borrow = _td.f1;
    }
    (*out)[i] = digit;
    borrow = next_borrow;
  }
  _ret = borrow;
  return _ret;
}

fn sub_limbs_to_wg_mem_params_wg_mem(a: u32, b: u32, out: u32, n: u32) -> u32 {
  var borrow: u32;
  var i: u32;
  var digit: u32;
  var next_borrow: u32;
  var _ret: u32;
  borrow = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = sub_borrow(wg_mem[(a + i)], params[(b + i)], borrow);
      digit = _td.f0;
      next_borrow = _td.f1;
    }
    wg_mem[(out + i)] = digit;
    borrow = next_borrow;
  }
  _ret = borrow;
  return _ret;
}

fn sub_limbs_to_wg_mem_wg_mem_wg_mem(a: u32, b: u32, out: u32, n: u32) -> u32 {
  var borrow: u32;
  var i: u32;
  var digit: u32;
  var next_borrow: u32;
  var _ret: u32;
  borrow = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = sub_borrow(wg_mem[(a + i)], wg_mem[(b + i)], borrow);
      digit = _td.f0;
      next_borrow = _td.f1;
    }
    wg_mem[(out + i)] = digit;
    borrow = next_borrow;
  }
  _ret = borrow;
  return _ret;
}

fn add_limbs_to_c_data_wg_mem___local_4(a: u32, b: u32, out: ptr<function, array<u32, 4>>, n: u32) -> u32 {
  var carry: u32;
  var i: u32;
  var digit: u32;
  var next_carry: u32;
  var _ret: u32;
  carry = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = add3(c_data[(a + i)], wg_mem[(b + i)], carry);
      digit = _td.f0;
      next_carry = _td.f1;
    }
    (*out)[i] = digit;
    carry = next_carry;
  }
  _ret = carry;
  return _ret;
}

fn add_limbs_to_wg_mem___local_4___local_4(a: u32, b: ptr<function, array<u32, 4>>, out: ptr<function, array<u32, 4>>, n: u32) -> u32 {
  var carry: u32;
  var i: u32;
  var digit: u32;
  var next_carry: u32;
  var _ret: u32;
  carry = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = add3(wg_mem[(a + i)], (*b)[i], carry);
      digit = _td.f0;
      next_carry = _td.f1;
    }
    (*out)[i] = digit;
    carry = next_carry;
  }
  _ret = carry;
  return _ret;
}

fn add_limbs_to_wg_mem_wg_mem_wg_mem(a: u32, b: u32, out: u32, n: u32) -> u32 {
  var carry: u32;
  var i: u32;
  var digit: u32;
  var next_carry: u32;
  var _ret: u32;
  carry = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = add3(wg_mem[(a + i)], wg_mem[(b + i)], carry);
      digit = _td.f0;
      next_carry = _td.f1;
    }
    wg_mem[(out + i)] = digit;
    carry = next_carry;
  }
  _ret = carry;
  return _ret;
}

fn mul_schoolbook_to_wg_mem___local_4___local_8(a: u32, b: ptr<function, array<u32, 4>>, out: ptr<function, array<u32, 8>>, n: u32) -> u32 {
  var nn: u32;
  var i: u32;
  var carry: u32;
  var j: u32;
  var prod_lo: u32;
  var prod_hi: u32;
  var sum1: u32;
  var c1: u32;
  var new_carry: u32;
  var _c2: u32;
  var _ret: u32;
  nn = (2u * n);
  for (var i: u32 = 0u; i < nn; i++) {
    (*out)[i] = zero_val();
  }
  for (var i: u32 = 0u; i < n; i++) {
    carry = zero_val();
    for (var j: u32 = 0u; j < n; j++) {
      {
        var _td = mul2(wg_mem[(a + j)], (*b)[i]);
        prod_lo = _td.f0;
        prod_hi = _td.f1;
      }
      {
        var _td = add3(prod_lo, (*out)[(i + j)], carry);
        sum1 = _td.f0;
        c1 = _td.f1;
      }
      {
        var _td = add3(prod_hi, c1, zero_val());
        new_carry = _td.f0;
        _c2 = _td.f1;
      }
      (*out)[(i + j)] = sum1;
      carry = new_carry;
    }
    (*out)[(i + n)] = carry;
  }
  return _ret;
}

fn mul_schoolbook_to_wg_mem_wg_mem_wg_mem(a: u32, b: u32, out: u32, n: u32) -> u32 {
  var nn: u32;
  var i: u32;
  var carry: u32;
  var j: u32;
  var prod_lo: u32;
  var prod_hi: u32;
  var sum1: u32;
  var c1: u32;
  var new_carry: u32;
  var _c2: u32;
  var _ret: u32;
  nn = (2u * n);
  for (var i: u32 = 0u; i < nn; i++) {
    wg_mem[(out + i)] = zero_val();
  }
  for (var i: u32 = 0u; i < n; i++) {
    carry = zero_val();
    for (var j: u32 = 0u; j < n; j++) {
      {
        var _td = mul2(wg_mem[(a + j)], wg_mem[(b + i)]);
        prod_lo = _td.f0;
        prod_hi = _td.f1;
      }
      {
        var _td = add3(prod_lo, wg_mem[(out + (i + j))], carry);
        sum1 = _td.f0;
        c1 = _td.f1;
      }
      {
        var _td = add3(prod_hi, c1, zero_val());
        new_carry = _td.f0;
        _c2 = _td.f1;
      }
      wg_mem[(out + (i + j))] = sum1;
      carry = new_carry;
    }
    wg_mem[(out + (i + n))] = carry;
  }
  return _ret;
}

fn slice_vec_to_wg_mem_wg_mem(a: u32, start: u32, end: u32, out: u32, out_off: u32) -> u32 {
  var len: u32;
  var si: u32;
  var di: u32;
  var idx: u32;
  var _ret: u32;
  len = (end - start);
  si = start;
  di = out_off;
  for (var idx: u32 = 0u; idx < len; idx++) {
    wg_mem[(out + di)] = clone_limb(wg_mem[(a + si)]);
    si = (si + 1u);
    di = (di + 1u);
  }
  return _ret;
}

@compute @workgroup_size(16, 16, 1)
fn mandelbrot_perturbation(
  @builtin(global_invocation_id) gid: vec3<u32>,
  @builtin(local_invocation_id) lid: vec3<u32>,
) {
  let gid_x = gid.x;
  let gid_y = gid.y;
  let lid_x = lid.x;
  let lid_y = lid.y;
  var width: u32;
  var height: u32;
  var max_iters: u32;
  var n: u32;
  var frac_limbs: u32;
  var tid: u32;
  var local_id: u32;
  var z_stride: u32;
  var orbit_base: u32;
  var ref_c_base: u32;
  var t0_tmp_base: u32;
  var t0_re2: u32;
  var t0_im2: u32;
  var t0_rpi: u32;
  var t0_sum2: u32;
  var t0_diff: u32;
  var t0_prod: u32;
  var t0_stmp1: u32;
  var t0_stmp2: u32;
  var t0_stmp3: u32;
  var ref_escape_addr: u32;
  var vote_base: u32;
  var glitch_count_addr: u32;
  var best_ref_addr: u32;
  var c_stride_px: u32;
  var c_re_off: u32;
  var c_re_sign_off: u32;
  var c_im_off: u32;
  var c_im_sign_off: u32;
  var delta_re: array<u32, 4>;
  var delta_re_sign: u32;
  var delta_im: array<u32, 4>;
  var delta_im_sign: u32;
  var dc_re: array<u32, 4>;
  var dc_re_sign: u32;
  var dc_im: array<u32, 4>;
  var dc_im_sign: u32;
  var t1: array<u32, 4>;
  var t2: array<u32, 4>;
  var t3: array<u32, 4>;
  var t4: array<u32, 4>;
  var t5: array<u32, 4>;
  var lprod: array<u32, 8>;
  var ls1: array<u32, 4>;
  var ls2: array<u32, 4>;
  var escaped_iter: u32;
  var is_glitched: u32;
  var glitch_iter: u32;
  var max_rounds: u32;
  var round: u32;
  var ref_x: u32;
  var ref_y: u32;
  var ref_x_c: u32;
  var ref_y_c: u32;
  var ref_tid_init: u32;
  var ref_c_off: u32;
  var i: u32;
  var z0_off: u32;
  var ref_escaped: u32;
  var iter: u32;
  var zk: u32;
  var zk_re: u32;
  var zk_re_sign: u32;
  var zk_im: u32;
  var zk_im_sign: u32;
  var re2_s: u32;
  var im2_s: u32;
  var rpi_s: u32;
  var sum2_s: u32;
  var zn: u32;
  var diff_s: u32;
  var new_re_s: u32;
  var t1_s: u32;
  var t2_s: u32;
  var new_im_s: u32;
  var _call_tmp: u32;
  var thresh_off: u32;
  var esc_borrow: u32;
  var zn_re: u32;
  var zn_re_sign: u32;
  var zn_im: u32;
  var zn_im_sign: u32;
  var s1: u32;
  var s2: u32;
  var s3: u32;
  var s4: u32;
  var d1_s: u32;
  var tzd_re_s: u32;
  var d2_s: u32;
  var tzd_im_s: u32;
  var drs_s: u32;
  var dis_s: u32;
  var dri_s: u32;
  var dri2_s: u32;
  var dsq_re_s: u32;
  var q1_s: u32;
  var dsq_im_s: u32;
  var p1_s: u32;
  var new_dr_s: u32;
  var p2_s: u32;
  var new_di_s: u32;
  var full_re_s: u32;
  var full_im_s: u32;
  var fr2_s: u32;
  var fi2_s: u32;
  var borrow: u32;
  var best_vote: u32;
  var best_idx: u32;
  var g_count: u32;
  var best_gx: u32;
  var best_gy: u32;
  var best_tid: u32;
  var best_c_off: u32;
  var alpha: u32;
  var t_col: u32;
  var r: u32;
  var g: u32;
  var b: u32;
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
  local_id = ((lid_y * 16u) + lid_x);
  z_stride = ((2u * n) + 2u);
  orbit_base = 0u;
  ref_c_base = ((max_iters + 1u) * z_stride);
  t0_tmp_base = (ref_c_base + z_stride);
  t0_re2 = t0_tmp_base;
  t0_im2 = (t0_re2 + n);
  t0_rpi = (t0_im2 + n);
  t0_sum2 = (t0_rpi + n);
  t0_diff = (t0_sum2 + n);
  t0_prod = (t0_diff + n);
  t0_stmp1 = (t0_prod + (2u * n));
  t0_stmp2 = (t0_stmp1 + n);
  t0_stmp3 = (t0_stmp2 + n);
  ref_escape_addr = (t0_stmp3 + n);
  vote_base = (ref_escape_addr + 1u);
  glitch_count_addr = (vote_base + 256u);
  best_ref_addr = (glitch_count_addr + 1u);
  c_stride_px = ((2u * n) + 2u);
  c_re_off = (tid * c_stride_px);
  c_re_sign_off = (c_re_off + n);
  c_im_off = (c_re_sign_off + 1u);
  c_im_sign_off = (c_im_off + n);
  escaped_iter = max_iters;
  is_glitched = 1u;
  glitch_iter = 0u;
  max_rounds = 5u;
  for (var round: u32 = 0u; round < max_rounds; round++) {
    if ((local_id == 0u)) {
      if ((round == 0u)) {
        ref_x = ((gid_x - lid_x) + 8u);
        ref_y = ((gid_y - lid_y) + 8u);
        ref_x_c = select(ref_x, (width - 1u), (ref_x >= width));
        ref_y_c = select(ref_y, (height - 1u), (ref_y >= height));
        ref_tid_init = ((ref_y_c * width) + ref_x_c);
        ref_c_off = (ref_tid_init * c_stride_px);
        for (var i: u32 = 0u; i < n; i++) {
          wg_mem[(ref_c_base + i)] = c_data[(ref_c_off + i)];
        }
        wg_mem[(ref_c_base + n)] = c_data[(ref_c_off + n)];
        for (var i: u32 = 0u; i < n; i++) {
          wg_mem[(((ref_c_base + n) + 1u) + i)] = c_data[(((ref_c_off + n) + 1u) + i)];
        }
        wg_mem[((ref_c_base + (2u * n)) + 1u)] = c_data[((ref_c_off + (2u * n)) + 1u)];
      } else {
      }
      z0_off = orbit_base;
      for (var i: u32 = 0u; i < n; i++) {
        wg_mem[(z0_off + i)] = 0u;
      }
      wg_mem[(z0_off + n)] = 0u;
      for (var i: u32 = 0u; i < n; i++) {
        wg_mem[(((z0_off + n) + 1u) + i)] = 0u;
      }
      wg_mem[((z0_off + (2u * n)) + 1u)] = 0u;
      ref_escaped = max_iters;
      for (var iter: u32 = 0u; iter < max_iters; iter++) {
        zk = (orbit_base + (iter * z_stride));
        zk_re = zk;
        zk_re_sign = (zk + n);
        zk_im = ((zk + n) + 1u);
        zk_im_sign = ((zk + (2u * n)) + 1u);
        re2_s = signed_mul_to_wg_mem_wg_mem_wg_mem_wg_mem(zk_re, wg_mem[zk_re_sign], zk_re, wg_mem[zk_re_sign], t0_re2, t0_prod, n, frac_limbs);
        im2_s = signed_mul_to_wg_mem_wg_mem_wg_mem_wg_mem(zk_im, wg_mem[zk_im_sign], zk_im, wg_mem[zk_im_sign], t0_im2, t0_prod, n, frac_limbs);
        rpi_s = signed_add_to_wg_mem_wg_mem_wg_mem_wg_mem_wg_mem(zk_re, wg_mem[zk_re_sign], zk_im, wg_mem[zk_im_sign], t0_rpi, t0_stmp1, t0_stmp2, n);
        sum2_s = signed_mul_to_wg_mem_wg_mem_wg_mem_wg_mem(t0_rpi, rpi_s, t0_rpi, rpi_s, t0_sum2, t0_prod, n, frac_limbs);
        zn = (orbit_base + ((iter + 1u) * z_stride));
        diff_s = signed_sub_to_wg_mem_wg_mem_wg_mem_wg_mem_wg_mem(t0_re2, re2_s, t0_im2, im2_s, t0_diff, t0_stmp1, t0_stmp2, n);
        new_re_s = signed_add_to_wg_mem_wg_mem_wg_mem_wg_mem_wg_mem(t0_diff, diff_s, ref_c_base, wg_mem[(ref_c_base + n)], zn, t0_stmp1, t0_stmp2, n);
        wg_mem[(zn + n)] = new_re_s;
        t1_s = signed_sub_to_wg_mem_wg_mem_wg_mem_wg_mem_wg_mem(t0_sum2, sum2_s, t0_re2, re2_s, t0_diff, t0_stmp1, t0_stmp2, n);
        t2_s = signed_sub_to_wg_mem_wg_mem_wg_mem_wg_mem_wg_mem(t0_diff, t1_s, t0_im2, im2_s, t0_stmp3, t0_stmp1, t0_stmp2, n);
        new_im_s = signed_add_to_wg_mem_wg_mem_wg_mem_wg_mem_wg_mem(t0_stmp3, t2_s, ((ref_c_base + n) + 1u), wg_mem[((ref_c_base + (2u * n)) + 1u)], ((zn + n) + 1u), t0_stmp1, t0_stmp2, n);
        wg_mem[((zn + (2u * n)) + 1u)] = new_im_s;
        if ((ref_escaped == max_iters)) {
          _call_tmp = add_limbs_to_wg_mem_wg_mem_wg_mem(t0_re2, t0_im2, t0_diff, n);
          thresh_off = 5u;
          esc_borrow = sub_limbs_to_wg_mem_params_wg_mem(t0_diff, thresh_off, t0_stmp1, n);
          if ((esc_borrow == 0u)) {
            ref_escaped = (iter + 1u);
          } else {
          }
        } else {
        }
      }
      wg_mem[ref_escape_addr] = ref_escaped;
    } else {
    }
    workgroupBarrier();
    if (((is_glitched == 1u) && (escaped_iter == max_iters))) {
      dc_re_sign = signed_sub_to_c_data_wg_mem___local_4___local_4___local_4(c_re_off, c_data[c_re_sign_off], ref_c_base, wg_mem[(ref_c_base + n)], &dc_re, &ls1, &ls2, n);
      dc_im_sign = signed_sub_to_c_data_wg_mem___local_4___local_4___local_4(c_im_off, c_data[c_im_sign_off], ((ref_c_base + n) + 1u), wg_mem[((ref_c_base + (2u * n)) + 1u)], &dc_im, &ls1, &ls2, n);
      for (var i: u32 = 0u; i < n; i++) {
        delta_re[i] = 0u;
        delta_im[i] = 0u;
      }
      delta_re_sign = 0u;
      delta_im_sign = 0u;
      is_glitched = 0u;
      ref_escaped = wg_mem[ref_escape_addr];
      for (var iter: u32 = 0u; iter < max_iters; iter++) {
        if ((iter >= ref_escaped)) {
          break;
        } else {
        }
        zn = (orbit_base + (iter * z_stride));
        zn_re = zn;
        zn_re_sign = (zn + n);
        zn_im = ((zn + n) + 1u);
        zn_im_sign = ((zn + (2u * n)) + 1u);
        s1 = signed_mul_to_wg_mem___local_4___local_4___local_8(zn_re, wg_mem[zn_re_sign], &delta_re, delta_re_sign, &t1, &lprod, n, frac_limbs);
        s2 = signed_mul_to_wg_mem___local_4___local_4___local_8(zn_im, wg_mem[zn_im_sign], &delta_im, delta_im_sign, &t2, &lprod, n, frac_limbs);
        s3 = signed_mul_to_wg_mem___local_4___local_4___local_8(zn_re, wg_mem[zn_re_sign], &delta_im, delta_im_sign, &t3, &lprod, n, frac_limbs);
        s4 = signed_mul_to_wg_mem___local_4___local_4___local_8(zn_im, wg_mem[zn_im_sign], &delta_re, delta_re_sign, &t4, &lprod, n, frac_limbs);
        d1_s = signed_sub_to___local_4___local_4___local_4___local_4___local_4(&t1, s1, &t2, s2, &t5, &ls1, &ls2, n);
        tzd_re_s = signed_add_to___local_4___local_4___local_4___local_4___local_4(&t5, d1_s, &t5, d1_s, &t1, &ls1, &ls2, n);
        d2_s = signed_add_to___local_4___local_4___local_4___local_4___local_4(&t3, s3, &t4, s4, &t5, &ls1, &ls2, n);
        tzd_im_s = signed_add_to___local_4___local_4___local_4___local_4___local_4(&t5, d2_s, &t5, d2_s, &t2, &ls1, &ls2, n);
        drs_s = signed_mul_to___local_4___local_4___local_4___local_8(&delta_re, delta_re_sign, &delta_re, delta_re_sign, &t3, &lprod, n, frac_limbs);
        dis_s = signed_mul_to___local_4___local_4___local_4___local_8(&delta_im, delta_im_sign, &delta_im, delta_im_sign, &t4, &lprod, n, frac_limbs);
        dri_s = signed_add_to___local_4___local_4___local_4___local_4___local_4(&delta_re, delta_re_sign, &delta_im, delta_im_sign, &t5, &ls1, &ls2, n);
        dri2_s = signed_mul_to___local_4___local_4___local_4___local_8(&t5, dri_s, &t5, dri_s, &ls1, &lprod, n, frac_limbs);
        dsq_re_s = signed_sub_to___local_4___local_4___local_4___local_4___local_4(&t3, drs_s, &t4, dis_s, &t5, &delta_re, &delta_im, n);
        q1_s = signed_sub_to___local_4___local_4___local_4___local_4___local_4(&ls1, dri2_s, &t3, drs_s, &delta_re, &ls2, &delta_im, n);
        dsq_im_s = signed_sub_to___local_4___local_4___local_4___local_4___local_4(&delta_re, q1_s, &t4, dis_s, &t3, &ls2, &delta_im, n);
        p1_s = signed_add_to___local_4___local_4___local_4___local_4___local_4(&t1, tzd_re_s, &t5, dsq_re_s, &t4, &ls1, &ls2, n);
        new_dr_s = signed_add_to___local_4___local_4___local_4___local_4___local_4(&t4, p1_s, &dc_re, dc_re_sign, &delta_re, &ls1, &ls2, n);
        delta_re_sign = new_dr_s;
        p2_s = signed_add_to___local_4___local_4___local_4___local_4___local_4(&t2, tzd_im_s, &t3, dsq_im_s, &t4, &ls1, &ls2, n);
        new_di_s = signed_add_to___local_4___local_4___local_4___local_4___local_4(&t4, p2_s, &dc_im, dc_im_sign, &delta_im, &ls1, &ls2, n);
        delta_im_sign = new_di_s;
        if (((delta_re[(n - 1u)] > 3u) || (delta_im[(n - 1u)] > 3u))) {
          is_glitched = 1u;
          glitch_iter = iter;
          break;
        } else {
        }
        full_re_s = signed_add_to_wg_mem___local_4___local_4___local_4___local_4(zn_re, wg_mem[zn_re_sign], &delta_re, delta_re_sign, &t1, &ls1, &ls2, n);
        full_im_s = signed_add_to_wg_mem___local_4___local_4___local_4___local_4(zn_im, wg_mem[zn_im_sign], &delta_im, delta_im_sign, &t2, &ls1, &ls2, n);
        fr2_s = signed_mul_to___local_4___local_4___local_4___local_8(&t1, full_re_s, &t1, full_re_s, &t3, &lprod, n, frac_limbs);
        fi2_s = signed_mul_to___local_4___local_4___local_4___local_8(&t2, full_im_s, &t2, full_im_s, &t4, &lprod, n, frac_limbs);
        _call_tmp = add_limbs_to___local_4___local_4___local_4(&t3, &t4, &t5, n);
        thresh_off = 5u;
        borrow = sub_limbs_to___local_4_params___local_4(&t5, thresh_off, &t1, n);
        if ((borrow == 0u)) {
          if ((escaped_iter == max_iters)) {
            escaped_iter = iter;
          } else {
          }
        } else {
        }
      }
    } else {
    }
    workgroupBarrier();
    if (((is_glitched == 1u) && (escaped_iter == max_iters))) {
      wg_mem[(vote_base + local_id)] = (glitch_iter + 1u);
    } else {
      wg_mem[(vote_base + local_id)] = 0u;
    }
    workgroupBarrier();
    if ((local_id == 0u)) {
      best_vote = 0u;
      best_idx = 0u;
      g_count = 0u;
      for (var i: u32 = 0u; i < 256u; i++) {
        if ((wg_mem[(vote_base + i)] > best_vote)) {
          best_vote = wg_mem[(vote_base + i)];
          best_idx = i;
        } else {
        }
        if ((wg_mem[(vote_base + i)] > 0u)) {
          g_count = (g_count + 1u);
        } else {
        }
      }
      wg_mem[glitch_count_addr] = g_count;
      wg_mem[best_ref_addr] = best_idx;
      if ((g_count > 0u)) {
        best_gx = ((gid_x - lid_x) + (best_idx % 16u));
        best_gy = ((gid_y - lid_y) + (best_idx / 16u));
        best_tid = ((best_gy * width) + best_gx);
        best_c_off = (best_tid * c_stride_px);
        for (var i: u32 = 0u; i < n; i++) {
          wg_mem[(ref_c_base + i)] = c_data[(best_c_off + i)];
        }
        wg_mem[(ref_c_base + n)] = c_data[(best_c_off + n)];
        for (var i: u32 = 0u; i < n; i++) {
          wg_mem[(((ref_c_base + n) + 1u) + i)] = c_data[(((best_c_off + n) + 1u) + i)];
        }
        wg_mem[((ref_c_base + (2u * n)) + 1u)] = c_data[((best_c_off + (2u * n)) + 1u)];
      } else {
      }
    } else {
    }
    workgroupBarrier();
    if ((wg_mem[glitch_count_addr] == 0u)) {
      break;
    } else {
    }
  }
  alpha = 4278190080u;
  if ((escaped_iter >= max_iters)) {
    iter_counts[tid] = alpha;
  } else {
    t_col = ((escaped_iter * 255u) / max_iters);
    r = t_col;
    g = (t_col / 3u);
    b = (255u - (t_col / 2u));
    iter_counts[tid] = (((alpha | (b << 16u)) | (g << 8u)) | r);
  }
}

