struct R2 {
  _0: u32,
  _1: u32,
}

@group(0) @binding(0) var<storage, read> c_data: array<u32>;
@group(0) @binding(1) var<storage, read_write> scratch: array<u32>;
@group(0) @binding(2) var<storage, read_write> iter_counts: array<u32>;
@group(0) @binding(3) var<storage, read> params: array<u32>;

fn slice_vec_to_scratch_scratch(a: u32, start: u32, end: u32, out: u32, out_off: u32) -> u32 {
  var len: u32;
  var si: u32;
  var di: u32;
  var idx: u32;
  var _ret: u32;
  len = (end - start);
  si = start;
  di = out_off;
  for (var idx: u32 = 0u; idx < len; idx++) {
    scratch[(out + di)] = clone_limb(scratch[(a + si)]);
    si = (si + 1u);
    di = (di + 1u);
  }
  return _ret;
}

fn sub_limbs_to_scratch_params_scratch(a: u32, b: u32, out: u32, n: u32) -> u32 {
  var borrow: u32;
  var i: u32;
  var digit: u32;
  var next_borrow: u32;
  var _ret: u32;
  borrow = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = sub_borrow(scratch[(a + i)], params[(b + i)], borrow);
      digit = _td._0;
      next_borrow = _td._1;
    }
    scratch[(out + i)] = digit;
    borrow = next_borrow;
  }
  _ret = borrow;
  return _ret;
}

fn mul_schoolbook_to_scratch_scratch_scratch(a: u32, b: u32, out: u32, n: u32) -> u32 {
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
    scratch[(out + i)] = zero_val();
  }
  for (var i: u32 = 0u; i < n; i++) {
    carry = zero_val();
    for (var j: u32 = 0u; j < n; j++) {
      {
        var _td = mul2(scratch[(a + j)], scratch[(b + i)]);
        prod_lo = _td._0;
        prod_hi = _td._1;
      }
      {
        var _td = add3(prod_lo, scratch[(out + (i + j))], carry);
        sum1 = _td._0;
        c1 = _td._1;
      }
      {
        var _td = add3(prod_hi, c1, zero_val());
        new_carry = _td._0;
        _c2 = _td._1;
      }
      scratch[(out + (i + j))] = sum1;
      carry = new_carry;
    }
    scratch[(out + (i + n))] = carry;
  }
  return _ret;
}

fn add_limbs_to_scratch_c_data_scratch(a: u32, b: u32, out: u32, n: u32) -> u32 {
  var carry: u32;
  var i: u32;
  var digit: u32;
  var next_carry: u32;
  var _ret: u32;
  carry = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = add3(scratch[(a + i)], c_data[(b + i)], carry);
      digit = _td._0;
      next_carry = _td._1;
    }
    scratch[(out + i)] = digit;
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

fn zero_val() -> u32 {
  var _ret: u32;
  _ret = 0u;
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

fn sub_limbs_to_scratch_scratch_scratch(a: u32, b: u32, out: u32, n: u32) -> u32 {
  var borrow: u32;
  var i: u32;
  var digit: u32;
  var next_borrow: u32;
  var _ret: u32;
  borrow = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = sub_borrow(scratch[(a + i)], scratch[(b + i)], borrow);
      digit = _td._0;
      next_borrow = _td._1;
    }
    scratch[(out + i)] = digit;
    borrow = next_borrow;
  }
  _ret = borrow;
  return _ret;
}

fn add_limbs_to_scratch_scratch_scratch(a: u32, b: u32, out: u32, n: u32) -> u32 {
  var carry: u32;
  var i: u32;
  var digit: u32;
  var next_carry: u32;
  var _ret: u32;
  carry = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = add3(scratch[(a + i)], scratch[(b + i)], carry);
      digit = _td._0;
      next_carry = _td._1;
    }
    scratch[(out + i)] = digit;
    carry = next_carry;
  }
  _ret = carry;
  return _ret;
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
  var words_per_thread: u32;
  var sb: u32;
  var s0: u32;
  var s1: u32;
  var s2: u32;
  var s4: u32;
  var s5: u32;
  var s6: u32;
  var s7: u32;
  var s8: u32;
  var s9: u32;
  var s10: u32;
  var c_re: u32;
  var c_im: u32;
  var i: u32;
  var escaped_iter: u32;
  var iter: u32;
  var _call_tmp: u32;
  var thresh_off: u32;
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
  words_per_thread = (12u * n);
  sb = (tid * words_per_thread);
  s0 = sb;
  s1 = (sb + n);
  s2 = (sb + (2u * n));
  s4 = (sb + (4u * n));
  s5 = (sb + (5u * n));
  s6 = (sb + (6u * n));
  s7 = (sb + (7u * n));
  s8 = (sb + (8u * n));
  s9 = (sb + (9u * n));
  s10 = (sb + (10u * n));
  c_re = ((tid * 2u) * n);
  c_im = (c_re + n);
  for (var i: u32 = 0u; i < n; i++) {
    scratch[(s0 + i)] = 0u;
    scratch[(s1 + i)] = 0u;
  }
  escaped_iter = max_iters;
  for (var iter: u32 = 0u; iter < max_iters; iter++) {
    _call_tmp = mul_schoolbook_to_scratch_scratch_scratch(s0, s0, s2, n);
    _call_tmp = slice_vec_to_scratch_scratch(s2, frac_limbs, (frac_limbs + n), s4, 0u);
    _call_tmp = mul_schoolbook_to_scratch_scratch_scratch(s1, s1, s2, n);
    _call_tmp = slice_vec_to_scratch_scratch(s2, frac_limbs, (frac_limbs + n), s5, 0u);
    _call_tmp = add_limbs_to_scratch_c_data_scratch(s0, s1, s7, n);
    _call_tmp = mul_schoolbook_to_scratch_scratch_scratch(s7, s7, s2, n);
    _call_tmp = slice_vec_to_scratch_scratch(s2, frac_limbs, (frac_limbs + n), s6, 0u);
    _call_tmp = sub_limbs_to_scratch_params_scratch(s4, s5, s9, n);
    _call_tmp = add_limbs_to_scratch_c_data_scratch(s9, c_re, s9, n);
    _call_tmp = sub_limbs_to_scratch_params_scratch(s6, s4, s10, n);
    _call_tmp = sub_limbs_to_scratch_params_scratch(s10, s5, s10, n);
    _call_tmp = add_limbs_to_scratch_c_data_scratch(s10, c_im, s10, n);
    for (var i: u32 = 0u; i < n; i++) {
      scratch[(s0 + i)] = scratch[(s9 + i)];
      scratch[(s1 + i)] = scratch[(s10 + i)];
    }
    _call_tmp = mul_schoolbook_to_scratch_scratch_scratch(s0, s0, s2, n);
    _call_tmp = slice_vec_to_scratch_scratch(s2, frac_limbs, (frac_limbs + n), s4, 0u);
    _call_tmp = mul_schoolbook_to_scratch_scratch_scratch(s1, s1, s2, n);
    _call_tmp = slice_vec_to_scratch_scratch(s2, frac_limbs, (frac_limbs + n), s5, 0u);
    _call_tmp = add_limbs_to_scratch_c_data_scratch(s4, s5, s8, n);
    thresh_off = 5u;
    borrow = sub_limbs_to_scratch_params_scratch(s8, thresh_off, s9, n);
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

