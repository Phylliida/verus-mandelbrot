struct R2 {
  f0: u32,
  f1: u32,
}

@group(0) @binding(0) var<storage, read> c_data: array<u32>;
@group(0) @binding(1) var<storage, read_write> scratch: array<u32>;
@group(0) @binding(2) var<storage, read_write> iter_counts: array<u32>;
@group(0) @binding(3) var<storage, read> params: array<u32>;

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
      digit = _td.f0;
      next_carry = _td.f1;
    }
    scratch[(out + i)] = digit;
    carry = next_carry;
  }
  _ret = carry;
  return _ret;
}

fn signed_sub_to_scratch_scratch_scratch_scratch_scratch(a: u32, a_sign: u32, b: u32, b_sign: u32, out: u32, tmp1: u32, tmp2: u32, n: u32) -> u32 {
  var neg_b_sign: u32;
  var _ret: u32;
  neg_b_sign = select_limb(b_sign, const_u32(1u), zero_val());
  _ret = signed_add_to_scratch_scratch_scratch_scratch_scratch(a, a_sign, b, neg_b_sign, out, tmp1, tmp2, n);
  return _ret;
}

fn sub_limbs_to_c_data_scratch_scratch(a: u32, b: u32, out: u32, n: u32) -> u32 {
  var borrow: u32;
  var i: u32;
  var digit: u32;
  var next_borrow: u32;
  var _ret: u32;
  borrow = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = sub_borrow(c_data[(a + i)], scratch[(b + i)], borrow);
      digit = _td.f0;
      next_borrow = _td.f1;
    }
    scratch[(out + i)] = digit;
    borrow = next_borrow;
  }
  _ret = borrow;
  return _ret;
}

fn signed_mul_to_scratch_scratch_scratch_scratch(a: u32, a_sign: u32, b: u32, b_sign: u32, out: u32, prod: u32, n: u32, frac_limbs: u32) -> u32 {
  var _call_tmp: u32;
  var sign_b_flipped: u32;
  var _ret: u32;
  _call_tmp = mul_schoolbook_to_scratch_scratch_scratch(a, b, prod, n);
  _call_tmp = slice_vec_to_scratch_scratch(prod, frac_limbs, (frac_limbs + n), out, 0u);
  sign_b_flipped = select_limb(b_sign, const_u32(1u), zero_val());
  _ret = select_limb(a_sign, clone_limb(b_sign), sign_b_flipped);
  return _ret;
}

fn signed_add_to_scratch_c_data_scratch_scratch_scratch(a: u32, a_sign: u32, b: u32, b_sign: u32, out: u32, tmp1: u32, tmp2: u32, n: u32) -> u32 {
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
  _sum_carry = add_limbs_to_scratch_c_data_scratch(a, b, tmp1, n);
  borrow_ab = sub_limbs_to_scratch_c_data_scratch(a, b, tmp2, n);
  _borrow_ba = sub_limbs_to_c_data_scratch_scratch(b, a, out, n);
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
    diff_val = select_limb(borrow_ab, clone_limb(scratch[(tmp2 + i)]), clone_limb(scratch[(out + i)]));
    final_val = select_limb(same_sign, diff_val, clone_limb(scratch[(tmp1 + i)]));
    scratch[(out + i)] = final_val;
  }
  _ret = result_sign;
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

fn const_u32(c: u32) -> u32 {
  var _ret: u32;
  _ret = c;
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
        prod_lo = _td.f0;
        prod_hi = _td.f1;
      }
      {
        var _td = add3(prod_lo, scratch[(out + (i + j))], carry);
        sum1 = _td.f0;
        c1 = _td.f1;
      }
      {
        var _td = add3(prod_hi, c1, zero_val());
        new_carry = _td.f0;
        _c2 = _td.f1;
      }
      scratch[(out + (i + j))] = sum1;
      carry = new_carry;
    }
    scratch[(out + (i + n))] = carry;
  }
  return _ret;
}

fn clone_limb(self_val: u32) -> u32 {
  var _ret: u32;
  _ret = self_val;
  return _ret;
}

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

fn is_zero_limb(self_val: u32) -> u32 {
  var _ret: u32;
  if ((self_val == 0u)) {
    _ret = 1u;
  } else {
    _ret = 0u;
  }
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
      digit = _td.f0;
      next_carry = _td.f1;
    }
    scratch[(out + i)] = digit;
    carry = next_carry;
  }
  _ret = carry;
  return _ret;
}

fn sub_limbs_to_scratch_c_data_scratch(a: u32, b: u32, out: u32, n: u32) -> u32 {
  var borrow: u32;
  var i: u32;
  var digit: u32;
  var next_borrow: u32;
  var _ret: u32;
  borrow = zero_val();
  for (var i: u32 = 0u; i < n; i++) {
    {
      var _td = sub_borrow(scratch[(a + i)], c_data[(b + i)], borrow);
      digit = _td.f0;
      next_borrow = _td.f1;
    }
    scratch[(out + i)] = digit;
    borrow = next_borrow;
  }
  _ret = borrow;
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
      digit = _td.f0;
      next_borrow = _td.f1;
    }
    scratch[(out + i)] = digit;
    borrow = next_borrow;
  }
  _ret = borrow;
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
      digit = _td.f0;
      next_borrow = _td.f1;
    }
    scratch[(out + i)] = digit;
    borrow = next_borrow;
  }
  _ret = borrow;
  return _ret;
}

fn signed_add_to_scratch_scratch_scratch_scratch_scratch(a: u32, a_sign: u32, b: u32, b_sign: u32, out: u32, tmp1: u32, tmp2: u32, n: u32) -> u32 {
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
  _sum_carry = add_limbs_to_scratch_scratch_scratch(a, b, tmp1, n);
  borrow_ab = sub_limbs_to_scratch_scratch_scratch(a, b, tmp2, n);
  _borrow_ba = sub_limbs_to_scratch_scratch_scratch(b, a, out, n);
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
    diff_val = select_limb(borrow_ab, clone_limb(scratch[(tmp2 + i)]), clone_limb(scratch[(out + i)]));
    final_val = select_limb(same_sign, diff_val, clone_limb(scratch[(tmp1 + i)]));
    scratch[(out + i)] = final_val;
  }
  _ret = result_sign;
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
  var spt: u32;
  var sb: u32;
  var zr: u32;
  var zr_sign: u32;
  var zi: u32;
  var zi_sign: u32;
  var prod: u32;
  var re2: u32;
  var re2_sign: u32;
  var im2: u32;
  var im2_sign: u32;
  var sum2: u32;
  var sum2_sign: u32;
  var rpi: u32;
  var rpi_sign: u32;
  var tmp: u32;
  var tmp_sign: u32;
  var tmp2: u32;
  var tmp2_sign: u32;
  var stmp1: u32;
  var stmp2: u32;
  var c_stride: u32;
  var c_re: u32;
  var c_re_sign: u32;
  var c_im: u32;
  var c_im_sign: u32;
  var i: u32;
  var escaped_iter: u32;
  var iter: u32;
  var re2_s: u32;
  var im2_s: u32;
  var rpi_s: u32;
  var sum2_s: u32;
  var tmp_s: u32;
  var new_re_s: u32;
  var t1_s: u32;
  var t2_s: u32;
  var new_im_s: u32;
  var mag_re2_s: u32;
  var mag_im2_s: u32;
  var _call_tmp: u32;
  var thresh_off: u32;
  var borrow: u32;
  var alpha: u32;
  var t: u32;
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
  spt = ((16u * n) + 8u);
  sb = (tid * spt);
  zr = sb;
  zr_sign = (sb + n);
  zi = ((sb + n) + 1u);
  zi_sign = ((sb + (2u * n)) + 1u);
  prod = ((sb + (2u * n)) + 2u);
  re2 = ((sb + (4u * n)) + 2u);
  re2_sign = (re2 + n);
  im2 = (re2_sign + 1u);
  im2_sign = (im2 + n);
  sum2 = (im2_sign + 1u);
  sum2_sign = (sum2 + n);
  rpi = (sum2_sign + 1u);
  rpi_sign = (rpi + n);
  tmp = (rpi_sign + 1u);
  tmp_sign = (tmp + n);
  tmp2 = (tmp_sign + 1u);
  tmp2_sign = (tmp2 + n);
  stmp1 = (tmp2_sign + 1u);
  stmp2 = (stmp1 + n);
  c_stride = ((2u * n) + 2u);
  c_re = (tid * c_stride);
  c_re_sign = (c_re + n);
  c_im = (c_re_sign + 1u);
  c_im_sign = (c_im + n);
  for (var i: u32 = 0u; i < n; i++) {
    scratch[(zr + i)] = 0u;
    scratch[(zi + i)] = 0u;
  }
  scratch[zr_sign] = 0u;
  scratch[zi_sign] = 0u;
  escaped_iter = max_iters;
  for (var iter: u32 = 0u; iter < max_iters; iter++) {
    re2_s = signed_mul_to_scratch_scratch_scratch_scratch(zr, scratch[zr_sign], zr, scratch[zr_sign], re2, prod, n, frac_limbs);
    scratch[re2_sign] = re2_s;
    im2_s = signed_mul_to_scratch_scratch_scratch_scratch(zi, scratch[zi_sign], zi, scratch[zi_sign], im2, prod, n, frac_limbs);
    scratch[im2_sign] = im2_s;
    rpi_s = signed_add_to_scratch_scratch_scratch_scratch_scratch(zr, scratch[zr_sign], zi, scratch[zi_sign], rpi, stmp1, stmp2, n);
    scratch[rpi_sign] = rpi_s;
    sum2_s = signed_mul_to_scratch_scratch_scratch_scratch(rpi, scratch[rpi_sign], rpi, scratch[rpi_sign], sum2, prod, n, frac_limbs);
    scratch[sum2_sign] = sum2_s;
    tmp_s = signed_sub_to_scratch_scratch_scratch_scratch_scratch(re2, scratch[re2_sign], im2, scratch[im2_sign], tmp, stmp1, stmp2, n);
    scratch[tmp_sign] = tmp_s;
    new_re_s = signed_add_to_scratch_c_data_scratch_scratch_scratch(tmp, scratch[tmp_sign], c_re, c_data[c_re_sign], zr, stmp1, stmp2, n);
    scratch[zr_sign] = new_re_s;
    t1_s = signed_sub_to_scratch_scratch_scratch_scratch_scratch(sum2, scratch[sum2_sign], re2, scratch[re2_sign], tmp, stmp1, stmp2, n);
    scratch[tmp_sign] = t1_s;
    t2_s = signed_sub_to_scratch_scratch_scratch_scratch_scratch(tmp, scratch[tmp_sign], im2, scratch[im2_sign], tmp2, stmp1, stmp2, n);
    scratch[tmp2_sign] = t2_s;
    new_im_s = signed_add_to_scratch_c_data_scratch_scratch_scratch(tmp2, scratch[tmp2_sign], c_im, c_data[c_im_sign], zi, stmp1, stmp2, n);
    scratch[zi_sign] = new_im_s;
    mag_re2_s = signed_mul_to_scratch_scratch_scratch_scratch(zr, scratch[zr_sign], zr, scratch[zr_sign], re2, prod, n, frac_limbs);
    mag_im2_s = signed_mul_to_scratch_scratch_scratch_scratch(zi, scratch[zi_sign], zi, scratch[zi_sign], im2, prod, n, frac_limbs);
    _call_tmp = add_limbs_to_scratch_scratch_scratch(re2, im2, tmp, n);
    thresh_off = 5u;
    borrow = sub_limbs_to_scratch_params_scratch(tmp, thresh_off, tmp2, n);
    if ((borrow == 0u)) {
      if ((escaped_iter == max_iters)) {
        escaped_iter = iter;
      } else {
      }
    } else {
    }
  }
  alpha = 4278190080u;
  if ((escaped_iter >= max_iters)) {
    iter_counts[tid] = alpha;
  } else {
    t = ((escaped_iter * 255u) / max_iters);
    r = t;
    g = (t / 3u);
    b = (255u - (t / 2u));
    iter_counts[tid] = (((alpha | (b << 16u)) | (g << 8u)) | r);
  }
}

