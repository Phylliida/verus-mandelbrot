struct R2 {
  f0: u32,
  f1: u32,
}

struct R3 {
  f0: u32,
  f1: u32,
  f2: u32,
}

var<workgroup> wg_mem: array<u32, 8192>;
@group(0) @binding(0) var<storage, read> c_data: array<u32>;
@group(0) @binding(2) var<storage, read_write> iter_counts: array<u32>;
@group(0) @binding(3) var<storage, read> params: array<u32>;

fn ref_orbit_iteration_step_wg_mem___local_8___local_8(wg_mem: u32, zk_re: u32, zk_im: u32, zk_re_s: u32, zk_im_s: u32, ref_c_base: u32, ref_c_re_s: u32, ref_c_im_s: u32, t0_re2: u32, t0_im2: u32, t0_rpi: u32, t0_sum2: u32, t0_diff: u32, t0_prod: u32, t0_stmp1: u32, t0_stmp2: u32, t0_stmp3: u32, zn: u32, ref_a: ptr<function, array<u32, 8>>, ref_b: ptr<function, array<u32, 8>>, n: u32, frac_limbs: u32) -> R2 {
  var re2_s: u32;
  var im2_s: u32;
  var rpi_s: u32;
  var sum2_s: u32;
  var diff_s: u32;
  var new_re_s: u32;
  var t1_s: u32;
  var t2_s: u32;
  var new_im_s: u32;
  var _ret: R2;
  {
    var _td = ref_orbit_step_part_a_wg_mem___local_8___local_8(wg_mem, zk_re, zk_im, zk_re_s, zk_im_s, t0_re2, ref_a, ref_b, n, frac_limbs);
    re2_s = _td.f0;
    im2_s = _td.f1;
    rpi_s = _td.f2;
  }
  {
    var _td = ref_orbit_step_part_b_wg_mem___local_8___local_8(wg_mem, re2_s, im2_s, rpi_s, ref_c_re_s, t0_re2, zn, ref_c_base, ref_a, ref_b, n, frac_limbs);
    sum2_s = _td.f0;
    diff_s = _td.f1;
    new_re_s = _td.f2;
  }
  {
    var _td = ref_orbit_step_part_c_wg_mem___local_8___local_8(wg_mem, re2_s, im2_s, sum2_s, ref_c_im_s, t0_re2, zn, ref_c_base, ref_a, ref_b, n);
    t1_s = _td.f0;
    t2_s = _td.f1;
    new_im_s = _td.f2;
  }
  _ret = R2(new_re_s, new_im_s);
  return _ret;
}

fn direct_computation_fallback_c_data_c_data___local_8___local_8___local_8___local_8___local_8___local_8___local_8___local_16___local_8___local_8_params(c_re_slice: u32, c_re_sign: u32, c_im_slice: u32, c_im_sign: u32, z_re: ptr<function, array<u32, 8>>, z_im: ptr<function, array<u32, 8>>, t1: ptr<function, array<u32, 8>>, t2: ptr<function, array<u32, 8>>, t3: ptr<function, array<u32, 8>>, t4: ptr<function, array<u32, 8>>, t5: ptr<function, array<u32, 8>>, lprod: ptr<function, array<u32, 16>>, ls1: ptr<function, array<u32, 8>>, ls2: ptr<function, array<u32, 8>>, thresh: u32, n: u32, frac_limbs: u32, max_iters: u32) -> u32 {
  var n_us: u32;
  var frac_us: u32;
  var z_re_sign: u32;
  var z_im_sign: u32;
  var escaped_iter: u32;
  var iter: u32;
  var re2_s: u32;
  var im2_s: u32;
  var rpi_s: u32;
  var rpi2_s: u32;
  var diff_s: u32;
  var x1_s: u32;
  var x2_s: u32;
  var _fr2_s: u32;
  var _fi2_s: u32;
  var _mag_carry: u32;
  var borrow: u32;
  var _while_i: u32;
  var _ret: u32;
  n_us = n;
  frac_us = frac_limbs;
  z_re_sign = 0u;
  z_im_sign = 0u;
  escaped_iter = max_iters;
  iter = 0u;
  for (var _while_i: u32 = 0u; _while_i < 4294967295u; _while_i++) {
    if ((!(iter < max_iters))) {
      break;
    } else {
    }
    re2_s = fn_7(z_re, z_re_sign, z_re, z_re_sign, t3, 0u, lprod, 0u, n_us, frac_us);
    im2_s = fn_7(z_im, z_im_sign, z_im, z_im_sign, t4, 0u, lprod, 0u, n_us, frac_us);
    rpi_s = fn_8(z_re, z_re_sign, z_im, z_im_sign, t1, 0u, ls1, 0u, ls2, 0u, n_us);
    rpi2_s = fn_7(t1, rpi_s, t1, rpi_s, t2, 0u, lprod, 0u, n_us, frac_us);
    diff_s = fn_9(t3, re2_s, t4, im2_s, t5, 0u, ls1, 0u, ls2, 0u, n_us);
    z_re_sign = fn_8(t5, diff_s, c_re_slice, c_re_sign, z_re, 0u, ls1, 0u, ls2, 0u, n_us);
    x1_s = fn_9(t2, rpi2_s, t3, re2_s, t1, 0u, ls1, 0u, ls2, 0u, n_us);
    x2_s = fn_9(t1, x1_s, t4, im2_s, t5, 0u, ls1, 0u, ls2, 0u, n_us);
    z_im_sign = fn_8(t5, x2_s, c_im_slice, c_im_sign, z_im, 0u, ls1, 0u, ls2, 0u, n_us);
    _fr2_s = fn_7(z_re, z_re_sign, z_re, z_re_sign, t3, 0u, lprod, 0u, n_us, frac_us);
    _fi2_s = fn_7(z_im, z_im_sign, z_im, z_im_sign, t4, 0u, lprod, 0u, n_us, frac_us);
    _mag_carry = fn_10(t3, t4, t5, 0u, n_us);
    borrow = fn_11(t5, thresh, t1, 0u, n_us);
    if ((borrow == 0u)) {
      escaped_iter = iter;
      break;
    } else {
    }
    iter = (iter + 1u);
  }
  _ret = escaped_iter;
  return _ret;
}

fn copy_limbs_wg_mem___local_8(src: u32, src_off: u32, dst: ptr<function, array<u32, 8>>, n: u32) -> u32 {
  var i: u32;
  var _ret: u32;
  for (var i: u32 = 0u; i < n; i++) {
    (*dst)[i] = wg_mem[(src + (src_off + i))];
  }
  return _ret;
}

fn perturbation_iteration_step_wg_mem_wg_mem___local_8___local_8___local_8___local_8___local_8___local_8___local_8___local_8___local_8___local_16___local_8___local_8(z_re_slice: u32, z_re_sign: u32, z_im_slice: u32, z_im_sign: u32, delta_re: ptr<function, array<u32, 8>>, delta_re_sign_in: u32, delta_im: ptr<function, array<u32, 8>>, delta_im_sign_in: u32, dc_re: ptr<function, array<u32, 8>>, dc_re_sign: u32, dc_im: ptr<function, array<u32, 8>>, dc_im_sign: u32, t1: ptr<function, array<u32, 8>>, t2: ptr<function, array<u32, 8>>, t3: ptr<function, array<u32, 8>>, t4: ptr<function, array<u32, 8>>, t5: ptr<function, array<u32, 8>>, lprod: ptr<function, array<u32, 16>>, ls1: ptr<function, array<u32, 8>>, ls2: ptr<function, array<u32, 8>>, n: u32, frac_limbs: u32) -> R2 {
  var n_us: u32;
  var frac_us: u32;
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
  var _ret: R2;
  n_us = n;
  frac_us = frac_limbs;
  s1 = fn_7(z_re_slice, z_re_sign, delta_re, delta_re_sign_in, t1, 0u, lprod, 0u, n_us, frac_us);
  s2 = fn_7(z_im_slice, z_im_sign, delta_im, delta_im_sign_in, t2, 0u, lprod, 0u, n_us, frac_us);
  s3 = fn_7(z_re_slice, z_re_sign, delta_im, delta_im_sign_in, t3, 0u, lprod, 0u, n_us, frac_us);
  s4 = fn_7(z_im_slice, z_im_sign, delta_re, delta_re_sign_in, t4, 0u, lprod, 0u, n_us, frac_us);
  d1_s = fn_8(t1, s1, t2, s2, t5, 0u, ls1, 0u, ls2, 0u, n_us);
  tzd_re_s = fn_9(t5, d1_s, t5, d1_s, t1, 0u, ls1, 0u, ls2, 0u, n_us);
  d2_s = fn_9(t3, s3, t4, s4, t5, 0u, ls1, 0u, ls2, 0u, n_us);
  tzd_im_s = fn_9(t5, d2_s, t5, d2_s, t2, 0u, ls1, 0u, ls2, 0u, n_us);
  drs_s = fn_7(delta_re, delta_re_sign_in, delta_re, delta_re_sign_in, t3, 0u, lprod, 0u, n_us, frac_us);
  dis_s = fn_7(delta_im, delta_im_sign_in, delta_im, delta_im_sign_in, t4, 0u, lprod, 0u, n_us, frac_us);
  dri_s = fn_9(delta_re, delta_re_sign_in, delta_im, delta_im_sign_in, t5, 0u, ls1, 0u, ls2, 0u, n_us);
  dri2_s = fn_7(t5, dri_s, t5, dri_s, ls1, 0u, lprod, 0u, n_us, frac_us);
  dsq_re_s = fn_8(t3, drs_s, t4, dis_s, t5, 0u, delta_re, 0u, delta_im, 0u, n_us);
  q1_s = fn_8(ls1, dri2_s, t3, drs_s, delta_re, 0u, ls2, 0u, delta_im, 0u, n_us);
  dsq_im_s = fn_8(delta_re, q1_s, t4, dis_s, t3, 0u, ls2, 0u, delta_im, 0u, n_us);
  p1_s = fn_9(t1, tzd_re_s, t5, dsq_re_s, t4, 0u, ls1, 0u, ls2, 0u, n_us);
  new_dr_s = fn_9(t4, p1_s, dc_re, dc_re_sign, delta_re, 0u, ls1, 0u, ls2, 0u, n_us);
  p2_s = fn_9(t2, tzd_im_s, t3, dsq_im_s, t4, 0u, ls1, 0u, ls2, 0u, n_us);
  new_di_s = fn_9(t4, p2_s, dc_im, dc_im_sign, delta_im, 0u, ls1, 0u, ls2, 0u, n_us);
  _ret = R2(new_dr_s, new_di_s);
  return _ret;
}

fn ref_orbit_step_part_b_wg_mem___local_8___local_8(wg_mem: u32, re2_s: u32, im2_s: u32, rpi_s: u32, ref_c_re_s: u32, t0_re2: u32, zn: u32, ref_c_base: u32, ref_a: ptr<function, array<u32, 8>>, ref_b: ptr<function, array<u32, 8>>, n: u32, frac_limbs: u32) -> R3 {
  var t0_im2: u32;
  var t0_rpi: u32;
  var t0_sum2: u32;
  var t0_diff: u32;
  var t0_prod: u32;
  var t0_stmp1: u32;
  var t0_stmp2: u32;
  var _call_tmp: u32;
  var sum2_s: u32;
  var diff_s: u32;
  var new_re_s: u32;
  var _ret: R3;
  t0_im2 = (t0_re2 + n);
  t0_rpi = (t0_re2 + (2u * n));
  t0_sum2 = (t0_re2 + (3u * n));
  t0_diff = (t0_re2 + (4u * n));
  t0_prod = (t0_re2 + (5u * n));
  t0_stmp1 = (t0_re2 + (7u * n));
  t0_stmp2 = (t0_re2 + (8u * n));
  _call_tmp = copy_limbs_wg_mem___local_8(wg_mem, t0_rpi, ref_a, n);
  sum2_s = fn_7(ref_a, rpi_s, ref_a, rpi_s, wg_mem, t0_sum2, t0_prod, n, frac_limbs);
  _call_tmp = copy_limbs_wg_mem___local_8(wg_mem, t0_re2, ref_a, n);
  _call_tmp = copy_limbs_wg_mem___local_8(wg_mem, t0_im2, ref_b, n);
  diff_s = fn_8(ref_a, re2_s, ref_b, im2_s, wg_mem, t0_diff, t0_stmp1, t0_stmp2, n);
  _call_tmp = copy_limbs_wg_mem___local_8(wg_mem, t0_diff, ref_a, n);
  _call_tmp = copy_limbs_wg_mem___local_8(wg_mem, ref_c_base, ref_b, n);
  new_re_s = fn_9(ref_a, diff_s, ref_b, ref_c_re_s, wg_mem, zn, t0_stmp1, t0_stmp2, n);
  _ret = R3(sum2_s, diff_s, new_re_s);
  return _ret;
}

fn ref_orbit_step_part_a_wg_mem___local_8___local_8(wg_mem: u32, zk_re: u32, zk_im: u32, zk_re_s: u32, zk_im_s: u32, t0_re2: u32, ref_a: ptr<function, array<u32, 8>>, ref_b: ptr<function, array<u32, 8>>, n: u32, frac_limbs: u32) -> R3 {
  var t0_im2: u32;
  var t0_rpi: u32;
  var t0_prod: u32;
  var t0_stmp1: u32;
  var t0_stmp2: u32;
  var _call_tmp: u32;
  var re2_s: u32;
  var im2_s: u32;
  var rpi_s: u32;
  var _ret: R3;
  t0_im2 = (t0_re2 + n);
  t0_rpi = (t0_re2 + (2u * n));
  t0_prod = (t0_re2 + (5u * n));
  t0_stmp1 = (t0_re2 + (7u * n));
  t0_stmp2 = (t0_re2 + (8u * n));
  _call_tmp = copy_limbs_wg_mem___local_8(wg_mem, zk_re, ref_a, n);
  re2_s = fn_7(ref_a, zk_re_s, ref_a, zk_re_s, wg_mem, t0_re2, t0_prod, n, frac_limbs);
  _call_tmp = copy_limbs_wg_mem___local_8(wg_mem, zk_im, ref_a, n);
  im2_s = fn_7(ref_a, zk_im_s, ref_a, zk_im_s, wg_mem, t0_im2, t0_prod, n, frac_limbs);
  _call_tmp = copy_limbs_wg_mem___local_8(wg_mem, zk_re, ref_a, n);
  _call_tmp = copy_limbs_wg_mem___local_8(wg_mem, zk_im, ref_b, n);
  rpi_s = fn_8(ref_a, zk_re_s, ref_b, zk_im_s, wg_mem, t0_rpi, t0_stmp1, t0_stmp2, n);
  _ret = R3(re2_s, im2_s, rpi_s);
  return _ret;
}

fn ref_orbit_step_part_c_wg_mem___local_8___local_8(wg_mem: u32, re2_s: u32, im2_s: u32, sum2_s: u32, ref_c_im_s: u32, t0_re2: u32, zn: u32, ref_c_base: u32, ref_a: ptr<function, array<u32, 8>>, ref_b: ptr<function, array<u32, 8>>, n: u32) -> R3 {
  var t0_re2_off: u32;
  var t0_im2: u32;
  var t0_sum2: u32;
  var t0_diff: u32;
  var t0_stmp1: u32;
  var t0_stmp2: u32;
  var t0_stmp3: u32;
  var _call_tmp: u32;
  var t1_s: u32;
  var t2_s: u32;
  var new_im_s: u32;
  var _ret: R3;
  t0_re2_off = t0_re2;
  t0_im2 = (t0_re2 + n);
  t0_sum2 = (t0_re2 + (3u * n));
  t0_diff = (t0_re2 + (4u * n));
  t0_stmp1 = (t0_re2 + (7u * n));
  t0_stmp2 = (t0_re2 + (8u * n));
  t0_stmp3 = (t0_re2 + (9u * n));
  _call_tmp = copy_limbs_wg_mem___local_8(wg_mem, t0_sum2, ref_a, n);
  _call_tmp = copy_limbs_wg_mem___local_8(wg_mem, t0_re2_off, ref_b, n);
  t1_s = fn_7(ref_a, sum2_s, ref_b, re2_s, wg_mem, t0_diff, t0_stmp1, t0_stmp2, n);
  _call_tmp = copy_limbs_wg_mem___local_8(wg_mem, t0_diff, ref_a, n);
  _call_tmp = copy_limbs_wg_mem___local_8(wg_mem, t0_im2, ref_b, n);
  t2_s = fn_7(ref_a, t1_s, ref_b, im2_s, wg_mem, t0_stmp3, t0_stmp1, t0_stmp2, n);
  _call_tmp = copy_limbs_wg_mem___local_8(wg_mem, t0_stmp3, ref_a, n);
  _call_tmp = copy_limbs_wg_mem___local_8(wg_mem, ((ref_c_base + n) + 1u), ref_b, n);
  new_im_s = fn_8(ref_a, t2_s, ref_b, ref_c_im_s, wg_mem, ((zn + n) + 1u), t0_stmp1, t0_stmp2, n);
  _ret = R3(t1_s, t2_s, new_im_s);
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
  var max_rounds: u32;
  var use_perturbation: u32;
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
  var delta_re: array<u32, 8>;
  var delta_re_sign: u32;
  var delta_im: array<u32, 8>;
  var delta_im_sign: u32;
  var dc_re: array<u32, 8>;
  var dc_re_sign: u32;
  var dc_im: array<u32, 8>;
  var dc_im_sign: u32;
  var t1: array<u32, 8>;
  var t2: array<u32, 8>;
  var t3: array<u32, 8>;
  var t4: array<u32, 8>;
  var t5: array<u32, 8>;
  var lprod: array<u32, 16>;
  var ls1: array<u32, 8>;
  var ls2: array<u32, 8>;
  var ref_a: array<u32, 8>;
  var ref_b: array<u32, 8>;
  var escaped_iter: u32;
  var is_glitched: u32;
  var glitch_iter: u32;
  var round: u32;
  var ref_x: u32;
  var ref_y: u32;
  var ref_x_c: u32;
  var ref_y_c: u32;
  var ref_tid_init: u32;
  var ref_c_off: u32;
  var i: u32;
  var ref_escaped: u32;
  var ref_c_re_s: u32;
  var ref_c_im_s: u32;
  var iter: u32;
  var zk: u32;
  var zk_re: u32;
  var zk_re_sign: u32;
  var zk_im: u32;
  var zk_im_sign: u32;
  var zk_re_s: u32;
  var zk_im_s: u32;
  var zn: u32;
  var new_re_s: u32;
  var new_im_s: u32;
  var _call_tmp: u32;
  var thresh_off: u32;
  var esc_borrow: u32;
  var cre_s: u32;
  var cim_s: u32;
  var refre_s: u32;
  var refim_s: u32;
  var zn_re: u32;
  var zn_re_sign: u32;
  var zn_im: u32;
  var zn_im_sign: u32;
  var zn_re_s: u32;
  var zn_im_s: u32;
  var zn_re_slc: u32;
  var zn_im_slc: u32;
  var new_dr_s: u32;
  var new_di_s: u32;
  var full_re_s: u32;
  var full_im_s: u32;
  var fr2_s: u32;
  var fi2_s: u32;
  var mag_carry: u32;
  var borrow: u32;
  var _while_i: u32;
  var vi: u32;
  var best_vote: u32;
  var best_idx: u32;
  var g_count: u32;
  var v: u32;
  var best_gx_raw: u32;
  var best_gy_raw: u32;
  var best_gx: u32;
  var best_gy: u32;
  var best_tid: u32;
  var best_c_off: u32;
  var cre_s_fb: u32;
  var cim_s_fb: u32;
  var zi: u32;
  var alpha: u32;
  var t_col: u32;
  var r: u32;
  var g: u32;
  var half_t: u32;
  var b: u32;
  width = params[0u];
  height = params[1u];
  max_iters = params[2u];
  n = params[3u];
  frac_limbs = params[4u];
  max_rounds = params[(5u + n)];
  use_perturbation = params[(6u + n)];
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
  round = 0u;
  for (var _while_i: u32 = 0u; _while_i < 4294967295u; _while_i++) {
    if ((!((round < max_rounds) && (use_perturbation != 0u)))) {
      break;
    } else {
    }
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
      for (var i: u32 = 0u; i < n; i++) {
        wg_mem[(orbit_base + i)] = 0u;
      }
      wg_mem[(orbit_base + n)] = 0u;
      for (var i: u32 = 0u; i < n; i++) {
        wg_mem[(((orbit_base + n) + 1u) + i)] = 0u;
      }
      wg_mem[((orbit_base + (2u * n)) + 1u)] = 0u;
      ref_escaped = max_iters;
      ref_c_re_s = wg_mem[(ref_c_base + n)];
      ref_c_im_s = wg_mem[((ref_c_base + (2u * n)) + 1u)];
      if (((ref_c_re_s > 1u) || (ref_c_im_s > 1u))) {
        ref_escaped = 0u;
      } else {
        for (var iter: u32 = 0u; iter < max_iters; iter++) {
          zk = (orbit_base + (iter * z_stride));
          zk_re = zk;
          zk_re_sign = (zk + n);
          zk_im = ((zk + n) + 1u);
          zk_im_sign = ((zk + (2u * n)) + 1u);
          zk_re_s = wg_mem[zk_re_sign];
          zk_im_s = wg_mem[zk_im_sign];
          if (((zk_re_s > 1u) || (zk_im_s > 1u))) {
            ref_escaped = iter;
          } else {
            zn = (orbit_base + ((iter + 1u) * z_stride));
            {
              var _td = ref_orbit_iteration_step_wg_mem___local_8___local_8(0u, zk_re, zk_im, zk_re_s, zk_im_s, ref_c_base, ref_c_re_s, ref_c_im_s, t0_re2, t0_im2, t0_rpi, t0_sum2, t0_diff, t0_prod, t0_stmp1, t0_stmp2, t0_stmp3, zn, &ref_a, &ref_b, n, frac_limbs);
              new_re_s = _td.f0;
              new_im_s = _td.f1;
            }
            wg_mem[(zn + n)] = new_re_s;
            wg_mem[((zn + (2u * n)) + 1u)] = new_im_s;
            if ((ref_escaped == max_iters)) {
              _call_tmp = copy_limbs_wg_mem___local_8(0u, t0_re2, &ref_a, n);
              _call_tmp = copy_limbs_wg_mem___local_8(0u, t0_im2, &ref_b, n);
              _call_tmp = fn_8(&ref_a, &ref_b, 0u, t0_diff, n);
              thresh_off = 5u;
              _call_tmp = copy_limbs_wg_mem___local_8(0u, t0_diff, &ref_a, n);
              esc_borrow = fn_9(&ref_a, thresh_off, 0u, t0_stmp1, n);
              if ((esc_borrow == 0u)) {
                ref_escaped = (iter + 1u);
              } else {
              }
            } else {
            }
          }
        }
      }
      wg_mem[ref_escape_addr] = ref_escaped;
    } else {
    }
    workgroupBarrier();
    if (((is_glitched == 1u) && (escaped_iter == max_iters))) {
      cre_s = c_data[c_re_sign_off];
      cim_s = c_data[c_im_sign_off];
      refre_s = wg_mem[(ref_c_base + n)];
      refim_s = wg_mem[((ref_c_base + (2u * n)) + 1u)];
      if (((((cre_s > 1u) || (cim_s > 1u)) || (refre_s > 1u)) || (refim_s > 1u))) {
        is_glitched = 0u;
      } else {
        dc_re_sign = fn_10(c_re_off, cre_s, ref_c_base, refre_s, &dc_re, 0u, &ls1, 0u, &ls2, 0u, n);
        dc_im_sign = fn_10(c_im_off, cim_s, ((ref_c_base + n) + 1u), refim_s, &dc_im, 0u, &ls1, 0u, &ls2, 0u, n);
        for (var i: u32 = 0u; i < n; i++) {
          delta_re[i] = 0u;
          delta_im[i] = 0u;
        }
        delta_re_sign = 0u;
        delta_im_sign = 0u;
        is_glitched = 0u;
        ref_escaped = wg_mem[ref_escape_addr];
        iter = 0u;
        for (var _while_i: u32 = 0u; _while_i < 4294967295u; _while_i++) {
          if ((!(iter < max_iters))) {
            break;
          } else {
          }
          if ((iter >= ref_escaped)) {
            is_glitched = 1u;
            glitch_iter = iter;
            break;
          } else {
          }
          zn = (orbit_base + (iter * z_stride));
          zn_re = zn;
          zn_re_sign = (zn + n);
          zn_im = ((zn + n) + 1u);
          zn_im_sign = ((zn + (2u * n)) + 1u);
          zn_re_s = wg_mem[zn_re_sign];
          zn_im_s = wg_mem[zn_im_sign];
          if (((zn_re_s > 1u) || (zn_im_s > 1u))) {
            is_glitched = 1u;
            glitch_iter = iter;
            break;
          } else {
          }
          zn_re_slc = zn_re;
          zn_im_slc = zn_im;
          {
            var _td = perturbation_iteration_step_wg_mem_wg_mem___local_8___local_8___local_8___local_8___local_8___local_8___local_8___local_8___local_8___local_16___local_8___local_8(zn_re_slc, zn_re_s, zn_im_slc, zn_im_s, &delta_re, delta_re_sign, &delta_im, delta_im_sign, &dc_re, dc_re_sign, &dc_im, dc_im_sign, &t1, &t2, &t3, &t4, &t5, &lprod, &ls1, &ls2, n, frac_limbs);
            new_dr_s = _td.f0;
            new_di_s = _td.f1;
          }
          delta_re_sign = new_dr_s;
          delta_im_sign = new_di_s;
          if (((delta_re[(n - 1u)] > 3u) || (delta_im[(n - 1u)] > 3u))) {
            is_glitched = 1u;
            glitch_iter = iter;
            break;
          } else {
          }
          full_re_s = fn_11(zn_re, zn_re_s, &delta_re, delta_re_sign, &t1, 0u, &ls1, 0u, &ls2, 0u, n);
          full_im_s = fn_11(zn_im, zn_im_s, &delta_im, delta_im_sign, &t2, 0u, &ls1, 0u, &ls2, 0u, n);
          fr2_s = fn_12(&t1, full_re_s, &t1, full_re_s, &t3, 0u, &lprod, 0u, n, frac_limbs);
          fi2_s = fn_12(&t2, full_im_s, &t2, full_im_s, &t4, 0u, &lprod, 0u, n, frac_limbs);
          mag_carry = fn_8(&t3, &t4, &t5, 0u, n);
          thresh_off = 5u;
          borrow = fn_9(&t5, thresh_off, &t1, 0u, n);
          if ((borrow == 0u)) {
            if ((escaped_iter == max_iters)) {
              escaped_iter = iter;
            } else {
            }
          } else {
          }
          iter = (iter + 1u);
        }
      }
    } else {
    }
    workgroupBarrier();
    if ((local_id == 0u)) {
      vi = 0u;
      for (var _while_i: u32 = 0u; _while_i < 4294967295u; _while_i++) {
        if ((!(vi < 256u))) {
          break;
        } else {
        }
        wg_mem[(vote_base + vi)] = 0u;
        vi = (vi + 1u);
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
        v = wg_mem[(vote_base + i)];
        if ((v > best_vote)) {
          best_vote = v;
          best_idx = i;
        } else {
        }
        if ((v > 0u)) {
          g_count = (g_count + 1u);
        } else {
        }
      }
      wg_mem[glitch_count_addr] = g_count;
      wg_mem[best_ref_addr] = best_idx;
      if ((g_count > 0u)) {
        best_gx_raw = ((gid_x - lid_x) + (best_idx % 16u));
        best_gy_raw = ((gid_y - lid_y) + (best_idx / 16u));
        best_gx = select(best_gx_raw, (width - 1u), (best_gx_raw >= width));
        best_gy = select(best_gy_raw, (height - 1u), (best_gy_raw >= height));
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
    round = (round + 1u);
  }
  if (((is_glitched == 1u) && (escaped_iter == max_iters))) {
    cre_s_fb = c_data[c_re_sign_off];
    cim_s_fb = c_data[c_im_sign_off];
    if (((cre_s_fb <= 1u) && (cim_s_fb <= 1u))) {
      for (var zi: u32 = 0u; zi < n; zi++) {
        delta_re[zi] = 0u;
        delta_im[zi] = 0u;
      }
      escaped_iter = direct_computation_fallback_c_data_c_data___local_8___local_8___local_8___local_8___local_8___local_8___local_8___local_16___local_8___local_8_params(c_re_off, cre_s_fb, c_im_off, cim_s_fb, &delta_re, &delta_im, &t1, &t2, &t3, &t4, &t5, &lprod, &ls1, &ls2, 5u, n, frac_limbs, max_iters);
    } else {
    }
  } else {
  }
  alpha = 4278190080u;
  if ((escaped_iter >= max_iters)) {
    iter_counts[tid] = alpha;
  } else {
    t_col = ((escaped_iter * 255u) / max_iters);
    r = t_col;
    g = (t_col / 3u);
    half_t = (t_col / 2u);
    b = (255u - half_t);
    iter_counts[tid] = (((alpha | (b << 16u)) | (g << 8u)) | r);
  }
}
