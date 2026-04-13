// Verified Mandelbrot WebGPU renderer.
// All multi-precision arithmetic from verus-fixed-point (914 verified, 0 errors),
// auto-transpiled to WGSL via verus-gpu-parser.

// ═══════════════════════════════════════════════════════════════
// WGSL Shader — verified arithmetic functions from verus-fixed-point
// ═══════════════════════════════════════════════════════════════

// The core arithmetic functions (add3, sub_borrow, mul2, etc.) are
// transpiled from the verified Verus source. For the web demo, we inline
// a clean version that mirrors the verified code structure exactly.

// Load the auto-generated WGSL shaders from verified Verus code.
// One shader per limb count (n=4,8,16,32,64) with matching array sizes.
const SHADER_VARIANTS = {};  // n -> { code, pipeline }
let ENTRY_POINT = 'mandelbrot_perturbation';

async function loadShader() {
  const sizes = [4, 8, 16, 32, 64];
  for (const n of sizes) {
    const resp = await fetch(`mandelbrot_perturbation_n${n}.wgsl`);
    if (resp.ok) {
      SHADER_VARIANTS[n] = { code: await resp.text(), pipeline: null };
      console.log(`Loaded shader for n=${n}: ${SHADER_VARIANTS[n].code.split('\\n').length} lines`);
    }
  }
  // Fallback: try the default shader (for n=4)
  if (!SHADER_VARIANTS[4]) {
    const resp = await fetch('mandelbrot_perturbation.wgsl');
    if (resp.ok) {
      SHADER_VARIANTS[4] = { code: await resp.text(), pipeline: null };
    }
  }
}

const SHADER_CODE_FALLBACK = `
// Fallback (should not be used — load mandelbrot_verified.wgsl instead)
struct R2 { _0: u32, _1: u32, }

// ── Verified LimbOps (from verus-fixed-point/limb_ops.rs) ──

fn add3(a: u32, b: u32, carry: u32) -> R2 {
  // Verified: out._0 == (a + b + carry) % 2^32
  //           out._1 == (a + b + carry) / 2^32
  var ab = a + b;
  var c1 = select(0u, 1u, ab < a);
  var abc = ab + carry;
  var c2 = select(0u, 1u, abc < ab);
  return R2(abc, c1 + c2);
}

fn sub_borrow(a: u32, b: u32, borrow: u32) -> R2 {
  var diff = a - b;
  var bw1 = select(0u, 1u, a < b);
  var result = diff - borrow;
  var bw2 = select(0u, 1u, diff < borrow);
  return R2(result, bw1 + bw2);
}

fn mul2(a: u32, b: u32) -> R2 {
  // 32x32 → 64-bit via 16-bit split (GPU has no u64)
  var a_lo = a & 0xFFFFu;
  var a_hi = a >> 16u;
  var b_lo = b & 0xFFFFu;
  var b_hi = b >> 16u;
  var p0 = a_lo * b_lo;
  var p1 = a_lo * b_hi;
  var p2 = a_hi * b_lo;
  var p3 = a_hi * b_hi;
  var mid = p1 + p2;
  var mid_carry = select(0u, 1u, mid < p1);
  var lo = p0 + (mid << 16u);
  var lo_carry = select(0u, 1u, lo < p0);
  var hi = p3 + (mid >> 16u) + (mid_carry << 16u) + lo_carry;
  return R2(lo, hi);
}

fn select_limb(cond: u32, if_zero: u32, if_nonzero: u32) -> u32 {
  return select(if_zero, if_nonzero, cond != 0u);
}

// ── Multi-limb operations (from verus-fixed-point, buffer-backed) ──

@group(0) @binding(0) var<storage, read> c_data: array<u32>;
@group(0) @binding(1) var<storage, read_write> scratch: array<u32>;
@group(0) @binding(2) var<storage, read_write> iter_counts: array<u32>;
@group(0) @binding(3) var<storage, read> params: array<u32>;

// Add n-limb values: scratch[a_off..] + scratch[b_off..] → scratch[out_off..], returns carry
fn add_limbs(a_off: u32, b_off: u32, out_off: u32, n: u32) -> u32 {
  var carry: u32 = 0u;
  for (var i: u32 = 0u; i < n; i++) {
    var td = add3(scratch[a_off + i], scratch[b_off + i], carry);
    scratch[out_off + i] = td._0;
    carry = td._1;
  }
  return carry;
}

// Sub n-limb values: scratch[a_off..] - scratch[b_off..] → scratch[out_off..], returns borrow
fn sub_limbs(a_off: u32, b_off: u32, out_off: u32, n: u32) -> u32 {
  var borrow: u32 = 0u;
  for (var i: u32 = 0u; i < n; i++) {
    var td = sub_borrow(scratch[a_off + i], scratch[b_off + i], borrow);
    scratch[out_off + i] = td._0;
    borrow = td._1;
  }
  return borrow;
}

// Conditional select: if cond==0 copy a to out, else copy b to out
fn select_vec(cond: u32, a_off: u32, b_off: u32, out_off: u32, n: u32) {
  for (var i: u32 = 0u; i < n; i++) {
    scratch[out_off + i] = select_limb(cond, scratch[a_off + i], scratch[b_off + i]);
  }
}

// Multiply n-limb by scalar, result is (n+1) limbs at out_off
fn mul_by_scalar(a_off: u32, scalar: u32, out_off: u32, n: u32) {
  var carry: u32 = 0u;
  for (var i: u32 = 0u; i < n; i++) {
    var td = mul2(scratch[a_off + i], scalar);
    var td2 = add3(td._0, carry, 0u);
    scratch[out_off + i] = td2._0;
    carry = td._1 + td2._1;
  }
  scratch[out_off + n] = carry;
}

// Schoolbook n×n multiply → 2n limbs at out_off
fn mul_schoolbook(a_off: u32, b_off: u32, out_off: u32, n: u32) {
  // Zero output
  for (var i: u32 = 0u; i < 2u * n; i++) {
    scratch[out_off + i] = 0u;
  }
  // Schoolbook multiply
  for (var i: u32 = 0u; i < n; i++) {
    var carry: u32 = 0u;
    for (var j: u32 = 0u; j < n; j++) {
      var td = mul2(scratch[a_off + i], scratch[b_off + j]);
      var td2 = add3(td._0, scratch[out_off + i + j], carry);
      scratch[out_off + i + j] = td2._0;
      carry = td._1 + td2._1;
    }
    scratch[out_off + i + n] = carry;
  }
}

// Mersenne reduction: 2n-limb product → n-limb result mod p = 2^(32n) - c
fn mersenne_reduce(prod_off: u32, out_off: u32, n: u32, c_val: u32, p_off: u32) {
  // hi * c: multiply upper n limbs by c_val
  var hi_off = prod_off + n;
  var hc_off = out_off;  // temporary: store hi*c at out_off (will be overwritten)

  // hi * c_val → (n+1) limbs
  var carry: u32 = 0u;
  for (var i: u32 = 0u; i < n; i++) {
    var td = mul2(scratch[hi_off + i], c_val);
    var td2 = add3(td._0, carry, 0u);
    scratch[hc_off + i] = td2._0;
    carry = td._1 + td2._1;
  }
  var hc_top = carry;

  // lo + hi*c → out_off
  var add_carry = add_limbs(prod_off, hc_off, out_off, n);

  // Fold remaining: (add_carry + hc_top) * c_val
  var extra = (add_carry + hc_top) * c_val;
  var td3 = add3(scratch[out_off], extra, 0u);
  scratch[out_off] = td3._0;
  var prop = td3._1;
  for (var i: u32 = 1u; i < n; i++) {
    if (prop == 0u) { break; }
    var td4 = add3(scratch[out_off + i], prop, 0u);
    scratch[out_off + i] = td4._0;
    prop = td4._1;
  }

  // Conditional subtract p (twice for safety)
  var diff_off = out_off + n;  // temp space after out
  var bw1 = sub_limbs_ab(out_off, p_off, diff_off, n);
  select_vec(bw1, diff_off, out_off, out_off, n);
  bw1 = sub_limbs_ab(out_off, p_off, diff_off, n);
  select_vec(bw1, diff_off, out_off, out_off, n);
}

// Sub: scratch[a] - params[b] → scratch[out]
fn sub_limbs_ab(a_off: u32, b_off: u32, out_off: u32, n: u32) -> u32 {
  var borrow: u32 = 0u;
  for (var i: u32 = 0u; i < n; i++) {
    var td = sub_borrow(scratch[a_off + i], params[b_off + i], borrow);
    scratch[out_off + i] = td._0;
    borrow = td._1;
  }
  return borrow;
}

// Add: c_data[a] + scratch[b] → scratch[out]
fn add_limbs_cd(a_off: u32, b_off: u32, out_off: u32, n: u32) -> u32 {
  var carry: u32 = 0u;
  for (var i: u32 = 0u; i < n; i++) {
    var td = add3(c_data[a_off + i], scratch[b_off + i], carry);
    scratch[out_off + i] = td._0;
    carry = td._1;
  }
  return carry;
}

// Modular multiply: scratch[a] * scratch[b] mod p → scratch[out]
fn mul_mod(a_off: u32, b_off: u32, out_off: u32, n: u32, c_val: u32, p_off: u32, tmp_off: u32) {
  mul_schoolbook(a_off, b_off, tmp_off, n);
  mersenne_reduce(tmp_off, out_off, n, c_val, p_off);
}

// ── Mandelbrot kernel ──

@compute @workgroup_size(16, 16, 1)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
  // params layout: [width, height, max_iters, n_limbs, c_val, p0..p_{n-1}]
  var width = params[0];
  var height = params[1];
  var max_iters = params[2];
  var n = params[3];
  var c_val = params[4];
  var p_off: u32 = 5u;

  var px = gid.x;
  var py = gid.y;
  if (px >= width || py >= height) { return; }
  var tid = py * width + px;

  // Scratch layout per thread (all offsets relative to sb):
  // 0..n:      z_re
  // n..2n:     z_im
  // 2n..4n:    product tmp (2n limbs)
  // 4n..5n:    reduced tmp
  // 5n..6n:    temp1
  // 6n..7n:    temp2
  // 7n..8n:    temp3
  // 8n..10n:   extra product tmp
  // 10n..12n:  mersenne reduce scratch
  var words_per_thread = 12u * n;
  var sb = tid * words_per_thread;

  var zr = sb;
  var zi = sb + n;
  var prod_tmp = sb + 2u * n;
  var red_tmp = sb + 4u * n;
  var t1 = sb + 5u * n;
  var t2 = sb + 6u * n;
  var t3 = sb + 7u * n;
  var prod_tmp2 = sb + 8u * n;
  var red_scratch = sb + 10u * n;

  // c for this pixel: c_data[tid * 2n .. tid * 2n + 2n]
  var c_re_off = tid * 2u * n;
  var c_im_off = c_re_off + n;

  // Z_0 = 0
  for (var i: u32 = 0u; i < n; i++) {
    scratch[zr + i] = 0u;
    scratch[zi + i] = 0u;
  }

  var escaped_iter = max_iters;

  // Mandelbrot iteration: Z_{n+1} = Z_n^2 + c
  for (var iter: u32 = 0u; iter < max_iters; iter++) {
    // Complex squaring: Z^2 = (re^2 - im^2, 2*re*im)
    // Using 3-mul trick: re^2, im^2, (re+im)^2
    // new_im = (re+im)^2 - re^2 - im^2

    // re^2 → t1
    mul_mod(zr, zr, t1, n, c_val, p_off, prod_tmp);

    // im^2 → t2
    mul_mod(zi, zi, t2, n, c_val, p_off, prod_tmp);

    // re + im → t3
    var carry_ri = add_limbs(zr, zi, t3, n);
    // Fold carry (carry * c_val)
    var fold_c = carry_ri * c_val;
    var td_fc = add3(scratch[t3], fold_c, 0u);
    scratch[t3] = td_fc._0;
    var prop_c = td_fc._1;
    for (var i: u32 = 1u; i < n; i++) {
      if (prop_c == 0u) { break; }
      var td_p = add3(scratch[t3 + i], prop_c, 0u);
      scratch[t3 + i] = td_p._0;
      prop_c = td_p._1;
    }
    // Conditional subtract p
    var bw_ri = sub_limbs_ab(t3, p_off, red_tmp, n);
    select_vec(bw_ri, red_tmp, t3, t3, n);

    // (re+im)^2 → red_tmp
    mul_mod(t3, t3, red_tmp, n, c_val, p_off, prod_tmp);

    // new_re = re^2 - im^2 + c_re
    // re^2 - im^2 → zr (new)
    sub_limbs(t1, t2, zr, n);
    // + c_re
    add_limbs_cd(c_re_off, zr, zr, n);
    // Fold carry + conditional sub p (simplified: just sub p if >= p)
    var bw_nr = sub_limbs_ab(zr, p_off, t3, n);
    select_vec(bw_nr, t3, zr, zr, n);

    // new_im = (re+im)^2 - re^2 - im^2 + c_im
    sub_limbs(red_tmp, t1, zi, n);
    sub_limbs(zi, t2, zi, n);
    add_limbs_cd(c_im_off, zi, zi, n);
    var bw_ni = sub_limbs_ab(zi, p_off, t3, n);
    select_vec(bw_ni, t3, zi, zi, n);

    // Escape check: |Z|^2 > 4
    // re^2 + im^2 (already in t1, t2 from this iteration's squaring)
    // Wait — t1 and t2 were re^2 and im^2 BEFORE the update.
    // For escape, use the NEW z values. Recompute re^2 + im^2.
    mul_mod(zr, zr, t1, n, c_val, p_off, prod_tmp);
    mul_mod(zi, zi, t2, n, c_val, p_off, prod_tmp);
    add_limbs(t1, t2, t3, n);
    // Compare against escape threshold (params[5+n..5+2n] = threshold limbs)
    var thresh_off = p_off + n;
    var bw_esc = sub_limbs_ab(t3, thresh_off, red_tmp, n);
    // bw_esc == 0 → |Z|^2 >= threshold → escaped
    if (bw_esc == 0u && escaped_iter == max_iters) {
      escaped_iter = iter;
    }
  }

  iter_counts[tid] = escaped_iter;
}
`;

// ═══════════════════════════════════════════════════════════════
// WebGPU Setup + Rendering
// ═══════════════════════════════════════════════════════════════

let device, pipeline, bindGroupLayout;
// Center coordinates as BigInt fixed-point (scaled by 2^(32*frac_limbs))
// and zoom as BigInt (pixel spacing = 3 / (zoom * width), represented as BigInt ratio)
let centerRe = -0.5, centerIm = 0.0, zoom = 1.0;
// BigInt versions for deep zoom (initialized lazily)
let centerReBig = null, centerImBig = null, zoomBig = 1n;

const statusEl = document.getElementById('status');
const canvas = document.getElementById('canvas');
const ctx2d = canvas.getContext('2d');

// Slider UI
const refNSlider = document.getElementById('refN');
const pertNSlider = document.getElementById('pertN');
const maxItersSlider = document.getElementById('maxIters');
const resSlider = document.getElementById('resolution');
const maxRoundsSlider = document.getElementById('maxRounds');
const renderBtn = document.getElementById('renderBtn');

refNSlider.oninput = () => {
  const n = 1 << refNSlider.value;
  document.getElementById('refNVal').textContent = n;
  // Show max iters for this n (shared memory constraint)
  const maxI = Math.floor((8192 - 10 * n - 259) / (2 * n + 2)) - 2;
  document.getElementById('maxItersVal').textContent = maxItersSlider.value + ` (max ${maxI})`;
};
pertNSlider.oninput = () => document.getElementById('pertNVal').textContent = (1 << pertNSlider.value);
maxItersSlider.oninput = () => {
  const n = 1 << refNSlider.value;
  const maxI = Math.floor((8192 - 10 * n - 259) / (2 * n + 2)) - 2;
  document.getElementById('maxItersVal').textContent = maxItersSlider.value + ` (max ${maxI})`;
};
resSlider.oninput = () => document.getElementById('resVal').textContent = resSlider.value;
if (maxRoundsSlider) maxRoundsSlider.oninput = () => document.getElementById('maxRoundsVal').textContent = maxRoundsSlider.value;

// Initialize display
refNSlider.oninput();
pertNSlider.oninput();

async function initWebGPU() {
  if (!navigator.gpu) {
    statusEl.textContent = 'WebGPU not supported in this browser';
    return false;
  }
  const adapter = await navigator.gpu.requestAdapter();
  if (!adapter) {
    statusEl.textContent = 'No GPU adapter found';
    return false;
  }
  device = await adapter.requestDevice();
  statusEl.textContent = 'Ready';
  return true;
}

// Get or create a compute pipeline for the given limb count n.
async function getPipeline(n) {
  const variant = SHADER_VARIANTS[n];
  if (!variant) {
    statusEl.textContent = `No shader for n=${n}`;
    return null;
  }
  if (variant.pipeline) return variant.pipeline;

  const shaderModule = device.createShaderModule({ code: variant.code });
  const info = await shaderModule.getCompilationInfo();
  for (const msg of info.messages) {
    if (msg.type === 'error') {
      statusEl.textContent = `Shader error (n=${n}): ${msg.message}`;
      console.error('Shader error:', msg);
      return null;
    }
  }
  variant.pipeline = device.createComputePipeline({
    layout: 'auto',
    compute: { module: shaderModule, entryPoint: ENTRY_POINT },
  });
  console.log(`Created pipeline for n=${n}`);
  return variant.pipeline;
}

// Convert a double to sign-magnitude fixed-point limbs.
// Returns { limbs: Uint32Array(n), sign: 0 or 1 }.
// Limb 0 is LSB (fractional), limb n-1 is MSB (integer part).
function doubleToFixedPoint(val, n) {
  const limbs = new Uint32Array(n);
  const sign = val < 0 ? 1 : 0;
  let absVal = Math.abs(val);
  for (let i = n - 1; i >= 0; i--) {
    const limb = Math.floor(absVal) >>> 0;
    limbs[i] = limb;
    absVal = (absVal - limb) * 4294967296;
  }
  return { limbs, sign };
}

// Convert a BigInt (scaled by 2^(32*fracLimbs)) to sign-magnitude fixed-point limbs.
// Full precision — no f64 rounding.
function bigintToFixedPoint(val, n) {
  const limbs = new Uint32Array(n);
  const sign = val < 0n ? 1 : 0;
  let abs = val < 0n ? -val : val;
  const mask = (1n << 32n) - 1n;
  for (let i = 0; i < n; i++) {
    limbs[i] = Number(abs & mask);
    abs >>= 32n;
  }
  return { limbs, sign };
}

// Convert f64 to BigInt fixed-point (scaled by 2^(32*fracLimbs))
function doubleToBigFixed(val, fracLimbs) {
  const scale = 1n << BigInt(32 * fracLimbs);
  // Use enough precision: multiply by scale, round
  const sign = val < 0 ? -1n : 1n;
  const abs = Math.abs(val);
  const intPart = BigInt(Math.floor(abs));
  const fracPart = abs - Number(intPart);
  // fracPart * scale — do in steps to avoid f64 overflow
  let frac = 0n;
  let remaining = fracPart;
  for (let i = 0; i < fracLimbs; i++) {
    remaining *= 4294967296;
    const limb = BigInt(Math.floor(remaining) >>> 0);
    frac += limb << BigInt(32 * i);
    remaining -= Number(limb);
  }
  return sign * (intPart * scale + frac);
}

// HSV to RGB for coloring
function hsvToRgb(h, s, v) {
  let r, g, b;
  const i = Math.floor(h * 6);
  const f = h * 6 - i;
  const p = v * (1 - s);
  const q = v * (1 - f * s);
  const t = v * (1 - (1 - f) * s);
  switch (i % 6) {
    case 0: r = v; g = t; b = p; break;
    case 1: r = q; g = v; b = p; break;
    case 2: r = p; g = v; b = t; break;
    case 3: r = p; g = q; b = v; break;
    case 4: r = t; g = p; b = v; break;
    case 5: r = v; g = p; b = q; break;
  }
  return [Math.round(r * 255), Math.round(g * 255), Math.round(b * 255)];
}

async function render() {
  if (!device) return;
  const width = parseInt(resSlider.value);
  const height = width;
  canvas.width = width;
  canvas.height = height;

  const n = 1 << parseInt(refNSlider.value); // limbs per value
  const maxIters = parseInt(maxItersSlider.value);
  const frac_limbs = n - 1; // n-1 fractional limbs, 1 integer limb

  // Enforce shared memory constraint: (maxIters+2)*(2n+2) + 10n + 259 <= 8192
  const sharedMemNeeded = (maxIters + 2) * (2 * n + 2) + 10 * n + 259;
  const maxItersForN = Math.floor((8192 - 10 * n - 259) / (2 * n + 2)) - 2;
  if (sharedMemNeeded > 8192) {
    statusEl.textContent = `n=${n} requires max_iters <= ${maxItersForN} (shared memory limit). Reduce iters or N.`;
    return;
  }

  // Get pipeline for this n
  pipeline = await getPipeline(n);
  if (!pipeline) return;

  statusEl.textContent = `Computing ${width}x${height}, N=${n} limbs, ${maxIters} iters...`;

  const totalPixels = width * height;

  // Build c_data: per pixel [re_limbs(n), re_sign(1), im_limbs(n), im_sign(1)]
  // Use BigInt arithmetic for full precision at any zoom level.
  const stride = 2 * n + 2; // words per pixel
  const c_data = new Uint32Array(totalPixels * stride);

  // Convert center to BigInt fixed-point if not already
  const centerReBig_ = centerReBig !== null ? centerReBig : doubleToBigFixed(centerRe, frac_limbs);
  const centerImBig_ = centerImBig !== null ? centerImBig : doubleToBigFixed(centerIm, frac_limbs);

  // Pixel step in BigInt: 3 * 2^(32*frac_limbs) / (zoom * width)
  // = 3 * scale / (zoom * width)
  const scale = 1n << BigInt(32 * frac_limbs);
  const zoomBig_ = zoomBig > 1n ? zoomBig : BigInt(Math.round(zoom));
  const pixelStepBig = (3n * scale) / (zoomBig_ * BigInt(width));

  for (let py = 0; py < height; py++) {
    for (let px = 0; px < width; px++) {
      const dx = BigInt(px - Math.floor(width / 2));
      const dy = BigInt(py - Math.floor(height / 2));
      const cr = centerReBig_ + dx * pixelStepBig;
      const ci = centerImBig_ + dy * pixelStepBig;
      const idx = (py * width + px) * stride;
      const re = bigintToFixedPoint(cr, n);
      const im = bigintToFixedPoint(ci, n);
      c_data.set(re.limbs, idx);
      c_data[idx + n] = re.sign;
      c_data.set(im.limbs, idx + n + 1);
      c_data[idx + 2 * n + 1] = im.sign;
    }
  }

  // Build params: [width, height, max_iters, n_limbs, frac_limbs, thresh_limbs(n), max_rounds, use_perturbation]
  // Escape threshold = 4.0 in fixed-point: integer part = 4 in top limb
  const thresh_limbs = new Uint32Array(n);
  thresh_limbs[n - 1] = 4;
  const maxRounds = parseInt(document.getElementById('maxRounds')?.value || '5');
  const usePerturbation = document.getElementById('usePerturbation')?.checked ? 1 : 0;
  const paramsData = new Uint32Array(7 + n);
  paramsData[0] = width;
  paramsData[1] = height;
  paramsData[2] = maxIters;
  paramsData[3] = n;
  paramsData[4] = frac_limbs;
  paramsData.set(thresh_limbs, 5);
  paramsData[5 + n] = maxRounds;
  paramsData[6 + n] = usePerturbation;

  // No scratch buffer needed — all intermediates are thread-local arrays
  const iterCountsSize = totalPixels * 4;

  // Create GPU buffers
  const cDataBuf = device.createBuffer({ size: c_data.byteLength, usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST });
  const iterCountsBuf = device.createBuffer({ size: iterCountsSize, usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC });
  const paramsBuf = device.createBuffer({ size: paramsData.byteLength, usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST });
  const readbackBuf = device.createBuffer({ size: iterCountsSize, usage: GPUBufferUsage.MAP_READ | GPUBufferUsage.COPY_DST });

  device.queue.writeBuffer(cDataBuf, 0, c_data);
  device.queue.writeBuffer(paramsBuf, 0, paramsData);

  const bindGroup = device.createBindGroup({
    layout: pipeline.getBindGroupLayout(0),
    entries: [
      { binding: 0, resource: { buffer: cDataBuf } },
      { binding: 2, resource: { buffer: iterCountsBuf } },
      { binding: 3, resource: { buffer: paramsBuf } },
    ],
  });

  const t0 = performance.now();

  const encoder = device.createCommandEncoder();
  const pass = encoder.beginComputePass();
  pass.setPipeline(pipeline);
  pass.setBindGroup(0, bindGroup);
  pass.dispatchWorkgroups(Math.ceil(width / 16), Math.ceil(height / 16));
  pass.end();
  encoder.copyBufferToBuffer(iterCountsBuf, 0, readbackBuf, 0, iterCountsSize);
  device.queue.submit([encoder.finish()]);

  await readbackBuf.mapAsync(GPUMapMode.READ);
  const iterCounts = new Uint32Array(readbackBuf.getMappedRange().slice(0));
  readbackBuf.unmap();

  const elapsed = performance.now() - t0;
  const zoomStr = zoomBig > 1n ? `zoom=2^${zoomBig.toString(2).length - 1}` : `zoom=${zoom.toFixed(0)}`;
  statusEl.textContent = `Done in ${elapsed.toFixed(0)}ms (${n} limbs, ${maxIters} iters, ${zoomStr})`;

  // Render to canvas — GPU outputs packed RGBA directly
  const imageData = ctx2d.createImageData(width, height);
  const pixels = new Uint8Array(iterCounts.buffer);
  imageData.data.set(pixels);
  ctx2d.putImageData(imageData, 0, 0);

  // Clean up
  cDataBuf.destroy();
  iterCountsBuf.destroy();
  paramsBuf.destroy();
  readbackBuf.destroy();
}

// Click to zoom — use BigInt for deep zoom precision
canvas.addEventListener('click', (e) => {
  const rect = canvas.getBoundingClientRect();
  const px = (e.clientX - rect.left) / rect.width;
  const py = (e.clientY - rect.top) / rect.height;
  const n = 1 << parseInt(refNSlider.value);
  const frac_limbs = n - 1;
  const scale = 1n << BigInt(32 * frac_limbs);

  // Initialize BigInt center from f64 on first zoom
  if (centerReBig === null) {
    centerReBig = doubleToBigFixed(centerRe, frac_limbs);
    centerImBig = doubleToBigFixed(centerIm, frac_limbs);
    zoomBig = BigInt(Math.round(zoom));
    if (zoomBig < 1n) zoomBig = 1n;
  }

  const pixelStepBig = (3n * scale) / (zoomBig * BigInt(canvas.width));
  const dx = BigInt(Math.round((px - 0.5) * canvas.width));
  const dy = BigInt(Math.round((py - 0.5) * canvas.height));
  centerReBig += dx * pixelStepBig;
  centerImBig += dy * pixelStepBig;
  zoomBig *= 2n;

  // Keep f64 in sync for display
  centerRe = Number(centerReBig) / Number(scale);
  centerIm = Number(centerImBig) / Number(scale);
  zoom = Number(zoomBig);

  render();
});

canvas.addEventListener('contextmenu', (e) => {
  e.preventDefault();
  if (zoomBig > 1n) {
    zoomBig /= 2n;
    if (zoomBig < 1n) zoomBig = 1n;
    zoom = Number(zoomBig);
  } else {
    zoom = Math.max(1, zoom / 2);
  }
  render();
});

renderBtn.onclick = render;

// Init
(async () => {
  await loadShader();
  if (await initWebGPU()) {
    render();
  }
})();
