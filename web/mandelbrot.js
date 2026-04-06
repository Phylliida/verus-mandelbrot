// Verified Mandelbrot WebGPU renderer.
// All multi-precision arithmetic from verus-fixed-point (914 verified, 0 errors),
// auto-transpiled to WGSL via verus-gpu-parser.

// ═══════════════════════════════════════════════════════════════
// WGSL Shader — verified arithmetic functions from verus-fixed-point
// ═══════════════════════════════════════════════════════════════

// The core arithmetic functions (add3, sub_borrow, mul2, etc.) are
// transpiled from the verified Verus source. For the web demo, we inline
// a clean version that mirrors the verified code structure exactly.

// Load the auto-generated WGSL from verified Verus code
let SHADER_CODE = null;

async function loadShader() {
  const resp = await fetch('mandelbrot_verified.wgsl');
  SHADER_CODE = await resp.text();
  console.log(`Loaded ${SHADER_CODE.split('\\n').length} lines of verified WGSL`);
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
let centerRe = -0.5, centerIm = 0.0, zoom = 1.0;

const statusEl = document.getElementById('status');
const canvas = document.getElementById('canvas');
const ctx2d = canvas.getContext('2d');

// Slider UI
const refNSlider = document.getElementById('refN');
const pertNSlider = document.getElementById('pertN');
const maxItersSlider = document.getElementById('maxIters');
const resSlider = document.getElementById('resolution');
const renderBtn = document.getElementById('renderBtn');

refNSlider.oninput = () => document.getElementById('refNVal').textContent = (1 << refNSlider.value);
pertNSlider.oninput = () => document.getElementById('pertNVal').textContent = (1 << pertNSlider.value);
maxItersSlider.oninput = () => document.getElementById('maxItersVal').textContent = maxItersSlider.value;
resSlider.oninput = () => document.getElementById('resVal').textContent = resSlider.value;

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
  device = await adapter.requestDevice({
    requiredLimits: {
      maxStorageBufferBindingSize: 512 * 1024 * 1024, // 512MB
      maxBufferSize: 512 * 1024 * 1024,
    }
  });

  const shaderModule = device.createShaderModule({ code: SHADER_CODE });

  // Check for compilation errors
  const info = await shaderModule.getCompilationInfo();
  for (const msg of info.messages) {
    if (msg.type === 'error') {
      statusEl.textContent = `Shader error: ${msg.message}`;
      console.error('Shader error:', msg);
      return false;
    }
  }

  pipeline = device.createComputePipeline({
    layout: 'auto',
    compute: { module: shaderModule, entryPoint: 'mandelbrot_fixedpoint' },
  });

  statusEl.textContent = 'Ready';
  return true;
}

// Convert a double to sign-magnitude fixed-point limbs.
// Returns { limbs: Uint32Array(n), sign: 0 or 1 }.
// Limb 0 is LSB (fractional), limb n-1 is MSB (integer part).
// frac_limbs fractional limbs, rest is integer.
function doubleToFixedPoint(val, n) {
  const limbs = new Uint32Array(n);
  const sign = val < 0 ? 1 : 0;
  let absVal = Math.abs(val);

  // Fill from MSB (integer part) down to LSB (finest fractional)
  for (let i = n - 1; i >= 0; i--) {
    const limb = Math.floor(absVal) >>> 0;
    limbs[i] = limb;
    absVal = (absVal - limb) * 4294967296; // * 2^32
  }
  return { limbs, sign };
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

  statusEl.textContent = `Computing ${width}x${height}, N=${n} limbs, ${maxIters} iters...`;

  const totalPixels = width * height;

  // Build c_data: per pixel [re_limbs(n), re_sign(1), im_limbs(n), im_sign(1)]
  const stride = 2 * n + 2; // words per pixel
  const c_data = new Uint32Array(totalPixels * stride);
  const pixelStep = 3.0 / (zoom * width);
  for (let py = 0; py < height; py++) {
    for (let px = 0; px < width; px++) {
      const cr = centerRe + (px - width / 2 + 0.5) * pixelStep;
      const ci = centerIm + (py - height / 2 + 0.5) * pixelStep;
      const idx = (py * width + px) * stride;
      const re = doubleToFixedPoint(cr, n);
      const im = doubleToFixedPoint(ci, n);
      c_data.set(re.limbs, idx);
      c_data[idx + n] = re.sign;
      c_data.set(im.limbs, idx + n + 1);
      c_data[idx + 2 * n + 1] = im.sign;
    }
  }

  // Build params: [width, height, max_iters, n_limbs, frac_limbs, thresh_limbs(n)]
  // Escape threshold = 4.0 in fixed-point: integer part = 4 in top limb
  const thresh_limbs = new Uint32Array(n);
  thresh_limbs[n - 1] = 4;
  const paramsData = new Uint32Array(5 + n);
  paramsData[0] = width;
  paramsData[1] = height;
  paramsData[2] = maxIters;
  paramsData[3] = n;
  paramsData[4] = frac_limbs;
  paramsData.set(thresh_limbs, 5);

  // Scratch buffer: signed arithmetic needs more space for signs + intermediates
  const wordsPerThread = 14 * n + 8;
  const scratchSize = totalPixels * wordsPerThread * 4; // bytes
  const iterCountsSize = totalPixels * 4;

  // Create GPU buffers
  const cDataBuf = device.createBuffer({ size: c_data.byteLength, usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST });
  const scratchBuf = device.createBuffer({ size: scratchSize, usage: GPUBufferUsage.STORAGE });
  const iterCountsBuf = device.createBuffer({ size: iterCountsSize, usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC });
  const paramsBuf = device.createBuffer({ size: paramsData.byteLength, usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST });
  const readbackBuf = device.createBuffer({ size: iterCountsSize, usage: GPUBufferUsage.MAP_READ | GPUBufferUsage.COPY_DST });

  device.queue.writeBuffer(cDataBuf, 0, c_data);
  device.queue.writeBuffer(paramsBuf, 0, paramsData);

  const bindGroup = device.createBindGroup({
    layout: pipeline.getBindGroupLayout(0),
    entries: [
      { binding: 0, resource: { buffer: cDataBuf } },
      { binding: 1, resource: { buffer: scratchBuf } },
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
  statusEl.textContent = `Done in ${elapsed.toFixed(0)}ms (${n} limbs, ${maxIters} iters)`;

  // Render to canvas
  const imageData = ctx2d.createImageData(width, height);
  for (let i = 0; i < totalPixels; i++) {
    const iter = iterCounts[i];
    const px = i * 4;
    if (iter >= maxIters) {
      imageData.data[px] = 0;
      imageData.data[px + 1] = 0;
      imageData.data[px + 2] = 0;
      imageData.data[px + 3] = 255;
    } else {
      const t = iter / maxIters;
      const [r, g, b] = hsvToRgb(0.66 + t * 3.0, 0.8, 0.3 + 0.7 * (1 - t));
      imageData.data[px] = r;
      imageData.data[px + 1] = g;
      imageData.data[px + 2] = b;
      imageData.data[px + 3] = 255;
    }
  }
  ctx2d.putImageData(imageData, 0, 0);

  // Clean up
  cDataBuf.destroy();
  scratchBuf.destroy();
  iterCountsBuf.destroy();
  paramsBuf.destroy();
  readbackBuf.destroy();
}

// Click to zoom
canvas.addEventListener('click', (e) => {
  const rect = canvas.getBoundingClientRect();
  const px = (e.clientX - rect.left) / rect.width;
  const py = (e.clientY - rect.top) / rect.height;
  const pixelStep = 3.0 / (zoom * canvas.width);
  centerRe += (px - 0.5) * canvas.width * pixelStep;
  centerIm += (py - 0.5) * canvas.height * pixelStep;
  zoom *= 2;
  render();
});

canvas.addEventListener('contextmenu', (e) => {
  e.preventDefault();
  zoom = Math.max(1, zoom / 2);
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
