//! GPU-accelerated Mandelbrot viewer with dynamic multi-precision fixed-point arithmetic.
//!
//! Automatically increases precision (N_LIMBS) as you zoom in:
//!   N=2  (64-bit)   for zoom < 2^10
//!   N=4  (128-bit)  for zoom < 2^74
//!   N=8  (256-bit)  for zoom < 2^202
//!   N=16 (512-bit)  for zoom < 2^458
//!   N=32 (1024-bit) for zoom < 2^970
//!   N=64 (2048-bit) for zoom < 2^1994
//!
//! Controls:
//!   WASD / Arrows — pan viewport
//!   +/=  -/_     — zoom in/out 2x
//!   Left click    — recenter on clicked pixel
//!   R             — reset to initial view
//!   C             — cycle color palette (HSV / Fire / Ocean)
//!   ] / [         — max_iters +-50 (range 50–10000)
//!   V             — cycle resolution (1x/2x/4x pixel scale)
//!   P             — toggle perturbation mode (float32, ~100x faster)
//!
//! Run: `cargo run --bin mandelbrot_viewer --features viewer`

use std::collections::HashSet;
use winit::{
    application::ApplicationHandler,
    event::{DeviceEvent, DeviceId, WindowEvent},
    event_loop::{ActiveEventLoop, EventLoop},
    keyboard::{KeyCode, PhysicalKey},
    window::{Window, WindowId, WindowAttributes},
};

// Supported N_LIMBS values (must match compiled shader variants).
const SUPPORTED_N: &[usize] = &[2, 4, 8, 16, 32, 64];

/// Choose minimum N_LIMBS for a given zoom level (2^zoom_level magnification).
/// Each limb gives 32 fractional bits of precision. limb[0] is integer part,
/// so fractional bits = (N-1)*32. We want fractional bits > zoom_level + ~10 guard bits.
fn needed_n(zoom_level: i32) -> usize {
    if zoom_level < 0 {
        return SUPPORTED_N[0];
    }
    let bits_needed = zoom_level as usize + 10;
    let limbs_needed = bits_needed / 32 + 2; // +1 for integer limb, +1 for rounding
    for &n in SUPPORTED_N {
        if n >= limbs_needed {
            return n;
        }
    }
    *SUPPORTED_N.last().unwrap()
}

/// Auto-select iteration count based on zoom level.
/// Uses the standard heuristic: iters ≈ 50 * sqrt(2^zoom), clamped to [256, 10000].
fn needed_iters(zoom_level: i32) -> u32 {
    if zoom_level <= 0 {
        return 256;
    }
    // 50 * 2^(zoom/2) = 50 * sqrt(2^zoom)
    let iters = 50.0 * (2.0f64).powf(zoom_level as f64 / 2.0);
    (iters as u32).clamp(256, 10000)
}

fn n_index(n: usize) -> usize {
    SUPPORTED_N.iter().position(|&x| x == n).unwrap()
}

// ═══════════════════════════════════════════════════════════════════════════
// Multi-precision fixed-point helpers (MSB-first limbs, matching GLSL shader)
//
// Format: limb[0] = integer part, limb[1..N-1] = fractional bits
// Value = limb[0] + limb[1]/2^32 + limb[2]/2^64 + ... + limb[N-1]/2^(32*(N-1))
// ═══════════════════════════════════════════════════════════════════════════

/// Create a zero-valued N-limb fixed-point number.
fn fp_zero(n: usize) -> Vec<u32> {
    vec![0u32; n]
}

/// Convert f64 to N-limb fixed-point magnitude + sign.
/// Precision is limited by f64's 52-bit mantissa (sufficient for initialization).
fn f64_to_fp(val: f64, n: usize) -> (Vec<u32>, bool) {
    let sign = val < 0.0;
    let abs_val = val.abs();
    let int_part = abs_val as u64;
    let mut frac = abs_val - int_part as f64;

    let mut limbs = vec![0u32; n];
    limbs[0] = int_part as u32;
    for i in 1..n {
        frac *= 4294967296.0; // 2^32
        let limb_val = frac as u64;
        limbs[i] = limb_val as u32;
        frac -= limb_val as f64;
    }
    (limbs, sign)
}

/// Unsigned addition: r = a + b (carry discarded).
fn fp_add(a: &[u32], b: &[u32]) -> Vec<u32> {
    let n = a.len();
    debug_assert_eq!(n, b.len());
    let mut r = vec![0u32; n];
    let mut carry = 0u64;
    for i in (0..n).rev() {
        let sum = a[i] as u64 + b[i] as u64 + carry;
        r[i] = sum as u32;
        carry = sum >> 32;
    }
    r
}

/// Unsigned subtraction: r = a - b (assumes a >= b).
fn fp_sub(a: &[u32], b: &[u32]) -> Vec<u32> {
    let n = a.len();
    debug_assert_eq!(n, b.len());
    let mut r = vec![0u32; n];
    let mut borrow = 0i64;
    for i in (0..n).rev() {
        let diff = a[i] as i64 - b[i] as i64 - borrow;
        if diff < 0 {
            r[i] = (diff + (1i64 << 32)) as u32;
            borrow = 1;
        } else {
            r[i] = diff as u32;
            borrow = 0;
        }
    }
    r
}

/// Unsigned comparison: true if a >= b.
fn fp_ge(a: &[u32], b: &[u32]) -> bool {
    for i in 0..a.len() {
        if a[i] > b[i] { return true; }
        if a[i] < b[i] { return false; }
    }
    true
}

/// Check if all limbs are zero.
fn fp_is_zero(a: &[u32]) -> bool {
    a.iter().all(|&x| x == 0)
}

/// Right-shift by 1 bit (zoom in = halve pixel_step).
fn fp_shr1(a: &mut [u32]) {
    let n = a.len();
    for i in (1..n).rev() {
        a[i] = (a[i] >> 1) | (a[i - 1] << 31);
    }
    a[0] >>= 1;
}

/// Left-shift by 1 bit (zoom out = double pixel_step).
fn fp_shl1(a: &mut [u32]) {
    let n = a.len();
    for i in 0..n - 1 {
        a[i] = (a[i] << 1) | (a[i + 1] >> 31);
    }
    a[n - 1] <<= 1;
}

/// Multiply N-limb value by a u32 scalar.
fn fp_mul_u32(a: &[u32], scalar: u32) -> Vec<u32> {
    let n = a.len();
    let mut r = vec![0u32; n];
    let mut carry = 0u64;
    for i in (0..n).rev() {
        let prod = a[i] as u64 * scalar as u64 + carry;
        r[i] = prod as u32;
        carry = prod >> 32;
    }
    r
}

/// Sign-magnitude addition.
fn signed_add(a: &[u32], a_sign: bool, b: &[u32], b_sign: bool) -> (Vec<u32>, bool) {
    if a_sign == b_sign {
        (fp_add(a, b), a_sign)
    } else if fp_ge(a, b) {
        (fp_sub(a, b), a_sign)
    } else {
        (fp_sub(b, a), b_sign)
    }
}

/// Full-precision multiply of two N-limb fixed-point numbers.
/// Result is N limbs (truncated to same precision).
/// Both inputs are unsigned magnitudes; caller handles signs.
fn fp_mul(a: &[u32], b: &[u32]) -> Vec<u32> {
    let n = a.len();
    debug_assert_eq!(n, b.len());
    // Use u128 accumulators to avoid overflow with large N.
    let mut acc = vec![0u128; 2 * n];
    for i in (0..n).rev() {
        for j in (0..n).rev() {
            let prod = a[i] as u128 * b[j] as u128;
            let pos = i + j;
            if pos < 2 * n {
                acc[pos] += prod;
            }
        }
    }
    // Propagate carries from LSB to MSB
    for i in (1..2 * n).rev() {
        acc[i - 1] += acc[i] >> 32;
        acc[i] &= 0xFFFF_FFFF;
    }
    let mut r = vec![0u32; n];
    for i in 0..n {
        r[i] = acc[i] as u32;
    }
    r
}

/// Signed multiply: returns (|a*b|, sign).
fn signed_mul(a: &[u32], a_sign: bool, b: &[u32], b_sign: bool) -> (Vec<u32>, bool) {
    (fp_mul(a, b), a_sign != b_sign)
}

/// Extend limbs from old_n to new_n (pad with zeros on LSB side).
fn fp_extend(a: &[u32], new_n: usize) -> Vec<u32> {
    let mut r = vec![0u32; new_n];
    let copy_len = a.len().min(new_n);
    r[..copy_len].copy_from_slice(&a[..copy_len]);
    r
}

/// Truncate limbs from old_n to new_n (drop LSB limbs).
fn fp_truncate(a: &[u32], new_n: usize) -> Vec<u32> {
    a[..new_n].to_vec()
}

// ═══════════════════════════════════════════════════════════════════════════
// Vulkan backend
// ═══════════════════════════════════════════════════════════════════════════

mod vulkan {
    use super::*;
    use ash::vk;
    use ash::vk::Handle;
    use builtin::Ghost;
    use raw_window_handle::{HasDisplayHandle, HasWindowHandle};
    use std::sync::Arc;
    use std::time::Instant;
    use verus_vulkan::ffi;
    use verus_vulkan::runtime::command_buffer::RuntimeCommandBuffer;
    use verus_vulkan::runtime::command_pool::RuntimeCommandPool;
    use verus_vulkan::runtime::descriptor::{
        RuntimeDescriptorPool, RuntimeDescriptorSet, RuntimeDescriptorSetLayout,
    };
    use verus_vulkan::runtime::device::RuntimeDevice;
    use verus_vulkan::runtime::fence::RuntimeFence;
    use verus_vulkan::runtime::framebuffer::RuntimeImageView;
    use verus_vulkan::runtime::pipeline::RuntimeComputePipeline;
    use verus_vulkan::runtime::queue::RuntimeQueue;
    use verus_vulkan::runtime::semaphore::RuntimeSemaphore;
    use verus_vulkan::runtime::shader_module::RuntimeShaderModule;
    use verus_vulkan::runtime::surface::RuntimeSurface;
    use verus_vulkan::runtime::swapchain::RuntimeSwapchain;
    use verus_vulkan::runtime::mapped_buffer::{RuntimeMappedBuffer, reclaim_buffer, release_buffer, write_mapped_buffer};
    use verus_vulkan::vk_context::VulkanContext;

    // Push constants: only scalar parameters (28 bytes, N-independent).
    // Coordinate data goes in SSBO.
    #[repr(C)]
    struct PushConstants {
        width: u32,
        height: u32,
        max_iters: u32,
        cre_sign: u32,
        cim_sign: u32,
        color_mode: u32,
        pixel_scale: u32,
    }

    // Push constants for perturbation shader (52 bytes).
    #[repr(C)]
    struct PerturbPushConstants {
        width: u32,
        height: u32,
        max_iters: u32,
        ref_orbit_len: u32,
        pixel_step_re: f32,
        pixel_step_im: f32,
        color_mode: u32,
        pixel_scale: u32,
        ref_offset_px_re: f32,  // offset from screen center to ref point, in pixels
        ref_offset_px_im: f32,
        sa_re: f32,        // SA coefficient * pixel_step (real part)
        sa_im: f32,        // SA coefficient * pixel_step (imag part)
        skip_iters: u32,   // iterations to skip via SA
    }

    /// Per-N pipeline variant resources.
    struct PipelineVariant {
        n_limbs: usize,
        shader_module: RuntimeShaderModule,
        compute_pipeline: RuntimeComputePipeline,
    }

    pub struct VkState {
        ctx: VulkanContext,
        _dev: RuntimeDevice,
        raw_surface: vk::SurfaceKHR,
        _surface: RuntimeSurface,
        queue: RuntimeQueue,
        swapchain: RuntimeSwapchain,
        swapchain_images: Vec<u64>,
        image_views: Vec<RuntimeImageView>,
        // One pipeline per supported N
        pipelines: Vec<PipelineVariant>,
        current_n_index: usize,
        pipeline_layout_handle: u64,
        descriptor_set_layout: RuntimeDescriptorSetLayout,
        descriptor_pool: RuntimeDescriptorPool,
        descriptor_sets: Vec<RuntimeDescriptorSet>,
        // SSBO for coordinate data (ownership-tracked)
        ssbo: RuntimeMappedBuffer,
        command_pool: RuntimeCommandPool,
        command_buffers: Vec<RuntimeCommandBuffer>,
        image_available_sem: RuntimeSemaphore,
        render_finished_sem: RuntimeSemaphore,
        in_flight_fence: RuntimeFence,
        _format: vk::Format,
        width: u32,
        height: u32,
        // Viewport state (sign-magnitude, Vec<u32> MSB-first)
        pub center_re: Vec<u32>,
        pub center_im: Vec<u32>,
        pub center_re_sign: bool,
        pub center_im_sign: bool,
        pub pixel_step: Vec<u32>,
        pub current_n: usize,
        pub max_iters: u32,
        pub color_mode: u32,
        pub pixel_scale: u32,
        pub zoom_level: i32,
        // Perturbation mode
        pub perturbation_mode: bool,
        perturb_pipeline_layout: u64,
        perturb_shader_module: RuntimeShaderModule,
        perturb_pipeline: RuntimeComputePipeline,
        // Reference orbit SSBO (ownership-tracked)
        ref_orbit: RuntimeMappedBuffer,
        ref_orbit_len: u32,
        ref_offset_re: f32,  // offset from screen center to reference point
        ref_offset_im: f32,
        sa_re: f32,          // SA coefficient * pixel_step (real part)
        sa_im: f32,          // SA coefficient * pixel_step (imag part)
        skip_iters: u32,     // iterations to skip via SA
        pub ref_orbit_dirty: bool,
        // Perturbation descriptor sets (bind ref_orbit SSBO at binding 1)
        perturb_descriptor_pool: RuntimeDescriptorPool,
        perturb_descriptor_sets: Vec<RuntimeDescriptorSet>,
        // Input
        pub keys_held: HashSet<KeyCode>,
        pub last_frame_time: Instant,
        pub cursor_pos: (f64, f64),
    }

    impl VkState {
        /// Initial view: center = (-0.5, 0.0), view width = 3.0 Mandelbrot units
        fn initial_view(width: u32, n: usize) -> (Vec<u32>, bool, Vec<u32>, bool, Vec<u32>) {
            let (cre, cre_sign) = f64_to_fp(-0.5, n);
            let (cim, _) = f64_to_fp(0.0, n);
            let step = Self::compute_pixel_step(width, 0, n);
            (cre, cre_sign, cim, false, step)
        }

        /// Compute pixel_step at given zoom level with full precision in n limbs.
        /// pixel_step = (3.0 / width) / 2^zoom_level
        fn compute_pixel_step(width: u32, zoom_level: i32, n: usize) -> Vec<u32> {
            let (step, _) = f64_to_fp(3.0 / width as f64, n);
            if zoom_level <= 0 {
                return step;
            }
            // Bulk shift: zoom_level bits right = (zoom_level/32) full limbs + (zoom_level%32) bits
            let limb_shift = zoom_level as usize / 32;
            let bit_shift = zoom_level as u32 % 32;
            if limb_shift >= n {
                return fp_zero(n);
            }
            // Shift whole limbs first
            let mut shifted = fp_zero(n);
            for i in limb_shift..n {
                shifted[i] = step[i - limb_shift];
            }
            // Then shift remaining bits
            if bit_shift > 0 {
                let mut carry = 0u32;
                for i in 0..n {
                    let val = shifted[i];
                    shifted[i] = (val >> bit_shift) | carry;
                    carry = val << (32 - bit_shift);
                }
            }
            shifted
        }

        pub fn new(window: Arc<Window>) -> Self {
            let size = window.inner_size();
            let width = size.width.max(1);
            let height = size.height.max(1);

            let display_handle = window.display_handle().unwrap();
            let surface_extensions =
                ash_window::enumerate_required_extensions(display_handle.as_raw())
                    .expect("Failed to get required surface extensions");
            let device_exts: Vec<*const i8> = vec![ash::khr::swapchain::NAME.as_ptr()];

            let ctx = unsafe {
                VulkanContext::new(
                    "mandelbrot_viewer",
                    true,
                    surface_extensions,
                    &device_exts,
                    0,
                )
            };

            let raw_surface = unsafe {
                ash_window::create_surface(
                    &ctx.entry,
                    &ctx.instance,
                    display_handle.as_raw(),
                    window.window_handle().unwrap().as_raw(),
                    None,
                )
            }
            .expect("Failed to create Vulkan surface");
            let surface = ffi::vk_create_surface(&ctx, Ghost::assume_new(), raw_surface.as_raw());

            let dev = ffi::vk_create_device(&ctx, Ghost::assume_new());
            let queue = ffi::vk_get_device_queue(&ctx, 0, 0, Ghost::assume_new());

            let surface_formats = unsafe {
                ctx.surface_loader
                    .get_physical_device_surface_formats(ctx.physical_device, raw_surface)
            }
            .expect("Failed to query surface formats");
            let format = surface_formats
                .iter()
                .find(|f| f.format == vk::Format::B8G8R8A8_UNORM)
                .unwrap_or(&surface_formats[0])
                .format;

            let image_count = 2u64;
            let swapchain = ffi::vk_create_swapchain(
                &ctx,
                Ghost::assume_new(),
                image_count,
                raw_surface.as_raw(),
                format.as_raw() as u32,
                width,
                height,
                vk::PresentModeKHR::FIFO.as_raw() as u32,
                (vk::ImageUsageFlags::STORAGE | vk::ImageUsageFlags::COLOR_ATTACHMENT).as_raw(),
            );

            let swapchain_images = ffi::vk_get_swapchain_images(&ctx, &swapchain);
            let mut image_views = Vec::new();
            for &img in swapchain_images.iter() {
                let view = ffi::vk_create_image_view(
                    &ctx,
                    Ghost::assume_new(),
                    img,
                    format.as_raw() as u32,
                    vk::ImageAspectFlags::COLOR.as_raw() as u32,
                );
                image_views.push(view);
            }

            // Descriptor set layout: binding 0 = storage image, binding 1 = storage buffer (SSBO)
            let descriptor_set_layout = ffi::vk_create_descriptor_set_layout_typed(
                &ctx,
                Ghost::assume_new(),
                &[
                    (
                        0,
                        vk::DescriptorType::STORAGE_IMAGE.as_raw() as u32,
                        1,
                        vk::ShaderStageFlags::COMPUTE.as_raw(),
                    ),
                    (
                        1,
                        vk::DescriptorType::STORAGE_BUFFER.as_raw() as u32,
                        1,
                        vk::ShaderStageFlags::COMPUTE.as_raw(),
                    ),
                ],
            );

            // Pipeline layout with push constants (28 bytes for scalars)
            let pipeline_layout_handle = ffi::vk_create_pipeline_layout_push(
                &ctx,
                &[descriptor_set_layout.handle],
                vk::ShaderStageFlags::COMPUTE.as_raw(),
                0,
                std::mem::size_of::<PushConstants>() as u32,
            );

            // Load all 6 shader variants
            let shader_spvs: [&[u8]; 6] = [
                include_bytes!("shaders/mandelbrot_n2.comp.spv"),
                include_bytes!("shaders/mandelbrot_n4.comp.spv"),
                include_bytes!("shaders/mandelbrot_n8.comp.spv"),
                include_bytes!("shaders/mandelbrot_n16.comp.spv"),
                include_bytes!("shaders/mandelbrot_n32.comp.spv"),
                include_bytes!("shaders/mandelbrot_n64.comp.spv"),
            ];

            let mut pipelines = Vec::new();
            for (i, &spv_bytes) in shader_spvs.iter().enumerate() {
                let spv_code = spv_to_u32(spv_bytes);
                let shader_module =
                    ffi::vk_create_shader_module(&ctx, Ghost::assume_new(), &spv_code);
                let compute_pipeline = ffi::vk_create_compute_pipeline(
                    &ctx,
                    Ghost::assume_new(),
                    pipeline_layout_handle,
                    shader_module.handle,
                );
                pipelines.push(PipelineVariant {
                    n_limbs: SUPPORTED_N[i],
                    shader_module,
                    compute_pipeline,
                });
            }

            // Create SSBO (sized for max N=64)
            let max_n = *SUPPORTED_N.last().unwrap();
            let ssbo = ffi::vk_create_mapped_buffer(
                &ctx,
                Ghost::assume_new(),
                (3 * max_n * 4) as u64,
                vk::BufferUsageFlags::STORAGE_BUFFER.as_raw(),
            );

            // Descriptor pool: STORAGE_IMAGE + STORAGE_BUFFER per swapchain image
            let mut descriptor_pool = ffi::vk_create_descriptor_pool_typed(
                &ctx,
                Ghost::assume_new(),
                image_count,
                &[
                    (
                        vk::DescriptorType::STORAGE_IMAGE.as_raw() as u32,
                        image_count as u32,
                    ),
                    (
                        vk::DescriptorType::STORAGE_BUFFER.as_raw() as u32,
                        image_count as u32,
                    ),
                ],
            );

            let mut descriptor_sets = Vec::new();
            for i in 0..image_count as usize {
                let mut ds = ffi::vk_allocate_descriptor_sets(
                    &ctx,
                    &mut descriptor_pool,
                    Ghost::assume_new(),
                    Ghost::assume_new(),
                    descriptor_set_layout.handle,
                );
                // Bind storage image (binding 0)
                ffi::vk_update_descriptor_sets_image(
                    &ctx,
                    &mut ds,
                    Ghost::assume_new(),
                    Ghost::assume_new(),
                    0,
                    vk::DescriptorType::STORAGE_IMAGE.as_raw() as u32,
                    image_views[i].handle,
                    vk::ImageLayout::GENERAL.as_raw() as u32,
                );
                // Bind storage buffer (binding 1)
                let bi = [vk::DescriptorBufferInfo {
                    buffer: vk::Buffer::from_raw(ssbo.handle),
                    offset: 0,
                    range: vk::WHOLE_SIZE,
                }];
                let w = vk::WriteDescriptorSet::default()
                    .dst_set(vk::DescriptorSet::from_raw(ds.handle))
                    .dst_binding(1)
                    .descriptor_type(vk::DescriptorType::STORAGE_BUFFER)
                    .buffer_info(&bi);
                unsafe { ctx.device.update_descriptor_sets(&[w], &[]) };
                descriptor_sets.push(ds);
            }

            let command_pool = ffi::vk_create_command_pool(&ctx, Ghost::assume_new(), 0, true);
            let mut command_buffers = Vec::new();
            for _ in 0..image_count as usize {
                let cb = ffi::vk_allocate_command_buffer(
                    &ctx,
                    Ghost::assume_new(),
                    command_pool.handle,
                );
                command_buffers.push(cb);
            }

            let in_flight_fence = ffi::vk_create_fence(&ctx, Ghost::assume_new(), true);
            let image_available_sem = ffi::vk_create_semaphore(&ctx, Ghost::assume_new());
            let render_finished_sem = ffi::vk_create_semaphore(&ctx, Ghost::assume_new());

            let initial_n = SUPPORTED_N[0];
            let (cre, cre_sign, cim, cim_sign, step) = Self::initial_view(width, initial_n);

            // ── Perturbation pipeline ─────────────────────────────────
            // Perturbation shader has different push constants (32 bytes)
            let perturb_pipeline_layout = ffi::vk_create_pipeline_layout_push(
                &ctx,
                &[descriptor_set_layout.handle],
                vk::ShaderStageFlags::COMPUTE.as_raw(),
                0,
                std::mem::size_of::<PerturbPushConstants>() as u32,
            );

            let perturb_spv = include_bytes!("shaders/mandelbrot_perturb.comp.spv");
            let perturb_spv_code = spv_to_u32(perturb_spv);
            let perturb_shader_module =
                ffi::vk_create_shader_module(&ctx, Ghost::assume_new(), &perturb_spv_code);
            let perturb_pipeline = ffi::vk_create_compute_pipeline(
                &ctx,
                Ghost::assume_new(),
                perturb_pipeline_layout,
                perturb_shader_module.handle,
            );

            // Reference orbit SSBO: max 10000 orbit points * 2 floats * 4 bytes = 80KB
            let ref_orbit = ffi::vk_create_mapped_buffer(
                &ctx,
                Ghost::assume_new(),
                (10000 * 2 * 4) as u64,
                vk::BufferUsageFlags::STORAGE_BUFFER.as_raw(),
            );

            // Perturbation descriptor pool + sets (bind ref orbit SSBO)
            let mut perturb_descriptor_pool = ffi::vk_create_descriptor_pool_typed(
                &ctx,
                Ghost::assume_new(),
                image_count,
                &[
                    (
                        vk::DescriptorType::STORAGE_IMAGE.as_raw() as u32,
                        image_count as u32,
                    ),
                    (
                        vk::DescriptorType::STORAGE_BUFFER.as_raw() as u32,
                        image_count as u32,
                    ),
                ],
            );

            let mut perturb_descriptor_sets = Vec::new();
            for i in 0..image_count as usize {
                let mut ds = ffi::vk_allocate_descriptor_sets(
                    &ctx,
                    &mut perturb_descriptor_pool,
                    Ghost::assume_new(),
                    Ghost::assume_new(),
                    descriptor_set_layout.handle,
                );
                // Binding 0: storage image (same as bigint)
                ffi::vk_update_descriptor_sets_image(
                    &ctx,
                    &mut ds,
                    Ghost::assume_new(),
                    Ghost::assume_new(),
                    0,
                    vk::DescriptorType::STORAGE_IMAGE.as_raw() as u32,
                    image_views[i].handle,
                    vk::ImageLayout::GENERAL.as_raw() as u32,
                );
                // Binding 1: ref orbit SSBO
                let bi = [vk::DescriptorBufferInfo {
                    buffer: vk::Buffer::from_raw(ref_orbit.handle),
                    offset: 0,
                    range: vk::WHOLE_SIZE,
                }];
                let w = vk::WriteDescriptorSet::default()
                    .dst_set(vk::DescriptorSet::from_raw(ds.handle))
                    .dst_binding(1)
                    .descriptor_type(vk::DescriptorType::STORAGE_BUFFER)
                    .buffer_info(&bi);
                unsafe { ctx.device.update_descriptor_sets(&[w], &[]) };
                perturb_descriptor_sets.push(ds);
            }

            eprintln!(
                "Mandelbrot viewer initialized: {}x{}, format {:?}",
                width, height, format
            );
            eprintln!("Controls: WASD/Arrows=pan, +/-=zoom 2x, Left click=recenter");
            eprintln!("          R=reset, C=cycle colors, ]/[=iterations +-50");
            eprintln!("          V=cycle resolution, P=toggle perturbation mode");
            eprintln!("Dynamic precision: N={} ({}-bit)", initial_n, initial_n * 32);

            VkState {
                ctx,
                _dev: dev,
                raw_surface,
                _surface: surface,
                queue,
                swapchain,
                swapchain_images,
                image_views,
                pipelines,
                current_n_index: 0,
                pipeline_layout_handle,
                descriptor_set_layout,
                descriptor_pool,
                descriptor_sets,
                ssbo,
                command_pool,
                command_buffers,
                image_available_sem,
                render_finished_sem,
                in_flight_fence,
                _format: format,
                width,
                height,
                center_re: cre,
                center_im: cim,
                center_re_sign: cre_sign,
                center_im_sign: cim_sign,
                pixel_step: step,
                current_n: initial_n,
                max_iters: 256,
                color_mode: 0,
                pixel_scale: 2,
                zoom_level: 0,
                perturbation_mode: false,
                perturb_pipeline_layout,
                perturb_shader_module,
                perturb_pipeline,
                ref_orbit,
                ref_orbit_len: 0,
                ref_offset_re: 0.0,
                ref_offset_im: 0.0,
                sa_re: 0.0,
                sa_im: 0.0,
                skip_iters: 0,
                ref_orbit_dirty: true,
                perturb_descriptor_pool,
                perturb_descriptor_sets,
                keys_held: HashSet::new(),
                last_frame_time: Instant::now(),
                cursor_pos: (0.0, 0.0),
            }
        }

        /// Change N_LIMBS: extend or truncate coordinate vectors.
        fn change_n(&mut self, new_n: usize) {
            if new_n == self.current_n {
                return;
            }
            if new_n > self.current_n {
                self.center_re = fp_extend(&self.center_re, new_n);
                self.center_im = fp_extend(&self.center_im, new_n);
            } else {
                self.center_re = fp_truncate(&self.center_re, new_n);
                self.center_im = fp_truncate(&self.center_im, new_n);
            }
            // Recompute pixel_step at new N with full f64 precision
            self.pixel_step = Self::compute_pixel_step(self.width, self.zoom_level, new_n);
            self.current_n = new_n;
            self.current_n_index = n_index(new_n);
            eprintln!(
                "Precision: N={} ({}-bit, ~{} decimal digits)",
                new_n,
                new_n * 32,
                (new_n - 1) * 32 * 3 / 10 // approximate decimal digits from fractional bits
            );
        }

        pub fn resize(&mut self, width: u32, height: u32) {
            if width == 0 || height == 0 {
                return;
            }
            unsafe { let _ = self.ctx.device.device_wait_idle(); }

            // Destroy old swapchain resources
            unsafe {
                self.ctx.device.destroy_descriptor_pool(
                    vk::DescriptorPool::from_raw(self.descriptor_pool.handle),
                    None,
                );
                for iv in &self.image_views {
                    self.ctx
                        .device
                        .destroy_image_view(vk::ImageView::from_raw(iv.handle), None);
                }
                self.ctx
                    .swapchain_loader
                    .destroy_swapchain(vk::SwapchainKHR::from_raw(self.swapchain.handle), None);
            }

            self.width = width;
            self.height = height;

            let image_count = 2u64;
            self.swapchain = ffi::vk_create_swapchain(
                &self.ctx,
                Ghost::assume_new(),
                image_count,
                self.raw_surface.as_raw(),
                self._format.as_raw() as u32,
                width,
                height,
                vk::PresentModeKHR::FIFO.as_raw() as u32,
                (vk::ImageUsageFlags::STORAGE | vk::ImageUsageFlags::COLOR_ATTACHMENT).as_raw(),
            );

            self.swapchain_images = ffi::vk_get_swapchain_images(&self.ctx, &self.swapchain);
            self.image_views.clear();
            for &img in self.swapchain_images.iter() {
                let view = ffi::vk_create_image_view(
                    &self.ctx,
                    Ghost::assume_new(),
                    img,
                    self._format.as_raw() as u32,
                    vk::ImageAspectFlags::COLOR.as_raw() as u32,
                );
                self.image_views.push(view);
            }

            self.descriptor_pool = ffi::vk_create_descriptor_pool_typed(
                &self.ctx,
                Ghost::assume_new(),
                image_count,
                &[
                    (
                        vk::DescriptorType::STORAGE_IMAGE.as_raw() as u32,
                        image_count as u32,
                    ),
                    (
                        vk::DescriptorType::STORAGE_BUFFER.as_raw() as u32,
                        image_count as u32,
                    ),
                ],
            );
            self.descriptor_sets.clear();
            for i in 0..image_count as usize {
                let mut ds = ffi::vk_allocate_descriptor_sets(
                    &self.ctx,
                    &mut self.descriptor_pool,
                    Ghost::assume_new(),
                    Ghost::assume_new(),
                    self.descriptor_set_layout.handle,
                );
                ffi::vk_update_descriptor_sets_image(
                    &self.ctx,
                    &mut ds,
                    Ghost::assume_new(),
                    Ghost::assume_new(),
                    0,
                    vk::DescriptorType::STORAGE_IMAGE.as_raw() as u32,
                    self.image_views[i].handle,
                    vk::ImageLayout::GENERAL.as_raw() as u32,
                );
                let bi = [vk::DescriptorBufferInfo {
                    buffer: vk::Buffer::from_raw(self.ssbo.handle),
                    offset: 0,
                    range: vk::WHOLE_SIZE,
                }];
                let w = vk::WriteDescriptorSet::default()
                    .dst_set(vk::DescriptorSet::from_raw(ds.handle))
                    .dst_binding(1)
                    .descriptor_type(vk::DescriptorType::STORAGE_BUFFER)
                    .buffer_info(&bi);
                unsafe { self.ctx.device.update_descriptor_sets(&[w], &[]) };
                self.descriptor_sets.push(ds);
            }

            // Recreate perturbation descriptor sets (they reference image views)
            unsafe {
                self.ctx.device.destroy_descriptor_pool(
                    vk::DescriptorPool::from_raw(self.perturb_descriptor_pool.handle),
                    None,
                );
            }
            self.perturb_descriptor_pool = ffi::vk_create_descriptor_pool_typed(
                &self.ctx,
                Ghost::assume_new(),
                image_count,
                &[
                    (
                        vk::DescriptorType::STORAGE_IMAGE.as_raw() as u32,
                        image_count as u32,
                    ),
                    (
                        vk::DescriptorType::STORAGE_BUFFER.as_raw() as u32,
                        image_count as u32,
                    ),
                ],
            );
            self.perturb_descriptor_sets.clear();
            for i in 0..image_count as usize {
                let mut ds = ffi::vk_allocate_descriptor_sets(
                    &self.ctx,
                    &mut self.perturb_descriptor_pool,
                    Ghost::assume_new(),
                    Ghost::assume_new(),
                    self.descriptor_set_layout.handle,
                );
                ffi::vk_update_descriptor_sets_image(
                    &self.ctx,
                    &mut ds,
                    Ghost::assume_new(),
                    Ghost::assume_new(),
                    0,
                    vk::DescriptorType::STORAGE_IMAGE.as_raw() as u32,
                    self.image_views[i].handle,
                    vk::ImageLayout::GENERAL.as_raw() as u32,
                );
                let bi = [vk::DescriptorBufferInfo {
                    buffer: vk::Buffer::from_raw(self.ref_orbit.handle),
                    offset: 0,
                    range: vk::WHOLE_SIZE,
                }];
                let w = vk::WriteDescriptorSet::default()
                    .dst_set(vk::DescriptorSet::from_raw(ds.handle))
                    .dst_binding(1)
                    .descriptor_type(vk::DescriptorType::STORAGE_BUFFER)
                    .buffer_info(&bi);
                unsafe { self.ctx.device.update_descriptor_sets(&[w], &[]) };
                self.perturb_descriptor_sets.push(ds);
            }

            eprintln!("Resized: {}x{}", width, height);
        }

        pub fn reset_view(&mut self) {
            let initial_n = SUPPORTED_N[0];
            let (cre, cre_sign, cim, cim_sign, step) = Self::initial_view(self.width, initial_n);
            self.center_re = cre;
            self.center_re_sign = cre_sign;
            self.center_im = cim;
            self.center_im_sign = cim_sign;
            self.pixel_step = step;
            self.current_n = initial_n;
            self.current_n_index = 0;
            self.zoom_level = 0;
            self.max_iters = 256;
            self.ref_orbit_dirty = true;
            eprintln!("View reset (N={})", initial_n);
        }

        pub fn zoom_in(&mut self) {
            if fp_is_zero(&self.pixel_step) {
                eprintln!("Precision limit reached!");
                return;
            }
            fp_shr1(&mut self.pixel_step);
            self.zoom_level += 1;
            self.ref_orbit_dirty = true;

            // Auto-increase N and iterations
            let new_n = needed_n(self.zoom_level);
            self.change_n(new_n);
            self.max_iters = needed_iters(self.zoom_level);

            eprintln!(
                "Zoom: 2^{} | N={} | Iters: {}",
                self.zoom_level, self.current_n, self.max_iters
            );
        }

        pub fn zoom_out(&mut self) {
            fp_shl1(&mut self.pixel_step);
            self.zoom_level -= 1;
            self.ref_orbit_dirty = true;

            // Auto-decrease N and iterations
            let new_n = needed_n(self.zoom_level);
            self.change_n(new_n);
            self.max_iters = needed_iters(self.zoom_level);

            eprintln!(
                "Zoom: 2^{} | N={} | Iters: {}",
                self.zoom_level, self.current_n, self.max_iters
            );
        }

        pub fn recenter_on_click(&mut self) {
            let dx = self.cursor_pos.0 as i32 - (self.width / 2) as i32;
            let dy = self.cursor_pos.1 as i32 - (self.height / 2) as i32;

            if dx != 0 {
                let offset = fp_mul_u32(&self.pixel_step, dx.unsigned_abs());
                let (new_re, new_sign) =
                    signed_add(&self.center_re, self.center_re_sign, &offset, dx < 0);
                self.center_re = new_re;
                self.center_re_sign = new_sign;
            }

            if dy != 0 {
                let offset = fp_mul_u32(&self.pixel_step, dy.unsigned_abs());
                let (new_im, new_sign) =
                    signed_add(&self.center_im, self.center_im_sign, &offset, dy > 0);
                self.center_im = new_im;
                self.center_im_sign = new_sign;
            }

            self.ref_orbit_dirty = true;
        }

        pub fn update_viewport(&mut self) {
            let dt = self.last_frame_time.elapsed().as_secs_f32();
            self.last_frame_time = Instant::now();

            let pan_speed = 1.0f32;

            let pan_x = if self.keys_held.contains(&KeyCode::KeyD)
                || self.keys_held.contains(&KeyCode::ArrowRight)
            {
                1.0f32
            } else if self.keys_held.contains(&KeyCode::KeyA)
                || self.keys_held.contains(&KeyCode::ArrowLeft)
            {
                -1.0
            } else {
                0.0
            };

            let pan_y = if self.keys_held.contains(&KeyCode::KeyW)
                || self.keys_held.contains(&KeyCode::ArrowUp)
            {
                1.0f32
            } else if self.keys_held.contains(&KeyCode::KeyS)
                || self.keys_held.contains(&KeyCode::ArrowDown)
            {
                -1.0
            } else {
                0.0
            };

            if pan_x != 0.0 {
                let pixels = (pan_speed * dt * self.width as f32).max(1.0) as u32;
                let offset = fp_mul_u32(&self.pixel_step, pixels);
                let (new_re, new_sign) =
                    signed_add(&self.center_re, self.center_re_sign, &offset, pan_x < 0.0);
                self.center_re = new_re;
                self.center_re_sign = new_sign;
                self.ref_orbit_dirty = true;
            }

            if pan_y != 0.0 {
                let pixels = (pan_speed * dt * self.height as f32).max(1.0) as u32;
                let offset = fp_mul_u32(&self.pixel_step, pixels);
                let (new_im, new_sign) =
                    signed_add(&self.center_im, self.center_im_sign, &offset, pan_y < 0.0);
                self.center_im = new_im;
                self.center_im_sign = new_sign;
                self.ref_orbit_dirty = true;
            }
        }

        /// Convert sign-magnitude fixed-point limbs to f64.
        fn fp_to_f64(limbs: &[u32], sign: bool) -> f64 {
            let mut val = limbs[0] as f64;
            for i in 1..limbs.len() {
                let scale = (4294967296.0f64).powi(i as i32);
                if scale.is_infinite() { break; }
                val += limbs[i] as f64 / scale;
            }
            if sign { -val } else { val }
        }

        /// Compute a single reference orbit in full-precision fixed-point.
        /// Returns (orbit_f32_pairs, iteration_count, sa_coeffs) where sa_coeffs
        /// is a Vec of (A_re, A_im) f64 pairs for Series Approximation.
        fn compute_ref_orbit_fp(
            cr: &[u32], cr_sign: bool,
            ci: &[u32], ci_sign: bool,
            max_pts: usize,
        ) -> (Vec<f32>, usize, Vec<(f64, f64)>) {
            let n = cr.len();
            let mut orbit: Vec<f32> = Vec::with_capacity(max_pts * 2);
            let mut sa_coeffs: Vec<(f64, f64)> = Vec::with_capacity(max_pts);
            let mut zr = fp_zero(n);
            let mut zr_sign = false;
            let mut zi = fp_zero(n);
            let mut zi_sign = false;
            let mut iters = 0usize;

            // SA coefficient: A_{n+1} = 2*Z_n*A_n + 1, A_0 = 0
            let mut a_re = 0.0f64;
            let mut a_im = 0.0f64;

            // Escape threshold: |z|² > 4 means integer limb >= 5
            // (conservative: check if zr² + zi² integer part > 4)
            let four = {
                let mut v = fp_zero(n);
                v[0] = 4;
                v
            };

            for _ in 0..max_pts {
                // Convert current z to f64 for SA computation
                let z_re_f64 = Self::fp_to_f64(&zr, zr_sign);
                let z_im_f64 = Self::fp_to_f64(&zi, zi_sign);

                // Store orbit point as f32
                orbit.push(z_re_f64 as f32);
                orbit.push(z_im_f64 as f32);

                // Store SA coefficient for this iteration
                sa_coeffs.push((a_re, a_im));

                iters += 1;

                // Update SA: A_{n+1} = 2*Z_n*A_n + 1
                // Re: 2*(Z_re*A_re - Z_im*A_im) + 1
                // Im: 2*(Z_re*A_im + Z_im*A_re)
                let new_a_re = 2.0 * (z_re_f64 * a_re - z_im_f64 * a_im) + 1.0;
                let new_a_im = 2.0 * (z_re_f64 * a_im + z_im_f64 * a_re);
                a_re = new_a_re;
                a_im = new_a_im;

                // z = z² + c
                // new_zr = zr² - zi² + cr
                // new_zi = 2·zr·zi + ci
                let (zr2, zr2_sign) = signed_mul(&zr, zr_sign, &zr, zr_sign); // zr², always positive
                let (zi2, zi2_sign) = signed_mul(&zi, zi_sign, &zi, zi_sign); // zi², always positive
                let (zrzi, zrzi_sign) = signed_mul(&zr, zr_sign, &zi, zi_sign);
                let two_zrzi = fp_add(&zrzi, &zrzi); // 2·zr·zi (unsigned double)

                // new_zr = (zr² - zi²) + cr
                let (diff, diff_sign) = signed_add(&zr2, zr2_sign, &zi2, !zi2_sign);
                let (new_zr, new_zr_sign) = signed_add(&diff, diff_sign, cr, cr_sign);

                // new_zi = 2·zr·zi + ci
                let (new_zi, new_zi_sign) = signed_add(&two_zrzi, zrzi_sign, ci, ci_sign);

                zr = new_zr;
                zr_sign = new_zr_sign;
                zi = new_zi;
                zi_sign = new_zi_sign;

                // Escape check: |z|² > 4
                // zr² + zi² (both positive after squaring)
                let mag2 = fp_add(&fp_mul(&zr, &zr), &fp_mul(&zi, &zi));
                if fp_ge(&mag2, &four) {
                    break;
                }
            }
            (orbit, iters, sa_coeffs)
        }

        /// Quick escape test: returns iteration count before escape (up to probe_iters).
        fn probe_escape_fp(
            cr: &[u32], cr_sign: bool,
            ci: &[u32], ci_sign: bool,
            probe_iters: usize,
        ) -> usize {
            let n = cr.len();
            let mut zr = fp_zero(n);
            let mut zr_sign = false;
            let mut zi = fp_zero(n);
            let mut zi_sign = false;
            let four = { let mut v = fp_zero(n); v[0] = 4; v };

            for iter in 0..probe_iters {
                let zr2 = fp_mul(&zr, &zr);
                let zi2 = fp_mul(&zi, &zi);
                let mag2 = fp_add(&zr2, &zi2);
                if fp_ge(&mag2, &four) {
                    return iter;
                }
                let zrzi = fp_mul(&zr, &zi);
                let zrzi_sign = zr_sign != zi_sign;
                let two_zrzi = fp_add(&zrzi, &zrzi);
                let (diff, diff_sign) = signed_add(&zr2, false, &zi2, true);
                let (new_zr, new_zr_sign) = signed_add(&diff, diff_sign, cr, cr_sign);
                let (new_zi, new_zi_sign) = signed_add(&two_zrzi, zrzi_sign, ci, ci_sign);
                zr = new_zr; zr_sign = new_zr_sign;
                zi = new_zi; zi_sign = new_zi_sign;
            }
            probe_iters // survived all iterations
        }

        /// Compute reference orbit in full-precision fixed-point and upload to SSBO.
        /// Uses hill-climbing on the iteration count landscape: samples 8 neighbors,
        /// moves toward higher iteration counts, halves step size when stuck.
        /// This quickly converges toward the Mandelbrot set interior.
        fn compute_and_upload_ref_orbit(&mut self) {
            let max_pts = (self.max_iters as usize).min(10000);
            let probe_iters = max_pts.min(500);

            // Current best position (start at screen center)
            let mut cur_re = self.center_re.clone();
            let mut cur_re_sign = self.center_re_sign;
            let mut cur_im = self.center_im.clone();
            let mut cur_im_sign = self.center_im_sign;
            let mut cur_iters = Self::probe_escape_fp(
                &cur_re, cur_re_sign, &cur_im, cur_im_sign, probe_iters,
            );
            // Track pixel offset from screen center
            let mut offset_re_px = 0.0f64;
            let mut offset_im_px = 0.0f64;

            // Initial step: quarter viewport in pixels
            let mut step_pixels = self.width.max(self.height) as f64 / 4.0;
            // 8 directions: N, NE, E, SE, S, SW, W, NW
            let dirs: [(f64, f64); 8] = [
                (0.0, 1.0), (1.0, 1.0), (1.0, 0.0), (1.0, -1.0),
                (0.0, -1.0), (-1.0, -1.0), (-1.0, 0.0), (-1.0, 1.0),
            ];

            let mut steps_taken = 0u32;
            while cur_iters < probe_iters && step_pixels >= 1.0 {
                let step_u32 = step_pixels as u32;
                if step_u32 == 0 { break; }
                let fp_step = fp_mul_u32(&self.pixel_step, step_u32);

                let mut improved = false;
                for &(ddx, ddy) in &dirs {
                    // Compute candidate = cur + (ddx, ddy) * fp_step
                    let (cr, cr_sign) = if ddx == 0.0 {
                        (cur_re.clone(), cur_re_sign)
                    } else {
                        let off = if ddx.abs() > 1.5 {
                            fp_add(&fp_step, &fp_step)
                        } else {
                            fp_step.clone()
                        };
                        signed_add(&cur_re, cur_re_sign, &off, ddx < 0.0)
                    };
                    let (ci, ci_sign) = if ddy == 0.0 {
                        (cur_im.clone(), cur_im_sign)
                    } else {
                        let off = if ddy.abs() > 1.5 {
                            fp_add(&fp_step, &fp_step)
                        } else {
                            fp_step.clone()
                        };
                        // positive ddy = math upward = add to im
                        signed_add(&cur_im, cur_im_sign, &off, ddy < 0.0)
                    };

                    let iters = Self::probe_escape_fp(
                        &cr, cr_sign, &ci, ci_sign, probe_iters,
                    );
                    if iters > cur_iters {
                        cur_re = cr;
                        cur_re_sign = cr_sign;
                        cur_im = ci;
                        cur_im_sign = ci_sign;
                        cur_iters = iters;
                        offset_re_px += ddx * step_pixels;
                        offset_im_px += ddy * step_pixels;
                        improved = true;
                        steps_taken += 1;
                        if cur_iters >= probe_iters {
                            break;
                        }
                    }
                }
                if !improved {
                    step_pixels /= 2.0;
                }
            }

            // Compute the full orbit at the best point found
            let (mut best_orbit, best_iters, sa_coeffs) = Self::compute_ref_orbit_fp(
                &cur_re, cur_re_sign, &cur_im, cur_im_sign, max_pts,
            );

            self.ref_offset_re = offset_re_px as f32;
            self.ref_offset_im = offset_im_px as f32;
            self.ref_orbit_len = (best_orbit.len() / 2) as u32;

            // Compute SA skip
            let pixel_step_f64 = Self::fp_to_f64(&self.pixel_step, false);
            let max_offset = self.width.max(self.height) as f64 / 2.0;

            // Use SA whenever pixel_step itself would be subnormal in f32.
            // GPUs flush subnormals to zero BEFORE multiplication, so even if
            // pixel_step * max_offset would be normal, the GPU computes px * 0 = 0.
            let needs_sa = pixel_step_f64 < f32::MIN_POSITIVE as f64;

            if !needs_sa {
                // pixel_step produces normal f32 values, no SA needed
                self.sa_re = 0.0;
                self.sa_im = 0.0;
                self.skip_iters = 0;
            } else {
                // Find the best SA skip point. We need:
                //   |A_skip * pixel_step| to be a normal f32 (not subnormal)
                // so the GPU doesn't flush it to zero. The sa value gets multiplied
                // by pixel offsets up to max_offset in the shader, producing δ.
                // We want |sa| itself to be normal so per-pixel differences survive.
                let sa_normal_threshold = f32::MIN_POSITIVE as f64;

                // Find the iteration where |A| * pixel_step first produces a normal f32
                let mut skip_n = 0usize;
                let mut best_skip = 0usize;
                let mut best_sa_mag = 0.0f64;
                for (i, &(a_re, a_im)) in sa_coeffs.iter().enumerate() {
                    let sa_re_f64 = a_re * pixel_step_f64;
                    let sa_im_f64 = a_im * pixel_step_f64;
                    let sa_mag = sa_re_f64.abs().max(sa_im_f64.abs());

                    if sa_mag >= sa_normal_threshold && skip_n == 0 {
                        skip_n = i;
                    }
                    // Track the largest |sa| that still fits in f32
                    // (stop if A overflows or sa would exceed f32 range)
                    if sa_mag > best_sa_mag && sa_mag < f32::MAX as f64 * 0.5 {
                        best_sa_mag = sa_mag;
                        best_skip = i;
                    }
                }

                // Use the first iteration where sa is normal; fall back to best available
                if skip_n == 0 && best_skip > 0 {
                    skip_n = best_skip;
                }

                if skip_n > 0 {
                    let (a_re, a_im) = sa_coeffs[skip_n];
                    self.sa_re = (a_re * pixel_step_f64) as f32;
                    self.sa_im = (a_im * pixel_step_f64) as f32;
                    self.skip_iters = skip_n as u32;
                    eprintln!(
                        "SA: skip {} iters, sa=({:e}, {:e}), pixel_step_f64={:e}, |A|={:e}",
                        skip_n, self.sa_re, self.sa_im, pixel_step_f64,
                        sa_coeffs[skip_n].0.hypot(sa_coeffs[skip_n].1),
                    );
                } else {
                    // A never exceeded threshold — interior point with tiny A.
                    // Use A=1 equivalent: just pass pixel_step scaled up slightly.
                    // This won't produce great images but avoids total black.
                    self.sa_re = 0.0;
                    self.sa_im = 0.0;
                    self.skip_iters = 0;
                    eprintln!(
                        "SA: no valid skip found (pixel_step_f64={:e}, orbit_len={}, max |A|={:e})",
                        pixel_step_f64, sa_coeffs.len(), best_sa_mag / pixel_step_f64,
                    );
                }
            }

            // Upload to SSBO (clamp to buffer size)
            let max_floats = (self.ref_orbit.size / 4) as usize;
            if best_orbit.len() > max_floats {
                best_orbit.truncate(max_floats);
                self.ref_orbit_len = (max_floats / 2) as u32;
            }
            let src: &[u8] = bytemuck::cast_slice(&best_orbit);
            write_mapped_buffer(&self.ref_orbit, src, 0);

            self.ref_orbit_dirty = false;
            eprintln!(
                "Ref orbit: {} iters (max {}), offset: ({:.0}, {:.0}) px, {} steps, SA skip: {}",
                best_iters, max_pts, offset_re_px, offset_im_px, steps_taken, self.skip_iters,
            );
        }

        /// Upload coordinate data to the SSBO.
        fn upload_ssbo(&self) {
            let n = self.current_n;
            let coord_bytes = n * 4; // bytes per coordinate array
            let total = 3 * coord_bytes;
            debug_assert!(total as u64 <= self.ssbo.size);

            let src_re: &[u8] = bytemuck::cast_slice(&self.center_re);
            write_mapped_buffer(&self.ssbo, src_re, 0);
            let src_im: &[u8] = bytemuck::cast_slice(&self.center_im);
            write_mapped_buffer(&self.ssbo, src_im, coord_bytes);
            let src_step: &[u8] = bytemuck::cast_slice(&self.pixel_step);
            write_mapped_buffer(&self.ssbo, src_step, 2 * coord_bytes);
        }

        pub fn render(&mut self) {
            self.update_viewport();

            // Wait for previous frame's GPU work to complete before touching resources
            ffi::vk_wait_for_fences(
                &self.ctx,
                &mut self.in_flight_fence,
                Ghost::assume_new(),
                u64::MAX,
            );
            // Reclaim both SSBOs — fence@.signaled proved by vk_wait_for_fences
            reclaim_buffer(&mut self.ssbo, &self.in_flight_fence);
            reclaim_buffer(&mut self.ref_orbit, &self.in_flight_fence);

            ffi::vk_reset_fences(&self.ctx, &mut self.in_flight_fence);

            // Now safe to write SSBO data — HostOwned proved by reclaim_buffer
            if self.perturbation_mode {
                if self.ref_orbit_dirty {
                    self.compute_and_upload_ref_orbit();
                }
            } else {
                self.upload_ssbo();
            }

            // Release both SSBOs before GPU submission
            release_buffer(&mut self.ssbo);
            release_buffer(&mut self.ref_orbit);

            let idx = ffi::vk_acquire_next_image(
                &self.ctx,
                &mut self.swapchain,
                self.image_available_sem.handle,
                0,
                u64::MAX,
            );

            let cb = &mut self.command_buffers[idx as usize];
            let image_handle = self.swapchain_images[idx as usize];

            ffi::vk_begin_command_buffer(&self.ctx, cb);

            // UNDEFINED -> GENERAL
            ffi::vk_cmd_pipeline_barrier_image(
                &self.ctx,
                cb,
                Ghost::assume_new(),
                vk::PipelineStageFlags::TOP_OF_PIPE.as_raw(),
                vk::PipelineStageFlags::COMPUTE_SHADER.as_raw(),
                &[(
                    image_handle,
                    vk::ImageLayout::UNDEFINED.as_raw() as u32,
                    vk::ImageLayout::GENERAL.as_raw() as u32,
                    vk::AccessFlags::empty().as_raw(),
                    vk::AccessFlags::SHADER_WRITE.as_raw(),
                )],
            );

            if self.perturbation_mode {
                // ── Perturbation render path ──
                ffi::vk_cmd_bind_pipeline(
                    &self.ctx,
                    cb,
                    vk::PipelineBindPoint::COMPUTE.as_raw() as u32,
                    self.perturb_pipeline.handle,
                );

                ffi::vk_cmd_bind_descriptor_sets(
                    &self.ctx,
                    cb,
                    Ghost::assume_new(),
                    vk::PipelineBindPoint::COMPUTE.as_raw() as u32,
                    self.perturb_pipeline_layout,
                    0,
                    &[self.perturb_descriptor_sets[idx as usize].handle],
                );

                // Compute pixel step as f32 from fixed-point
                let pixel_step_f64 = Self::fp_to_f64(&self.pixel_step, false);
                let ppc = PerturbPushConstants {
                    width: self.width,
                    height: self.height,
                    max_iters: self.max_iters,
                    ref_orbit_len: self.ref_orbit_len,
                    pixel_step_re: pixel_step_f64 as f32,
                    pixel_step_im: pixel_step_f64 as f32,
                    color_mode: self.color_mode,
                    pixel_scale: self.pixel_scale,
                    ref_offset_px_re: self.ref_offset_re,
                    ref_offset_px_im: self.ref_offset_im,
                    sa_re: self.sa_re,
                    sa_im: self.sa_im,
                    skip_iters: self.skip_iters,
                };
                let pc_bytes: &[u8] = unsafe {
                    std::slice::from_raw_parts(
                        &ppc as *const PerturbPushConstants as *const u8,
                        std::mem::size_of::<PerturbPushConstants>(),
                    )
                };
                ffi::ffi_cmd_push_constants(
                    &self.ctx,
                    cb.handle,
                    self.perturb_pipeline_layout,
                    vk::ShaderStageFlags::COMPUTE.as_raw(),
                    0,
                    pc_bytes,
                );
            } else {
                // ── Bigint render path ──
                let pipeline = &self.pipelines[self.current_n_index];
                ffi::vk_cmd_bind_pipeline(
                    &self.ctx,
                    cb,
                    vk::PipelineBindPoint::COMPUTE.as_raw() as u32,
                    pipeline.compute_pipeline.handle,
                );

                ffi::vk_cmd_bind_descriptor_sets(
                    &self.ctx,
                    cb,
                    Ghost::assume_new(),
                    vk::PipelineBindPoint::COMPUTE.as_raw() as u32,
                    self.pipeline_layout_handle,
                    0,
                    &[self.descriptor_sets[idx as usize].handle],
                );

                let pc = PushConstants {
                    width: self.width,
                    height: self.height,
                    max_iters: self.max_iters,
                    cre_sign: if self.center_re_sign { 1 } else { 0 },
                    cim_sign: if self.center_im_sign { 1 } else { 0 },
                    color_mode: self.color_mode,
                    pixel_scale: self.pixel_scale,
                };
                let pc_bytes: &[u8] = unsafe {
                    std::slice::from_raw_parts(
                        &pc as *const PushConstants as *const u8,
                        std::mem::size_of::<PushConstants>(),
                    )
                };
                ffi::ffi_cmd_push_constants(
                    &self.ctx,
                    cb.handle,
                    self.pipeline_layout_handle,
                    vk::ShaderStageFlags::COMPUTE.as_raw(),
                    0,
                    pc_bytes,
                );
            }

            let s = self.pixel_scale.max(1);
            let group_x = ((self.width + s - 1) / s + 15) / 16;
            let group_y = ((self.height + s - 1) / s + 15) / 16;
            ffi::vk_cmd_dispatch(&self.ctx, cb, group_x, group_y, 1);

            // GENERAL -> PRESENT_SRC_KHR
            ffi::vk_cmd_pipeline_barrier_image(
                &self.ctx,
                cb,
                Ghost::assume_new(),
                vk::PipelineStageFlags::COMPUTE_SHADER.as_raw(),
                vk::PipelineStageFlags::BOTTOM_OF_PIPE.as_raw(),
                &[(
                    image_handle,
                    vk::ImageLayout::GENERAL.as_raw() as u32,
                    vk::ImageLayout::PRESENT_SRC_KHR.as_raw() as u32,
                    vk::AccessFlags::SHADER_WRITE.as_raw(),
                    vk::AccessFlags::empty().as_raw(),
                )],
            );

            ffi::vk_end_command_buffer(&self.ctx, cb);

            let wait_stage = vk::PipelineStageFlags::COMPUTE_SHADER.as_raw();
            ffi::vk_queue_submit(
                &self.ctx,
                &self.queue,
                Ghost::assume_new(),
                Ghost::assume_new(),
                Ghost::assume_new(),
                &[cb.handle],
                &[self.image_available_sem.handle],
                &[wait_stage],
                &[self.render_finished_sem.handle],
                self.in_flight_fence.handle,
            );

            ffi::vk_queue_present_khr(
                &self.ctx,
                &self.queue,
                &mut self.swapchain,
                idx,
                &[self.render_finished_sem.handle],
            );
        }

        pub fn destroy(&mut self) {
            unsafe { let _ = self.ctx.device.device_wait_idle(); }

            // After device_wait_idle, fence is conceptually signaled.
            // Wait on it to prove fence@.signaled for reclaim.
            ffi::vk_wait_for_fences(
                &self.ctx,
                &mut self.in_flight_fence,
                Ghost::assume_new(),
                u64::MAX,
            );

            // Reclaim SSBOs so they are HostOwned (required for destroy)
            reclaim_buffer(&mut self.ssbo, &self.in_flight_fence);
            reclaim_buffer(&mut self.ref_orbit, &self.in_flight_fence);

            // Move SSBOs out and destroy via FFI
            let ssbo = std::mem::replace(&mut self.ssbo, RuntimeMappedBuffer {
                handle: 0, mem_handle: 0, mapped_ptr: 0, size: 0,
                state: Ghost::assume_new(),
            });
            ffi::vk_destroy_mapped_buffer(&self.ctx, ssbo);

            let ref_orbit = std::mem::replace(&mut self.ref_orbit, RuntimeMappedBuffer {
                handle: 0, mem_handle: 0, mapped_ptr: 0, size: 0,
                state: Ghost::assume_new(),
            });
            ffi::vk_destroy_mapped_buffer(&self.ctx, ref_orbit);

            unsafe {
                for pv in &self.pipelines {
                    self.ctx.device.destroy_pipeline(
                        vk::Pipeline::from_raw(pv.compute_pipeline.handle),
                        None,
                    );
                    self.ctx.device.destroy_shader_module(
                        vk::ShaderModule::from_raw(pv.shader_module.handle),
                        None,
                    );
                }
                self.ctx.device.destroy_pipeline_layout(
                    vk::PipelineLayout::from_raw(self.pipeline_layout_handle),
                    None,
                );
                self.ctx.device.destroy_descriptor_pool(
                    vk::DescriptorPool::from_raw(self.descriptor_pool.handle),
                    None,
                );
                self.ctx.device.destroy_descriptor_set_layout(
                    vk::DescriptorSetLayout::from_raw(self.descriptor_set_layout.handle),
                    None,
                );

                // Destroy perturbation resources
                self.ctx.device.destroy_pipeline(
                    vk::Pipeline::from_raw(self.perturb_pipeline.handle),
                    None,
                );
                self.ctx.device.destroy_shader_module(
                    vk::ShaderModule::from_raw(self.perturb_shader_module.handle),
                    None,
                );
                self.ctx.device.destroy_pipeline_layout(
                    vk::PipelineLayout::from_raw(self.perturb_pipeline_layout),
                    None,
                );
                self.ctx.device.destroy_descriptor_pool(
                    vk::DescriptorPool::from_raw(self.perturb_descriptor_pool.handle),
                    None,
                );

                for iv in &self.image_views {
                    self.ctx
                        .device
                        .destroy_image_view(vk::ImageView::from_raw(iv.handle), None);
                }
                self.ctx.device.destroy_command_pool(
                    vk::CommandPool::from_raw(self.command_pool.handle),
                    None,
                );
                self.ctx
                    .device
                    .destroy_fence(vk::Fence::from_raw(self.in_flight_fence.handle), None);
                self.ctx.device.destroy_semaphore(
                    vk::Semaphore::from_raw(self.image_available_sem.handle),
                    None,
                );
                self.ctx.device.destroy_semaphore(
                    vk::Semaphore::from_raw(self.render_finished_sem.handle),
                    None,
                );
                self.ctx
                    .swapchain_loader
                    .destroy_swapchain(vk::SwapchainKHR::from_raw(self.swapchain.handle), None);
                self.ctx
                    .surface_loader
                    .destroy_surface(self.raw_surface, None);
                self.ctx.destroy();
            }
        }
    }

    fn spv_to_u32(bytes: &[u8]) -> Vec<u32> {
        bytes
            .chunks_exact(4)
            .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
            .collect()
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Application handler
// ═══════════════════════════════════════════════════════════════════════════

struct App {
    window: Option<std::sync::Arc<Window>>,
    state: Option<vulkan::VkState>,
}

impl ApplicationHandler for App {
    fn resumed(&mut self, event_loop: &ActiveEventLoop) {
        if self.window.is_some() {
            return;
        }
        let attrs =
            WindowAttributes::default().with_title("Mandelbrot — Zoom: 2^0 | N=2 | Iters: 256");
        let window = std::sync::Arc::new(
            event_loop
                .create_window(attrs)
                .expect("Failed to create window"),
        );
        self.window = Some(window.clone());
        self.state = Some(vulkan::VkState::new(window.clone()));
        window.request_redraw();
    }

    fn window_event(
        &mut self,
        event_loop: &ActiveEventLoop,
        _id: WindowId,
        event: WindowEvent,
    ) {
        match event {
            WindowEvent::CloseRequested => {
                event_loop.exit();
            }
            WindowEvent::Resized(size) => {
                if let Some(ref mut vk) = self.state {
                    vk.resize(size.width, size.height);
                }
            }
            WindowEvent::CursorMoved { position, .. } => {
                if let Some(ref mut vk) = self.state {
                    vk.cursor_pos = (position.x, position.y);
                }
            }
            WindowEvent::MouseInput {
                state: winit::event::ElementState::Pressed,
                button: winit::event::MouseButton::Left,
                ..
            } => {
                if let Some(ref mut vk) = self.state {
                    vk.recenter_on_click();
                    self.update_title();
                }
            }
            WindowEvent::KeyboardInput { event, .. } => {
                if let PhysicalKey::Code(key) = event.physical_key {
                    let pressed = event.state == winit::event::ElementState::Pressed;
                    if let Some(ref mut vk) = self.state {
                        if pressed {
                            vk.keys_held.insert(key);
                        } else {
                            vk.keys_held.remove(&key);
                        }

                        if pressed && !event.repeat {
                            match key {
                                KeyCode::Equal | KeyCode::NumpadAdd => {
                                    vk.zoom_in();
                                    self.update_title();
                                }
                                KeyCode::Minus | KeyCode::NumpadSubtract => {
                                    vk.zoom_out();
                                    self.update_title();
                                }
                                KeyCode::BracketRight => {
                                    vk.max_iters = (vk.max_iters + 50).min(10000);
                                    vk.ref_orbit_dirty = true;
                                    eprintln!("Iterations: {}", vk.max_iters);
                                    self.update_title();
                                }
                                KeyCode::BracketLeft => {
                                    vk.max_iters = vk.max_iters.saturating_sub(50).max(50);
                                    vk.ref_orbit_dirty = true;
                                    eprintln!("Iterations: {}", vk.max_iters);
                                    self.update_title();
                                }
                                KeyCode::KeyR => {
                                    vk.reset_view();
                                    self.update_title();
                                }
                                KeyCode::KeyV => {
                                    vk.pixel_scale = match vk.pixel_scale {
                                        1 => 2,
                                        2 => 4,
                                        _ => 1,
                                    };
                                    eprintln!("Pixel scale: {}x", vk.pixel_scale);
                                    self.update_title();
                                }
                                KeyCode::KeyC => {
                                    vk.color_mode = (vk.color_mode + 1) % 3;
                                    let name = match vk.color_mode {
                                        0 => "HSV",
                                        1 => "Fire",
                                        _ => "Ocean",
                                    };
                                    eprintln!("Color: {}", name);
                                    self.update_title();
                                }
                                KeyCode::KeyP => {
                                    vk.perturbation_mode = !vk.perturbation_mode;
                                    vk.ref_orbit_dirty = true;
                                    let mode = if vk.perturbation_mode {
                                        "PERTURBATION (float32)"
                                    } else {
                                        "BIGINT (multi-precision)"
                                    };
                                    eprintln!("Mode: {}", mode);
                                    self.update_title();
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
            WindowEvent::RedrawRequested => {
                if let Some(ref mut vk) = self.state {
                    vk.render();
                }
                if let Some(w) = &self.window {
                    w.request_redraw();
                }
            }
            _ => {}
        }
    }

    fn device_event(
        &mut self,
        _event_loop: &ActiveEventLoop,
        _device_id: DeviceId,
        _event: DeviceEvent,
    ) {
    }
}

impl App {
    fn update_title(&self) {
        if let (Some(w), Some(vk)) = (&self.window, &self.state) {
            let color_name = match vk.color_mode {
                0 => "HSV",
                1 => "Fire",
                _ => "Ocean",
            };
            let scale_str = if vk.pixel_scale > 1 {
                format!(" | {}x scale", vk.pixel_scale)
            } else {
                String::new()
            };
            let mode_str = if vk.perturbation_mode {
                " | PERTURB"
            } else {
                ""
            };
            w.set_title(&format!(
                "Mandelbrot — Zoom: 2^{} | N={} ({}-bit) | Iters: {} | {}{}{}",
                vk.zoom_level,
                vk.current_n,
                vk.current_n * 32,
                vk.max_iters,
                color_name,
                scale_str,
                mode_str,
            ));
        }
    }
}

fn main() {
    let event_loop = EventLoop::new().expect("Failed to create event loop");
    let mut app = App {
        window: None,
        state: None,
    };
    let _ = event_loop.run_app(&mut app);
    if let Some(ref mut vk) = app.state {
        vk.destroy();
    }
}
