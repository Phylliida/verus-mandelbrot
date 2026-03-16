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
        // SSBO for coordinate data
        ssbo_buffer: vk::Buffer,
        ssbo_memory: vk::DeviceMemory,
        ssbo_size: u64,
        ssbo_mapped_ptr: *mut u8,
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
            let (step, _) = f64_to_fp(3.0 / width as f64, n);
            (cre, cre_sign, cim, false, step)
        }

        /// Find a host-visible, host-coherent memory type index.
        fn find_host_visible_memory_type(ctx: &VulkanContext, type_filter: u32) -> u32 {
            let mem_props = unsafe {
                ctx.instance
                    .get_physical_device_memory_properties(ctx.physical_device)
            };
            let desired = vk::MemoryPropertyFlags::HOST_VISIBLE
                | vk::MemoryPropertyFlags::HOST_COHERENT;
            for i in 0..mem_props.memory_type_count {
                if (type_filter & (1 << i)) != 0
                    && mem_props.memory_types[i as usize]
                        .property_flags
                        .contains(desired)
                {
                    return i;
                }
            }
            panic!("No suitable host-visible memory type found");
        }

        /// Create (or recreate) the SSBO buffer for coordinate data.
        /// Size = 3 * max_n * 4 bytes (center_re + center_im + pixel_step).
        fn create_ssbo(ctx: &VulkanContext, max_n: usize) -> (vk::Buffer, vk::DeviceMemory, u64, *mut u8) {
            let size = (3 * max_n * 4) as u64;
            let buf = unsafe {
                ctx.device.create_buffer(
                    &vk::BufferCreateInfo::default()
                        .size(size)
                        .usage(vk::BufferUsageFlags::STORAGE_BUFFER)
                        .sharing_mode(vk::SharingMode::EXCLUSIVE),
                    None,
                )
            }
            .expect("Failed to create SSBO buffer");

            let mem_req = unsafe { ctx.device.get_buffer_memory_requirements(buf) };
            let mem_type_index =
                Self::find_host_visible_memory_type(ctx, mem_req.memory_type_bits);

            let mem = unsafe {
                ctx.device.allocate_memory(
                    &vk::MemoryAllocateInfo::default()
                        .allocation_size(mem_req.size)
                        .memory_type_index(mem_type_index),
                    None,
                )
            }
            .expect("Failed to allocate SSBO memory");

            unsafe { ctx.device.bind_buffer_memory(buf, mem, 0) }
                .expect("Failed to bind SSBO memory");

            let ptr = unsafe {
                ctx.device.map_memory(mem, 0, size, vk::MemoryMapFlags::empty())
            }
            .expect("Failed to map SSBO memory") as *mut u8;

            (buf, mem, size, ptr)
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
            let (ssbo_buffer, ssbo_memory, ssbo_size, ssbo_mapped_ptr) =
                Self::create_ssbo(&ctx, max_n);

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
                    buffer: ssbo_buffer,
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

            eprintln!(
                "Mandelbrot viewer initialized: {}x{}, format {:?}",
                width, height, format
            );
            eprintln!("Controls: WASD/Arrows=pan, +/-=zoom 2x, Left click=recenter");
            eprintln!("          R=reset, C=cycle colors, ]/[=iterations +-50");
            eprintln!("          V=cycle resolution (1x/2x/4x pixel scale)");
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
                ssbo_buffer,
                ssbo_memory,
                ssbo_size,
                ssbo_mapped_ptr,
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
                self.pixel_step = fp_extend(&self.pixel_step, new_n);
            } else {
                self.center_re = fp_truncate(&self.center_re, new_n);
                self.center_im = fp_truncate(&self.center_im, new_n);
                self.pixel_step = fp_truncate(&self.pixel_step, new_n);
            }
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
                    buffer: self.ssbo_buffer,
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
            eprintln!("View reset (N={})", initial_n);
        }

        pub fn zoom_in(&mut self) {
            if fp_is_zero(&self.pixel_step) {
                eprintln!("Precision limit reached!");
                return;
            }
            fp_shr1(&mut self.pixel_step);
            self.zoom_level += 1;

            // Auto-increase N if needed
            let new_n = needed_n(self.zoom_level);
            self.change_n(new_n);

            eprintln!(
                "Zoom: 2^{} | N={} | Iters: {}",
                self.zoom_level, self.current_n, self.max_iters
            );
        }

        pub fn zoom_out(&mut self) {
            fp_shl1(&mut self.pixel_step);
            self.zoom_level -= 1;

            // Auto-decrease N if possible
            let new_n = needed_n(self.zoom_level);
            self.change_n(new_n);

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
            }

            if pan_y != 0.0 {
                let pixels = (pan_speed * dt * self.height as f32).max(1.0) as u32;
                let offset = fp_mul_u32(&self.pixel_step, pixels);
                let (new_im, new_sign) =
                    signed_add(&self.center_im, self.center_im_sign, &offset, pan_y < 0.0);
                self.center_im = new_im;
                self.center_im_sign = new_sign;
            }
        }

        /// Upload coordinate data to the SSBO.
        fn upload_ssbo(&self) {
            let n = self.current_n;
            let coord_bytes = n * 4; // bytes per coordinate array
            let total = 3 * coord_bytes;
            debug_assert!(total as u64 <= self.ssbo_size);

            unsafe {
                let dst = self.ssbo_mapped_ptr;
                // center_re
                std::ptr::copy_nonoverlapping(
                    self.center_re.as_ptr() as *const u8,
                    dst,
                    coord_bytes,
                );
                // center_im
                std::ptr::copy_nonoverlapping(
                    self.center_im.as_ptr() as *const u8,
                    dst.add(coord_bytes),
                    coord_bytes,
                );
                // pixel_step
                std::ptr::copy_nonoverlapping(
                    self.pixel_step.as_ptr() as *const u8,
                    dst.add(2 * coord_bytes),
                    coord_bytes,
                );
            }
        }

        pub fn render(&mut self) {
            self.update_viewport();

            // Wait for GPU to finish before uploading new SSBO data
            // (prevents data race when N changes between frames)
            unsafe {
                let _ = self.ctx.device.device_wait_idle();
            }

            self.upload_ssbo();

            ffi::vk_wait_for_fences(
                &self.ctx,
                &mut self.in_flight_fence,
                Ghost::assume_new(),
                u64::MAX,
            );
            ffi::vk_reset_fences(&self.ctx, &mut self.in_flight_fence);

            let idx = ffi::vk_acquire_next_image(
                &self.ctx,
                &mut self.swapchain,
                self.image_available_sem.handle,
                0,
                u64::MAX,
            );

            let cb = &mut self.command_buffers[idx as usize];
            let image_handle = self.swapchain_images[idx as usize];

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

            // Bind the pipeline for current N
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

            ffi::ffi_cmd_push_constants(
                &self.ctx,
                cb.handle,
                self.pipeline_layout_handle,
                vk::ShaderStageFlags::COMPUTE.as_raw(),
                0,
                pc_bytes,
            );

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
            unsafe {
                let _ = self.ctx.device.device_wait_idle();
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
                // Destroy SSBO
                self.ctx.device.unmap_memory(self.ssbo_memory);
                self.ctx.device.destroy_buffer(self.ssbo_buffer, None);
                self.ctx.device.free_memory(self.ssbo_memory, None);

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
                                    eprintln!("Iterations: {}", vk.max_iters);
                                    self.update_title();
                                }
                                KeyCode::BracketLeft => {
                                    vk.max_iters = vk.max_iters.saturating_sub(50).max(50);
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
            w.set_title(&format!(
                "Mandelbrot — Zoom: 2^{} | N={} ({}-bit) | Iters: {} | {}{}",
                vk.zoom_level,
                vk.current_n,
                vk.current_n * 32,
                vk.max_iters,
                color_name,
                scale_str
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
