//! GPU shader profiler for the verified Mandelbrot compute shader.
//!
//! Runs the WGSL shader headlessly with various parameter configurations,
//! measures GPU execution time via timestamp queries (or wall-clock fallback),
//! and prints a summary table.
//!
//! Usage:
//!   cargo run --bin profile_shader --features profiler [-- OPTIONS]
//!
//! Options:
//!   --wgsl PATH       Path to WGSL file (default: web/mandelbrot_verified.wgsl)
//!   --limbs N[,N,...]  Limb counts to test (default: 4,8)
//!   --res W[,W,...]    Resolutions to test (default: 64,128,256)
//!   --iters N[,N,...]  Max iteration counts (default: 50,100,200)
//!   --runs N           Runs per config for timing stability (default: 3)
//!   --warmup N         Warmup runs before measurement (default: 1)
//!   --csv              Output CSV instead of table

use std::path::PathBuf;
use std::time::Instant;

fn double_to_fixed_point(val: f64, n: usize) -> (Vec<u32>, u32) {
    let sign = if val < 0.0 { 1u32 } else { 0u32 };
    let mut abs_val = val.abs();
    let mut limbs = vec![0u32; n];
    for i in (0..n).rev() {
        let limb = abs_val as u32;
        limbs[i] = limb;
        abs_val = (abs_val - limb as f64) * 4294967296.0;
    }
    (limbs, sign)
}

struct Config {
    wgsl_path: PathBuf,
    limbs: Vec<u32>,
    resolutions: Vec<u32>,
    iters: Vec<u32>,
    runs: u32,
    warmup: u32,
    csv: bool,
}

fn parse_args() -> Config {
    let args: Vec<String> = std::env::args().collect();
    let mut cfg = Config {
        wgsl_path: PathBuf::from("web/mandelbrot_verified.wgsl"),
        limbs: vec![4, 8],
        resolutions: vec![64, 128, 256],
        iters: vec![50, 100, 200],
        runs: 3,
        warmup: 1,
        csv: false,
    };

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--wgsl" => {
                i += 1;
                cfg.wgsl_path = PathBuf::from(&args[i]);
            }
            "--limbs" => {
                i += 1;
                cfg.limbs = args[i].split(',').map(|s| s.trim().parse().unwrap()).collect();
            }
            "--res" => {
                i += 1;
                cfg.resolutions = args[i].split(',').map(|s| s.trim().parse().unwrap()).collect();
            }
            "--iters" => {
                i += 1;
                cfg.iters = args[i].split(',').map(|s| s.trim().parse().unwrap()).collect();
            }
            "--runs" => {
                i += 1;
                cfg.runs = args[i].parse().unwrap();
            }
            "--warmup" => {
                i += 1;
                cfg.warmup = args[i].parse().unwrap();
            }
            "--csv" => {
                cfg.csv = true;
            }
            other => {
                eprintln!("Unknown option: {other}");
                std::process::exit(1);
            }
        }
        i += 1;
    }
    cfg
}

struct TimingResult {
    n_limbs: u32,
    resolution: u32,
    max_iters: u32,
    total_pixels: u32,
    wall_ms: Vec<f64>,
    gpu_ms: Vec<f64>, // empty if timestamps unavailable
}

impl TimingResult {
    fn wall_stats(&self) -> (f64, f64, f64) {
        stats(&self.wall_ms)
    }
    fn gpu_stats(&self) -> Option<(f64, f64, f64)> {
        if self.gpu_ms.is_empty() {
            None
        } else {
            Some(stats(&self.gpu_ms))
        }
    }
}

fn stats(v: &[f64]) -> (f64, f64, f64) {
    let mut sorted = v.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min = sorted[0];
    let max = sorted[sorted.len() - 1];
    let median = sorted[sorted.len() / 2];
    (min, median, max)
}

fn main() {
    let cfg = parse_args();

    // Read shader
    let wgsl = match std::fs::read_to_string(&cfg.wgsl_path) {
        Ok(s) => s,
        Err(e) => {
            // Try relative to crate root
            let alt = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(&cfg.wgsl_path);
            match std::fs::read_to_string(&alt) {
                Ok(s) => s,
                Err(_) => {
                    eprintln!("Cannot read WGSL: {} (tried {} and {})", e, cfg.wgsl_path.display(), alt.display());
                    std::process::exit(1);
                }
            }
        }
    };
    eprintln!("Loaded {} lines of WGSL from {}", wgsl.lines().count(), cfg.wgsl_path.display());

    // Init wgpu
    let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor {
        backends: wgpu::Backends::all(),
        ..Default::default()
    });

    let (device, queue, has_timestamps) = pollster::block_on(async {
        let adapter = instance
            .request_adapter(&wgpu::RequestAdapterOptions {
                power_preference: wgpu::PowerPreference::HighPerformance,
                ..Default::default()
            })
            .await
            .expect("No GPU adapter found");

        eprintln!("Adapter: {}", adapter.get_info().name);
        eprintln!("Backend: {:?}", adapter.get_info().backend);

        let has_ts = adapter.features().contains(wgpu::Features::TIMESTAMP_QUERY);
        eprintln!("Timestamp queries: {}", if has_ts { "YES" } else { "NO (wall-clock only)" });

        let mut required_features = wgpu::Features::empty();
        if has_ts {
            required_features |= wgpu::Features::TIMESTAMP_QUERY;
        }

        let (device, queue) = adapter
            .request_device(&wgpu::DeviceDescriptor {
                label: Some("profiler"),
                required_features,
                required_limits: wgpu::Limits {
                    max_storage_buffer_binding_size: 512 * 1024 * 1024,
                    max_buffer_size: 512 * 1024 * 1024,
                    ..Default::default()
                },
                ..Default::default()
            }, None)
            .await
            .expect("Failed to create device");

        (device, queue, has_ts)
    });

    // Compile shader once
    let shader_module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
        label: Some("mandelbrot"),
        source: wgpu::ShaderSource::Wgsl(wgsl.into()),
    });

    let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
        label: Some("mandelbrot"),
        layout: None,
        module: &shader_module,
        entry_point: Some("mandelbrot_fixedpoint"),
        compilation_options: Default::default(),
        cache: None,
    });

    // Run configs
    let total_configs = cfg.limbs.len() * cfg.resolutions.len() * cfg.iters.len();
    eprintln!("\nProfiling {} configurations ({} warmup + {} measured runs each)\n",
        total_configs, cfg.warmup, cfg.runs);

    let mut results = Vec::new();

    for &n in &cfg.limbs {
        for &res in &cfg.resolutions {
            for &max_iters in &cfg.iters {
                let result = run_config(
                    &device, &queue, &pipeline, has_timestamps,
                    n, res, max_iters, cfg.warmup, cfg.runs,
                );
                let (_, median, _) = result.wall_stats();
                let gpu_str = match result.gpu_stats() {
                    Some((_, m, _)) => format!(", gpu={:.2}ms", m),
                    None => String::new(),
                };
                eprintln!("  n={:2} res={:4} iters={:4} → wall={:.2}ms{}",
                    n, res, max_iters, median, gpu_str);
                results.push(result);
            }
        }
    }

    // Print results
    eprintln!();
    if cfg.csv {
        print_csv(&results, has_timestamps);
    } else {
        print_table(&results, has_timestamps);
    }
}

fn run_config(
    device: &wgpu::Device,
    queue: &wgpu::Queue,
    pipeline: &wgpu::ComputePipeline,
    has_timestamps: bool,
    n: u32,
    resolution: u32,
    max_iters: u32,
    warmup: u32,
    runs: u32,
) -> TimingResult {
    let width = resolution;
    let height = resolution;
    let total_pixels = width * height;
    let frac_limbs = n - 1;

    // Build c_data: per pixel [re_limbs(n), re_sign(1), im_limbs(n), im_sign(1)]
    let stride = 2 * n + 2;
    let mut c_data = vec![0u32; (total_pixels * stride) as usize];
    let pixel_step = 3.0 / width as f64;
    let center_re = -0.5;
    let center_im = 0.0;

    for py in 0..height {
        for px in 0..width {
            let cr = center_re + (px as f64 - width as f64 / 2.0 + 0.5) * pixel_step;
            let ci = center_im + (py as f64 - height as f64 / 2.0 + 0.5) * pixel_step;
            let idx = ((py * width + px) * stride) as usize;
            let (re_limbs, re_sign) = double_to_fixed_point(cr, n as usize);
            let (im_limbs, im_sign) = double_to_fixed_point(ci, n as usize);
            c_data[idx..idx + n as usize].copy_from_slice(&re_limbs);
            c_data[idx + n as usize] = re_sign;
            c_data[idx + n as usize + 1..idx + 2 * n as usize + 1].copy_from_slice(&im_limbs);
            c_data[idx + 2 * n as usize + 1] = im_sign;
        }
    }

    // Build params: [width, height, max_iters, n_limbs, frac_limbs, thresh_limbs(n)]
    let mut params_data = vec![0u32; 5 + n as usize];
    params_data[0] = width;
    params_data[1] = height;
    params_data[2] = max_iters;
    params_data[3] = n;
    params_data[4] = frac_limbs;
    params_data[5 + n as usize - 1] = 4; // threshold = 4.0 in top limb

    let words_per_thread = 16 * n + 8;
    let scratch_size = (total_pixels * words_per_thread * 4) as u64;
    let iter_counts_size = (total_pixels * 4) as u64;

    // Create GPU buffers
    let c_data_buf = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("c_data"),
        size: (c_data.len() * 4) as u64,
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });
    let scratch_buf = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("scratch"),
        size: scratch_size,
        usage: wgpu::BufferUsages::STORAGE,
        mapped_at_creation: false,
    });
    let iter_counts_buf = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("iter_counts"),
        size: iter_counts_size,
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
        mapped_at_creation: false,
    });
    let params_buf = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("params"),
        size: (params_data.len() * 4) as u64,
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });

    queue.write_buffer(&c_data_buf, 0, bytemuck_cast_slice(&c_data));
    queue.write_buffer(&params_buf, 0, bytemuck_cast_slice(&params_data));

    let bind_group_layout = pipeline.get_bind_group_layout(0);
    let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
        label: Some("mandelbrot"),
        layout: &bind_group_layout,
        entries: &[
            wgpu::BindGroupEntry { binding: 0, resource: c_data_buf.as_entire_binding() },
            wgpu::BindGroupEntry { binding: 1, resource: scratch_buf.as_entire_binding() },
            wgpu::BindGroupEntry { binding: 2, resource: iter_counts_buf.as_entire_binding() },
            wgpu::BindGroupEntry { binding: 3, resource: params_buf.as_entire_binding() },
        ],
    });

    // Timestamp query set
    let query_set = if has_timestamps {
        Some(device.create_query_set(&wgpu::QuerySetDescriptor {
            label: Some("timestamps"),
            ty: wgpu::QueryType::Timestamp,
            count: 2,
        }))
    } else {
        None
    };

    let ts_resolve_buf = if has_timestamps {
        Some(device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("ts_resolve"),
            size: 16, // 2 x u64
            usage: wgpu::BufferUsages::QUERY_RESOLVE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        }))
    } else {
        None
    };

    let ts_readback_buf = if has_timestamps {
        Some(device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("ts_readback"),
            size: 16,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        }))
    } else {
        None
    };

    let workgroups_x = (width + 15) / 16;
    let workgroups_y = (height + 15) / 16;

    let mut wall_times = Vec::new();
    let mut gpu_times = Vec::new();

    let total_runs = warmup + runs;

    for run_idx in 0..total_runs {
        let wall_start = Instant::now();

        let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
            label: Some("profiler"),
        });

        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("mandelbrot"),
                timestamp_writes: query_set.as_ref().map(|qs| wgpu::ComputePassTimestampWrites {
                    query_set: qs,
                    beginning_of_pass_write_index: Some(0),
                    end_of_pass_write_index: Some(1),
                }),
            });
            pass.set_pipeline(pipeline);
            pass.set_bind_group(0, &bind_group, &[]);
            pass.dispatch_workgroups(workgroups_x, workgroups_y, 1);
        }

        if let (Some(qs), Some(resolve_buf)) = (&query_set, &ts_resolve_buf) {
            encoder.resolve_query_set(qs, 0..2, resolve_buf, 0);
            if let Some(readback) = &ts_readback_buf {
                encoder.copy_buffer_to_buffer(resolve_buf, 0, readback, 0, 16);
            }
        }

        queue.submit(std::iter::once(encoder.finish()));

        // Wait for GPU to finish
        pollster::block_on(async {
            device.poll(wgpu::Maintain::Wait);
        });

        let wall_elapsed = wall_start.elapsed().as_secs_f64() * 1000.0;

        // Read GPU timestamps if available
        let gpu_elapsed = if let Some(readback) = &ts_readback_buf {
            let (sender, receiver) = std::sync::mpsc::channel();
            readback.slice(..).map_async(wgpu::MapMode::Read, move |result| {
                sender.send(result).unwrap();
            });
            device.poll(wgpu::Maintain::Wait);
            match receiver.recv() {
                Ok(Ok(())) => {
                    let data = readback.slice(..).get_mapped_range();
                    let timestamps: &[u64] = unsafe {
                        std::slice::from_raw_parts(data.as_ptr() as *const u64, 2)
                    };
                    let period = queue.get_timestamp_period() as f64; // nanoseconds per tick
                    let dt = (timestamps[1] - timestamps[0]) as f64 * period / 1_000_000.0;
                    drop(data);
                    readback.unmap();
                    Some(dt)
                }
                _ => None,
            }
        } else {
            None
        };

        if run_idx >= warmup {
            wall_times.push(wall_elapsed);
            if let Some(gpu_ms) = gpu_elapsed {
                gpu_times.push(gpu_ms);
            }
        }
    }

    // Clean up
    c_data_buf.destroy();
    scratch_buf.destroy();
    iter_counts_buf.destroy();
    params_buf.destroy();

    TimingResult {
        n_limbs: n,
        resolution,
        max_iters,
        total_pixels,
        wall_ms: wall_times,
        gpu_ms: gpu_times,
    }
}

fn bytemuck_cast_slice(data: &[u32]) -> &[u8] {
    unsafe {
        std::slice::from_raw_parts(data.as_ptr() as *const u8, data.len() * 4)
    }
}

fn print_table(results: &[TimingResult], has_timestamps: bool) {
    if has_timestamps {
        println!("┌───────┬──────┬───────┬─────────┬───────────────────────────┬───────────────────────────┐");
        println!("│ limbs │  res │ iters │  pixels │  wall (min/med/max) ms    │  gpu  (min/med/max) ms    │");
        println!("├───────┼──────┼───────┼─────────┼───────────────────────────┼───────────────────────────┤");
    } else {
        println!("┌───────┬──────┬───────┬─────────┬───────────────────────────┐");
        println!("│ limbs │  res │ iters │  pixels │  wall (min/med/max) ms    │");
        println!("├───────┼──────┼───────┼─────────┼───────────────────────────┤");
    }

    for r in results {
        let (wmin, wmed, wmax) = r.wall_stats();
        if has_timestamps {
            let gpu_str = match r.gpu_stats() {
                Some((gmin, gmed, gmax)) => format!("{:8.2} / {:8.2} / {:8.2}", gmin, gmed, gmax),
                None => "          N/A          ".to_string(),
            };
            println!("│ {:5} │ {:4} │ {:5} │ {:7} │ {:8.2} / {:8.2} / {:8.2} │ {} │",
                r.n_limbs, r.resolution, r.max_iters, r.total_pixels,
                wmin, wmed, wmax, gpu_str);
        } else {
            println!("│ {:5} │ {:4} │ {:5} │ {:7} │ {:8.2} / {:8.2} / {:8.2} │",
                r.n_limbs, r.resolution, r.max_iters, r.total_pixels,
                wmin, wmed, wmax);
        }
    }

    if has_timestamps {
        println!("└───────┴──────┴───────┴─────────┴───────────────────────────┴───────────────────────────┘");
    } else {
        println!("└───────┴──────┴───────┴─────────┴───────────────────────────┘");
    }

    // Summary: cost per pixel*iter
    println!("\nCost per pixel×iter (wall median):");
    for r in results {
        let (_, wmed, _) = r.wall_stats();
        let cost_ns = wmed * 1_000_000.0 / (r.total_pixels as f64 * r.max_iters as f64);
        println!("  n={:2} res={:4} iters={:4} → {:.1} ns/pixel/iter",
            r.n_limbs, r.resolution, r.max_iters, cost_ns);
    }
}

fn print_csv(results: &[TimingResult], has_timestamps: bool) {
    if has_timestamps {
        println!("limbs,res,iters,pixels,wall_min_ms,wall_med_ms,wall_max_ms,gpu_min_ms,gpu_med_ms,gpu_max_ms");
    } else {
        println!("limbs,res,iters,pixels,wall_min_ms,wall_med_ms,wall_max_ms");
    }
    for r in results {
        let (wmin, wmed, wmax) = r.wall_stats();
        if has_timestamps {
            let (gmin, gmed, gmax) = r.gpu_stats().unwrap_or((f64::NAN, f64::NAN, f64::NAN));
            println!("{},{},{},{},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3}",
                r.n_limbs, r.resolution, r.max_iters, r.total_pixels,
                wmin, wmed, wmax, gmin, gmed, gmax);
        } else {
            println!("{},{},{},{},{:.3},{:.3},{:.3}",
                r.n_limbs, r.resolution, r.max_iters, r.total_pixels,
                wmin, wmed, wmax);
        }
    }
}
