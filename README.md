# verus-mandelbrot
Infinite zoom mandelbrot with exact rational arithmetic in rust+verus

## GPU Shader Profiler

Headless GPU benchmark for the verified Mandelbrot compute shader.

### Building

```bash
# Uses cargo-verus (from verus-dev) to compile with --no-verify
cd verus-cad
verus-dev/source/target-verus/release/cargo-verus build \
  --manifest-path Cargo.toml -p verus-mandelbrot \
  --features profiler --release --no-verify --bin profile_shader
```

The binary is produced at `verus-mandelbrot/target/release/profile_shader`.

### Running (NixOS)

On NixOS, wgpu can't find the Vulkan loader or ICD by default. You need two environment variables:

```bash
# 1. Find the Vulkan loader path:
pkg-config --libs vulkan
# Look for: -L/nix/store/HASH-vulkan-loader-VERSION/lib

# 2. Find the ICD file:
echo $VK_ICD_FILENAMES
# Or check: /run/opengl-driver/share/vulkan/icd.d/

# 3. Run with both set:
LD_LIBRARY_PATH=/nix/store/HASH-vulkan-loader-VERSION/lib \
VK_ICD_FILENAMES=/run/opengl-driver/share/vulkan/icd.d/nvidia_icd.x86_64.json \
./target/release/profile_shader --limbs 4,8,16 --res 256 --iters 200 --runs 5
```

### Options

```
--limbs N[,N,...]   Limb counts to test (default: 4,8,16)
--res W[,W,...]     Resolutions to test (default: 128,256,512)
--iters N[,N,...]   Max iteration counts (default: 100,200,500)
--runs N            Measured runs per config (default: 5)
--warmup N          Warmup runs before measurement (default: 1)
--csv               Output CSV instead of table
```

### Example output (RTX 3090)

```
Profiling 4 configurations (1 warmup + 5 measured runs each)

┌───────┬──────┬───────┬─────────┬───────────────────────────┬───────────────────────────┐
│ limbs │  res │ iters │  pixels │  wall (min/med/max) ms    │  gpu  (min/med/max) ms    │
├───────┼──────┼───────┼─────────┼───────────────────────────┼───────────────────────────┤
│     4 │  256 │   500 │   65536 │    10.09 /    10.11 /    10.30 │    10.02 /    10.04 /    10.22 │
│     8 │  256 │   500 │   65536 │    30.10 /    30.29 /    30.53 │    29.87 /    30.06 /    30.36 │
│    16 │  256 │   500 │   65536 │   112.52 /   113.30 /   115.61 │   112.31 /   113.02 /   115.28 │
│    32 │  256 │   500 │   65536 │   910.69 /   915.61 /   918.00 │   910.35 /   915.12 /   917.60 │
└───────┴──────┴───────┴─────────┴───────────────────────────┴───────────────────────────┘

Cost per pixel×iter (wall median):
  n= 4 res= 256 iters= 500 → 0.3 ns/pixel/iter
  n= 8 res= 256 iters= 500 → 0.9 ns/pixel/iter
  n=16 res= 256 iters= 500 → 3.5 ns/pixel/iter
  n=32 res= 256 iters= 500 → 27.9 ns/pixel/iter
```
