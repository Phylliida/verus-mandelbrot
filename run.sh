#!/bin/bash
rustup run 1.93.1 cargo run --release --bin mandelbrot_viewer --features viewer "$@"
