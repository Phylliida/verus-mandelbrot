#!/bin/bash
# Convenience wrapper: delegates to top-level run.sh
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
exec "$SCRIPT_DIR/../run.sh" verus-mandelbrot --features viewer "$@"
