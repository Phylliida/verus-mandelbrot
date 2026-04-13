#!/usr/bin/env bash
# Generate WGSL shaders for different limb counts (n).
# Each shader has compile-time array sizes matching the target n.
#
# Usage: ./generate_shaders.sh
# Requires: verus-gpu-parser built (cargo build --release)

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SRC="$SCRIPT_DIR/../src/gpu_perturbation_entry.rs"
TRANSPILER="$SCRIPT_DIR/../../verus-gpu-parser"
TMPFILE=$(mktemp /tmp/gpu_perturbation_XXXXXX.rs)

trap "rm -f $TMPFILE" EXIT

for N in 4 8 16 32 64; do
    PROD=$((2 * N))
    OUT="$SCRIPT_DIR/mandelbrot_perturbation_n${N}.wgsl"

    echo "Generating shader for n=$N (local=$N, prod=$PROD) -> $OUT"

    # Replace gpu_local annotations with target sizes.
    # Order matters: replace (8) first so the (4)→N result doesn't get caught.
    sed -e "s|// #\[gpu_local(8)\]|// #[gpu_local($PROD)]|g" \
        -e "s|// #\[gpu_local(4)\]|// #[gpu_local($N)]|g" \
        "$SRC" > "$TMPFILE"

    # Transpile
    (cd "$TRANSPILER" && cargo run --release --bin verus-gpu-transpile -- \
        "$TMPFILE" -o "$OUT" 2>&1) | grep -E "^(Wrote|  \[gpu_local\])" || true

    echo "  Done: $(wc -c < "$OUT") bytes"
done

echo ""
echo "All shaders generated."
