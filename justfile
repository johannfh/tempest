help:
    @echo "Available commands:"
    @echo "  help        Show this help message"

test:
    RUST_LOG=trace cargo test --workspace

test-loom:
    RUSTFLAGS="--cfg loom" \
        LOOM_LOG=debug \
        LOOM_LOCATION=1 \
        LOOM_CHECKPOINT_INTERVAL=1 \
        LOOM_CHECKPOINT_FILE=./loom-checkpoint.json \
        RUST_LOG=trace \
        cargo test --workspace
