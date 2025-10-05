help:
    @echo "Available commands:"
    @echo "  help        Show this help message"
    @echo "  test        Run all tests with detailed logging"
    @echo "  test-base   Run standard tests with detailed logging"
    @echo "  test-loom   Run loom tests with detailed logging and loom configuration"


test: test-base test-loom

test-base:
    RUST_LOG=trace \
        cargo test --workspace

test-loom:
    RUSTFLAGS="--cfg loom" \
        LOOM_LOG=debug \
        LOOM_LOCATION=1 \
        LOOM_CHECKPOINT_INTERVAL=1 \
        LOOM_CHECKPOINT_FILE=./loom-checkpoint.json \
        RUST_LOG=trace \
        cargo test --workspace
