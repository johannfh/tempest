help:
    @echo "Available commands:"
    @echo "  help        Show this help message"
    @echo "  test        Run all tests with debug logging"
    @echo "  clippy      Run clippy lints, denying any warning"


test:
    RUST_LOG=debug \
        TRACE_LEVEL=trace \
        cargo test --workspace

clippy:
    cargo clippy -- \
        -D warnings
