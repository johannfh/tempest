help:
    @echo "Available commands:"
    @echo "  help        Show this help message"
    @echo "  test        Run all tests with detailed logging"
    @echo "  test-base   Run standard tests with detailed logging"
    @echo "  test-loom   Run loom tests with detailed logging and loom configuration"


test:
    RUST_LOG=debug \
        cargo test --workspace
