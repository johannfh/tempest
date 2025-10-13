default:
    just --list

[group('test')]
test:
    RUST_LOG=debug \
        TRACE_LEVEL=trace \
        cargo test --workspace

[group('lint')]
clippy:
    cargo clippy -- \
        -D warnings

[group('example')]
example NAME:
    cargo run --example {{NAME}}
