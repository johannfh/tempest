use std::path::PathBuf;

#[macro_export]
macro_rules! init {
    () => {
        let _tracing_default_guard = tracing::subscriber::set_default(
            tracing_subscriber::fmt::Subscriber::builder()
                .with_test_writer()
                .with_max_level(tracing::Level::TRACE)
                .finish(),
        );
    };
}

/// Generates a unique test directory path based on the current timestamp
/// and the provided name. This helps to avoid conflicts between test runs.
pub fn get_test_dir(name: &str) -> PathBuf {
    let now = std::time::SystemTime::now();
    let timestamp = now
        .duration_since(std::time::UNIX_EPOCH)
        .expect("Time went backwards");

    let millis = timestamp.as_millis();
    let subsec_nanos = timestamp.subsec_nanos();
    format!("./tmp/tempest_tests/{}-{}.{}", name, millis, subsec_nanos).into()
}
