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
#[cfg(test)]
pub fn get_test_dir() -> std::io::Result<PathBuf> {
    let thread = std::thread::current();
    let name = thread.name().expect("Test thread should have a name");

    let now = std::time::SystemTime::now();
    let timestamp = now
        .duration_since(std::time::UNIX_EPOCH)
        .expect("Time went backwards");

    let secs = timestamp.as_secs();
    let nanos = timestamp.subsec_nanos();

    let mut path = PathBuf::from("./tmp");
    path.push("tempest_tests");
    path.push(format!("{}-{}.{:09}", name, secs, nanos));

    std::fs::create_dir_all(&path)?;

    Ok(path)
}
