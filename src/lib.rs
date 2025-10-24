#![allow(dead_code)]
#![deny(clippy::undocumented_unsafe_blocks)]

mod arena_skiplist;
mod core;
mod wal;

#[cfg(not(any(target_pointer_width = "64", target_pointer_width = "32")))]
compile_error!("tempest only supports 32-bit and 64-bit architectures");

#[macro_use]
extern crate tracing;

#[cfg(any(test, doctest))]
mod tests {
    #[cfg(test)]
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
    pub(crate) fn get_test_dir() -> std::io::Result<std::path::PathBuf> {
        let thread = std::thread::current();
        let name = thread.name().expect("Test thread should have a name");

        let now = std::time::SystemTime::now();
        let timestamp = now
            .duration_since(std::time::UNIX_EPOCH)
            .expect("Time went backwards");

        let secs = timestamp.as_secs();
        let nanos = timestamp.subsec_nanos();

        let mut path = std::path::PathBuf::from("./tmp");
        path.push("tempest_tests");
        path.push(format!("{}-{}.{:09}", name, secs, nanos));

        std::fs::create_dir_all(&path)?;

        Ok(path)
    }
}
