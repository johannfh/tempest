#![allow(dead_code)]
#![deny(clippy::undocumented_unsafe_blocks)]

use std::sync::atomic::AtomicU64;

pub mod arena;
pub mod arena_skiplist;

#[macro_use]
extern crate tracing;

pub struct Tempest {
    seqnum: AtomicU64,
}

#[cfg(test)]
mod tests {
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
}
