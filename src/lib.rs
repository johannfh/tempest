#![allow(dead_code)]
#![deny(clippy::undocumented_unsafe_blocks)]

use std::sync::atomic::AtomicU64;

use crate::{
    arena::Arena,
    arena_skiplist::{ArenaSkiplist, KeyKind, KeyTrailer},
};

pub mod arena;
pub mod arena_skiplist;

#[macro_use]
extern crate tracing;

/// # Tempest
/// A simple persistent key-value store using an LSM-tree architecture.
///
/// # Example
/// ```
/// use tempest::Tempest;
///
/// let tempest = Tempest::new();
/// tempest.insert(b"key1", b"value1");
/// tempest.insert(b"key2", b"value2");
/// tempest.insert(b"key1", b"value3"); // Update key1
/// let value = tempest.get(b"key1").expect("key1 should exist");
/// assert_eq!(value, b"value3");
/// ```
pub struct Tempest {
    skiplist: ArenaSkiplist,
    seqnum: AtomicU64,
}

impl Tempest {
    pub fn new() -> Self {
        let arena = Arena::new(1024 * 1024); // 1MiB arena
        Self {
            skiplist: ArenaSkiplist::new_in(arena),
            seqnum: 1.into(),
        }
    }

    fn next_seqnum(&self) -> u64 {
        self.seqnum
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
    }

    pub fn insert(&self, key: &[u8], value: &[u8]) {
        let seqnum = self.next_seqnum();
        let key_trailer = KeyTrailer::new(seqnum, KeyKind::Value);
        self.skiplist
            .insert(key, key_trailer, value)
            .expect("insert should succeed");
        trace!(
            "inserted key: {:?}, seqnum: {}, value: {:?}",
            key, seqnum, value
        );
    }

    pub fn get(&self, key: &[u8]) -> Option<&[u8]> {
        match self.skiplist.get(key) {
            Some((key_trailer, value)) => {
                trace!(key, seqnum = key_trailer.seqnum(), value, "found key",);
                Some(value)
            }
            None => {
                trace!(key, "key not found");
                None
            }
        }
    }
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
