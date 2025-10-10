#![allow(dead_code)]
#![deny(clippy::undocumented_unsafe_blocks)]

use std::sync::atomic::{AtomicU64, Ordering};

use crate::{arena::Arena, arena_skiplist::ArenaSkiplist};

pub mod arena;
pub mod arena_skiplist;

#[macro_use]
extern crate tracing;

pub struct Tempest {
    skiplist: arena_skiplist::ArenaSkiplist,
    seqnum: AtomicU64,
}

impl Tempest {
    pub fn new() -> Self {
        let arena = Arena::new(1024 * 1024 * 16); // 16 MiB
        Tempest {
            skiplist: ArenaSkiplist::new_in(arena),
            seqnum: 1.into(),
        }
    }

    fn get_seqnum(&self) -> u64 {
        self.seqnum.fetch_add(1, Ordering::Relaxed)
    }

    pub fn set(&self, key: &[u8], value: Option<&[u8]>) {
        trace!(
            key = String::from_utf8_lossy(key).as_ref(),
            value = String::from_utf8_lossy(key).as_ref(),
            "setting key-value pair in tempest, skiplist: {:?}",
            self.skiplist,
        );
        let seqnum = self.get_seqnum();
        self.skiplist
            .insert(key, value, seqnum)
            .expect("insert failed, oom?");
    }

    pub fn get(&self, key: &[u8]) -> Option<&[u8]> {
        self.skiplist.get(key)
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

    use super::*;

    #[test]
    fn test_tempest_set_get_simple() {
        init!();

        let tempest = Tempest::new();
        let key1 = b"key1";
        let value1 = b"value1";
        tempest.set(key1, Some(value1));
        assert_eq!(tempest.get(key1).unwrap(), value1);
    }

    #[test]
    fn test_tempest_set_get_modify() {
        init!();

        let tempest = Tempest::new();
        let key = b"key";
        let value1 = b"value1";
        tempest.set(key, Some(value1));
        let key_value1 = tempest.get(key).unwrap();
        assert_eq!(
            key_value1,
            value1,
            "expected: key={}, got: key={}",
            String::from_utf8_lossy(value1),
            String::from_utf8_lossy(key_value1)
        );

        let value2 = b"value2";
        tempest.set(key, Some(value2));
        let key_value2 = tempest.get(key).unwrap();
        assert_eq!(
            key_value2,
            value2,
            "expected: key={}, got: key={}",
            String::from_utf8_lossy(value2),
            String::from_utf8_lossy(key_value2)
        );

        let value3 = b"value1";
        tempest.set(key, Some(value3));
        let key_value3 = tempest.get(key).unwrap();
        assert_eq!(
            key_value3,
            value3,
            "expected: key={}, got: key={}",
            String::from_utf8_lossy(value3),
            String::from_utf8_lossy(key_value3)
        );
    }
}
