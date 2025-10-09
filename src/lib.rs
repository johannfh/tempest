#![allow(dead_code)]
#![deny(clippy::undocumented_unsafe_blocks)]

use std::sync::atomic::{AtomicU64, Ordering};

use crate::{arena::Arena, arena_skiplist::ArenaSkiplist};

pub mod arena;
pub mod arena_skiplist;

#[macro_use]
extern crate log;

#[cfg(test)]
mod tests {
    use ctor::ctor;

    #[ctor]
    fn init() {
        // Initialize logger for tests
        env_logger::builder().is_test(true).try_init();
    }
}

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
        let seqnum = self.get_seqnum();
        self.skiplist
            .insert(key, value, seqnum)
            .expect("insert failed, oom?");
    }

    pub fn get(&self, key: &[u8]) -> Option<&[u8]> {
        todo!("get not implemented yet")
    }
}
