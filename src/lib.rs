#![allow(dead_code)]

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

pub struct Tempest {}
