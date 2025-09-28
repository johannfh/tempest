#![allow(dead_code)]

mod sync;
mod thread;

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

    pub fn exec(test: fn()) {
        #[cfg(loom)]
        loom::model::model(test);
        #[cfg(not(loom))]
        test();
    }
}

pub struct Tempest {}
