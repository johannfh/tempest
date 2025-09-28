#[cfg(loom)]
pub use loom::thread::spawn;
#[cfg(not(loom))]
pub use std::thread::spawn;

