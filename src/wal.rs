use std::path::PathBuf;

use derive_more::{From, Into};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, From, Into)]
pub struct WalNumber(u64);

impl WalNumber {
    pub const ZERO: u64 = 0;
    pub const START: u64 = 1;
    pub const MAX: u64 = (1 << 56) - 1;

    pub fn inner(&self) -> u64 {
        self.0
    }
}

pub struct Wal {
    path: PathBuf,
}

pub struct WalManager {
    dir: PathBuf,
    wals: Vec<Wal>,
}

impl WalManager {
    pub fn new(dir: PathBuf) -> Self {
        let mut wals = vec![];

        let log_dir = dir.join("log");
        if log_dir.exists() {
            // load wal files from dir/log
            for entry in std::fs::read_dir(log_dir).unwrap() {
                let entry = entry.unwrap();
                let path = entry.path();
                if path.extension().and_then(|s| s.to_str()) == Some("wal") {
                    wals.push(Wal { path });
                } else {
                    // ignore non-wal files
                    warn!("ignoring non-wal file: {:?}, expected .wal extension", path);
                }
            }
            // sort by file name
            wals.sort_by_key(|wal| wal.path.clone());
        } else {
            // create log dir if not exists
            std::fs::create_dir_all(&log_dir).unwrap();
        }

        Self { dir, wals }
    }
}
