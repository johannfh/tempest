use std::path::PathBuf;

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
