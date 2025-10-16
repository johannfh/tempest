#![allow(dead_code)]
#![deny(clippy::undocumented_unsafe_blocks)]

pub const TEMPEST_VERSION: u32 = 1;

use std::{path::PathBuf, sync::atomic::AtomicU64};

use bincode::{de::read::Reader, enc::write::Writer};

use crate::{
    arena::Arena,
    arena_skiplist::ArenaSkiplist,
    core::{KeyKind, KeyTrailer, SeqNum},
    wal::WalManager,
};

mod arena;
mod arena_skiplist;
mod core;
mod wal;

#[macro_use]
extern crate tracing;

#[derive(Debug)]
struct Manifest {
    /// Current version of the manifest format.
    version: u32,
    /// The next sequence number to be used.
    seqnum: u64,
}

impl Manifest {
    fn new(seqnum: u64) -> Self {
        Self {
            version: TEMPEST_VERSION,
            seqnum,
        }
    }

    fn decode_impl_v1<D: bincode::de::Decoder<Context = ()>>(
        decoder: &mut D,
        version: u32,
    ) -> Result<Self, bincode::error::DecodeError> {
        let seqnum = {
            let mut buf = [0u8; 8];
            decoder.reader().read(&mut buf)?;
            u64::from_le_bytes(buf)
        };
        Ok(Self { version, seqnum })
    }
}

impl bincode::Encode for Manifest {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> Result<(), bincode::error::EncodeError> {
        let version_bytes = self.version.to_le_bytes();
        encoder.writer().write(&version_bytes)?;
        let seqnum_bytes = self.seqnum.to_le_bytes();
        encoder.writer().write(&seqnum_bytes)?;
        Ok(())
    }
}

impl bincode::Decode<()> for Manifest {
    fn decode<D: bincode::de::Decoder<Context = ()>>(
        decoder: &mut D,
    ) -> Result<Self, bincode::error::DecodeError> {
        let version = {
            let mut buf = [0u8; 4];
            decoder.reader().read(&mut buf)?;
            u32::from_le_bytes(buf)
        };
        match version {
            TEMPEST_VERSION => Ok(Self::decode_impl_v1(decoder, version)?),
            v => {
                return Err(bincode::error::DecodeError::OtherString(
                    format!("unsupported manifest version: {}", v).into(),
                ));
            }
        }
    }
}

/// # Tempest
/// A simple persistent key-value store using an LSM-tree architecture.
pub struct Tempest {
    /// The data directory for all the data files.
    data_dir: PathBuf,

    /// Sequence number generator for versioning keys.
    /// Contains the next sequence number to be used.
    /// => To get the latest sequence number, subtract 1.
    seqnum: AtomicU64,

    /// The skiplist that holds the key-value pairs.
    skiplist: ArenaSkiplist,

    /// The write-ahead log manager.
    wal_manager: WalManager,
}

impl Tempest {
    pub fn new(dir: PathBuf) -> Self {
        let arena = Arena::new(1024 * 1024); // 1MiB arena
        #[cfg(test)]
        let dir = {
            use std::time;
            _ = dir;

            // Create a unique temp directory for each test run based on
            // the current timestamp to avoid conflicts between parallel
            // test runs or multiple runs of the same test.
            // Cleanup is done in the `cleanup` method.
            let temp_dir = std::env::var_os("CARGO_TARGET_DIR")
                .map(PathBuf::from)
                .unwrap_or_else(|| "./target".into());
            let now = time::SystemTime::now()
                .duration_since(time::UNIX_EPOCH)
                .expect("Time went backwards");
            let timestamp = format!("{}.{:09}", now.as_secs(), now.subsec_nanos());

            let temp_dir = temp_dir.join(format!("tempest_test_data-{}", timestamp));

            assert!(
                !temp_dir.exists(),
                "Temp data directory already exists: {:?}",
                temp_dir
            );

            std::fs::create_dir_all(&temp_dir).expect("Failed to create temp data directory");
            trace!("Using temp data dir: {:?}", temp_dir);
            temp_dir
        };

        #[cfg(not(test))]
        {
            // In non-test environments, create the directory if it doesn't exist.
            if !dir.exists() {
                std::fs::create_dir_all(&dir).expect("Failed to create data directory");
                info!(
                    ?dir,
                    absolute_dir = ?std::fs::canonicalize(&dir).unwrap(),
                    "data directory created"
                );
            } else {
                info!(
                    ?dir,
                    absolute_dir = ?std::fs::canonicalize(&dir).unwrap(),
                    "data directory exists"
                );
            }
        }

        Self {
            skiplist: ArenaSkiplist::new_in(arena),
            seqnum: AtomicU64::new(SeqNum::START),
            data_dir: dir.clone(),
            wal_manager: WalManager::new(dir),
        }
    }

    /// Get the current sequence number.
    fn latest_seqnum(&self) -> SeqNum {
        (self.seqnum.load(std::sync::atomic::Ordering::SeqCst) - 1).into()
    }

    /// Get the next sequence number and increment the internal counter.
    fn next_seqnum(&self) -> SeqNum {
        self.seqnum
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            .into()
    }

    #[instrument(
        level = "trace",
        skip_all,
        fields(key = String::from_utf8_lossy(key).as_ref(),
            value = String::from_utf8_lossy(value).as_ref())
    )]
    pub fn insert(&self, key: &[u8], value: &[u8]) {
        let seqnum = self.next_seqnum();
        let key_trailer = KeyTrailer::new(seqnum, KeyKind::Set);
        self.skiplist
            .insert(key, key_trailer, value)
            .expect("insert should succeed");
        trace!(
            "inserted key: {:?}, seqnum: {}, value: {:?}",
            key, seqnum, value
        );
    }

    #[instrument(
        level = "trace",
        skip_all,
        fields(key = String::from_utf8_lossy(key).as_ref()),
    )]
    pub fn get(&self, key: &[u8]) -> Option<&[u8]> {
        let latest_seqnum = self.latest_seqnum();
        match self.skiplist.get(key, latest_seqnum) {
            Some((key_trailer, value)) => {
                trace!(
                    latest_seqnum = latest_seqnum.inner(),
                    seqnum = key_trailer.seqnum().inner(),
                    value,
                    "found key",
                );
                Some(value)
            }
            None => {
                trace!(key, "key not found");
                None
            }
        }
    }

    // Cleanup the data directory. Only available in test builds.
    // This is so the OS doesn't get cluttered with test data.
    #[cfg(any(test, doctest))]
    fn cleanup(&self) {
        std::fs::remove_dir_all(&self.data_dir).expect("Failed to clean up data directory");
        trace!("Cleaned up data dir: {:?}", self.data_dir);
    }
}

#[cfg(any(test, doctest))]
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
    fn test_create_tempest() {
        init!();

        let tempest = Tempest::new("./data".into());
        tempest.insert(b"key1", b"value1");
        tempest.insert(b"key2", b"value2");
        tempest.insert(b"key1", b"value3"); // Update key1
        let value = tempest.get(b"key1").expect("key1 should exist");
        assert_eq!(value, b"value3");

        tempest.cleanup();
    }
}
