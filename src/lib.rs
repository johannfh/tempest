#![allow(dead_code)]
#![deny(clippy::undocumented_unsafe_blocks)]

pub const TEMPEST_VERSION: u32 = 1;

use std::{
    path::{Path, PathBuf},
    sync::atomic::AtomicU64,
};

use bincode::{de::read::Reader, enc::write::Writer};
use derive_more::{Display, Error, From};

use crate::{
    arena::Arena,
    arena_skiplist::ArenaSkiplist,
    core::{Key, KeyKind, KeyTrailer, SeqNum, Value},
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

/// # Tempest DB
///
/// A simple persistent key-value store using an LSM-tree architecture.
pub struct KvStore {
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

#[derive(Debug, Display, From, Error)]
pub enum TempestError {
    #[display("IO Error: {}", _0)]
    IoError(std::io::Error),
}

impl KvStore {
    #[instrument(level = "info", skip_all)]
    pub fn open(dir: impl AsRef<Path>) -> Result<Self, TempestError> {
        let dir: PathBuf = dir.as_ref().to_path_buf();
        if tracing::enabled!(tracing::Level::INFO) {}
        let arena = Arena::new(1024 * 1024); // 1MiB arena
        if cfg!(test) {
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
        } else {
            // In non-test environments, create the directory if it doesn't exist.
            if !dir.exists() {
                std::fs::create_dir_all(&dir)?;
                info!(
                    ?dir,
                    absolute_dir = ?std::fs::canonicalize(&dir)?,
                    "data directory created"
                );
            } else {
                info!(
                    ?dir,
                    absolute_dir = ?std::fs::canonicalize(&dir)?,
                    "data directory exists"
                );
            }
        }

        Ok(Self {
            skiplist: ArenaSkiplist::new_in(arena),
            seqnum: AtomicU64::new(SeqNum::START),
            data_dir: dir.clone(),
            wal_manager: WalManager::new(dir),
        })
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

    #[instrument(level = "debug", skip_all, fields(
        key_len = key.len(),
        key_hex = hex::encode(key),
        value_len = value.len(),
        value_hex = hex::encode(value),
    ))]
    pub fn insert(&self, key: Key, value: Value) {
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

    #[instrument(level = "debug", skip_all, fields(
        key_len = key.len(),
        key_hex = hex::encode(key),
        value_len, value_hex, seqnum,
    ))]
    pub fn get(&self, key: Key) -> Option<Value<'_>> {
        match self.skiplist.get(key, SeqNum::MAX) {
            Some((key_trailer, value)) => {
                if tracing::level_filters::STATIC_MAX_LEVEL <= tracing::metadata::LevelFilter::DEBUG
                {
                    tracing::Span::current().record("value_len", value.len());
                    tracing::Span::current().record("value_hex", hex::encode(value));
                    tracing::Span::current().record("seqnum", key_trailer.seqnum().inner());
                }
                Some(value)
            }
            None => {
                trace!(key, "key not found");
                None
            }
        }
    }

    pub fn dir(&self) -> &Path {
        &self.data_dir
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
}
