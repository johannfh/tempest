use bincode::{de::read::Reader, enc::write::Writer};
use derive_more::Display;
use num_enum::{IntoPrimitive, TryFromPrimitive};

// NOTE: May have owned variants in the future.
// Currently, keys and values are represented as borrowed slices.
// This avoids unnecessary data copying during data store operations.

/// A borrowed slice representing a key.
pub type KeySlice<'a> = &'a [u8];
/// A borrowed slice representing a value.
pub type ValueSlice<'a> = &'a [u8];

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Display)]
#[display("#{}", _0)]
pub struct SeqNum(u64);

impl SeqNum {
    pub const ZERO: u64 = 0;
    pub const START: u64 = 16; // reserve 0-15 for special purposes?
    pub const MAX: u64 = (1 << 56) - 1;

    pub(crate) fn inner(&self) -> u64 {
        self.0
    }
}

impl From<u64> for SeqNum {
    fn from(value: u64) -> Self {
        assert!(value <= Self::MAX, "sequence number overflow: {}", value);
        Self(value)
    }
}

/// Type of the key-value entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, TryFromPrimitive, IntoPrimitive)]
#[repr(u8)]
pub(crate) enum KeyKind {
    /// A deletion marker for a key.
    Delete = 0,
    /// A regular key-value entry.
    Set = 1,
    /// A merge operation for a key.
    /// The semantics of merge operations are application-defined.
    Merge = 2,
}

/// The trailer associated with a key in the write-ahead log.
/// It encodes the sequence number and the kind of the key.
///
/// # Layout
///
/// - Lower Bits 0-7: [`KeyKind`] (u8)
/// - Upper Bits 8-63: [`SeqNum`] (u56)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub(crate) struct KeyTrailer(u64);

impl KeyTrailer {
    pub(crate) fn new(seqnum: impl Into<SeqNum>, kind: KeyKind) -> Self {
        let seqnum: SeqNum = seqnum.into();
        Self(seqnum.inner() << 8 | (kind as u64))
    }

    pub(crate) fn inner(&self) -> u64 {
        self.0
    }

    pub(crate) fn seqnum(&self) -> SeqNum {
        SeqNum(self.0 >> 8)
    }

    pub(crate) fn kind(&self) -> KeyKind {
        KeyKind::try_from((self.0 & 0xff) as u8).expect("invalid key kind")
    }
}

impl bincode::Encode for KeyTrailer {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> Result<(), bincode::error::EncodeError> {
        encoder.writer().write(&self.0.to_le_bytes())?;
        Ok(())
    }
}

impl bincode::Decode<()> for KeyTrailer {
    fn decode<D: bincode::de::Decoder>(
        decoder: &mut D,
    ) -> Result<Self, bincode::error::DecodeError> {
        let value = {
            let mut buf = [0u8; 8];
            decoder.reader().read(&mut buf)?;
            u64::from_le_bytes(buf)
        };
        Self::try_from(value).map_err(|err| bincode::error::DecodeError::Other(err))
    }
}

impl TryFrom<u64> for KeyTrailer {
    type Error = &'static str;

    /// Tries to create a `KeyTrailer` from a raw u64 value.
    /// Returns an error if the key kind is invalid.
    ///
    /// # Errors
    /// - "invalid key kind": if the lower 8 bits do not correspond to a valid `KeyKind`.
    fn try_from(value: u64) -> Result<Self, Self::Error> {
        let kind = (value & 0xff) as u8;
        match KeyKind::try_from(kind) {
            Err(_) => Err("invalid key kind"),
            Ok(_) => Ok(Self(value)),
        }
    }
}
