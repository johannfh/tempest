use std::{
    cell::UnsafeCell,
    io::{Seek, SeekFrom},
    sync::{Arc, atomic::AtomicU32},
};

use crate::arena::Arena;

// An arena-based skiplist implementation.
// It is designed to store key-value pairs in an append-only manner,
// where keys and values are byte slices.
//
// The skiplist is built on top of an `Arena`, which provides efficient
// memory management by allocating a large contiguous block of memory upfront
// and then carving out smaller pieces as needed.
pub struct ArenaSkiplist {
    arena: UnsafeCell<Arena>,
    head: *mut Node, // Pointer to the head node in the skiplist
    tail: *mut Node, // Pointer to the tail node in the skiplist
}

/// Maximum size of the arena, limited by both `isize::MAX` and `i32::MAX`.
const MAX_ARENA_SIZE: usize = {
    let this = isize::MAX as usize;
    let other = i32::MAX as usize;
    if other < this { other } else { this }
};

/// Maximum height of the skiplist, typically 12 levels (0-11).
const MAX_HEIGHT: u8 = 12;

/// Probability factor for determining node height in the skiplist.
/// Typically set to 0.25 (1 in 4 chance to increase height).
const P: f64 = 0.25;

#[derive(Debug)]
pub enum InsertError {
    /// Not enough memory in the arena to insert the node.
    /// The value is the number of bytes required.
    OutOfMemory(u32),
}

impl ArenaSkiplist {
    /// Creates a new `ArenaSkiplist` with the given `Arena`.
    /// The arena's capacity must not exceed `MAX_ARENA_SIZE`.
    pub fn new_in(arena: Arena) -> Self {
        assert!(
            arena.capacity() as i32 <= MAX_ARENA_SIZE as i32,
            "Arena capacity exceeds maximum allowed size"
        );

        let mut skip_list = ArenaSkiplist {
            arena: arena.into(),
            head: std::ptr::null_mut(),
            tail: std::ptr::null_mut(),
        };

        // Initialize the skiplist with a head node at offset 0
        // The head node has maximum height and no key/value
        let head = skip_list
            .insert_node_raw(MAX_HEIGHT, 0, 0)
            .expect("Failed to initialize skiplist head node, arena may be too small");
        skip_list.head = head;
        // SAFETY: We allocated the head within the arena, so no OOB access will occur.
        let head_offset = unsafe {
            skip_list
                .arena
                .get_mut()
                .offset_of_unchecked(head as *const u8)
        };

        let tail = skip_list
            .insert_node_raw(MAX_HEIGHT, 0, 0)
            .expect("Failed to initialize skiplist tail node, arena may be too small");
        // SAFETY: We allocated the tail within the arena, so no OOB access will occur.
        let tail_offset = unsafe {
            skip_list
                .arena
                .get_mut()
                .offset_of_unchecked(tail as *const u8)
        };

        let order = std::sync::atomic::Ordering::SeqCst;

        // Link head with tail at all levels
        for level in 0..MAX_HEIGHT {
            unsafe {
                (*head).tower[level as usize]
                    .next_offset
                    .store(tail_offset, order);
                (*tail).tower[level as usize]
                    .prev_offset
                    .store(head_offset, order);
            }
        }

        skip_list.tail = tail;
        assert_eq!(head_offset, 0, "Head node must be at offset 0");

        skip_list
    }

    pub fn insert(
        &mut self,
        key: &[u8],
        value: Option<&[u8]>,
        seq_num: u64,
    ) -> Result<(), InsertError> {
        // Determine the height of the new node using a probabilistic method.
        // Each level has a probability `P` of being included, up to `MAX_HEIGHT`
        let height = {
            let mut h = 0;
            while h < MAX_HEIGHT - 1 && rand::random::<f64>() < P {
                h += 1;
            }
            h
        };

        match value {
            Some(v) => self.insert_set(key, v, seq_num, height),
            None => self.insert_delete(key, seq_num, height),
        }
    }

    fn insert_set(
        &mut self,
        key: &[u8],
        value: &[u8],
        seq_num: u64,
        height: u8,
    ) -> Result<(), InsertError> {
        let key_metadata = KeyMetadata::new(KeyKind::Set, seq_num);
        let node_ptr = self.insert_node(height, key, key_metadata, value)?;

        // SAFETY: We must not access `node.tower` beyond `height`.
        let node = unsafe { &mut (*node_ptr) };

        // Implementation for linking the new node into the skiplist
        // This is a placeholder and should be replaced with actual logic

        Ok(())
    }

    fn insert_delete(&mut self, key: &[u8], seq_num: u64, height: u8) -> Result<(), InsertError> {
        // Implementation for inserting a delete marker
        // This is a placeholder and should be replaced with actual logic
        unimplemented!(
            "insert_delete is not yet implemented, key: {:?}, seq_num: {}, height: {}",
            key,
            seq_num,
            height
        );
    }

    fn insert_node(
        &self,
        height: u8,
        key: &[u8],
        key_metadata: KeyMetadata,
        value: &[u8],
    ) -> Result<*mut Node, InsertError> {
        assert!(height < MAX_HEIGHT, "height exceeds MAX_HEIGHT");

        let key_size = key.len() as u32;
        assert!(key_size < u32::MAX, "key size is too large");
        let value_size = value.len() as u32;
        assert!(value_size < u32::MAX, "value size is too large");
        let combined_size = MAX_NODE_SIZE + key_size + value_size;
        assert!(
            combined_size <= MAX_ARENA_SIZE as u32,
            "combined key and value size exceeds maximum allowed size"
        );

        let node_ptr = self.insert_node_raw(height, key_size, value_size)?;

        // SAFETY: We must not access `node.tower` beyond `height`.
        let node = unsafe { &mut (*node_ptr) };
        for i in 0..=height {
            node.tower[i as usize].init(0);
        }

        // SAFETY: We have just allocated enough space for the key and value
        // at `node.data_offset`, so this pointer is valid.
        unsafe {
            let key_ptr = (node as *mut Node as *mut u8).add(node.data_offset as usize);
            let value_ptr = key_ptr.add(key.len());
            std::ptr::copy_nonoverlapping(key.as_ptr(), key_ptr, key.len());
            std::ptr::copy_nonoverlapping(value.as_ptr(), value_ptr, value.len());
        }

        node.key_metadata = key_metadata;

        Ok(node_ptr)
    }

    // Inserts a new node into the arena and returns a pointer to it.
    // This function does not initialize the node's key_metadata or tower links.
    // It only allocates the necessary space in the arena.
    // The caller is responsible for initializing remaining fields.
    //
    // # Arguments
    // - `height`: The height of the node in the skiplist.
    // - `key_size`: The size of the key in bytes.
    // - `value_size`: The size of the value in bytes.
    //
    // # Returns
    // - `Ok(*mut Node)`: A pointer to the newly allocated node in the arena.
    // - `Err(InsertError)`: If there is not enough memory in the arena.
    ///
    /// # Safety
    /// The caller must not access `node.tower` beyond `height`.
    fn insert_node_raw(
        &self,
        height: u8,
        key_size: u32,
        value_size: u32,
    ) -> Result<*mut Node, InsertError> {
        let tower_size =
            (MAX_HEIGHT as u32 - height as u32) * std::mem::size_of::<NodeLinks>() as u32;
        let node_size = std::mem::size_of::<Node>() as u32 - tower_size; // Size of Node without unused tower links
        let total_size = node_size + key_size + value_size;

        let arena = unsafe { &*self.arena.get() };

        // Allocate space for the node and its key/value in the arena
        let arena_offset = arena
            .alloc(total_size, 4)
            .map_err(|_| InsertError::OutOfMemory(total_size))?;

        // SAFETY: We have just allocated `total_size` bytes at `arena_offset`,
        // giving us a valid pointer into the arena buffer.
        let node_ptr = unsafe { arena.offset_to_ptr(arena_offset) as *mut Node };

        // SAFETY: We must not access `node.tower` beyond `height`.
        let node = unsafe { &mut *node_ptr };
        node.data_offset = arena_offset + node_size;
        node.key_size = key_size;
        node.value_size = value_size;

        Ok(node_ptr)
    }

    /// Discards the `ArenaSkiplist`, returning the underlying `Arena` for reuse.
    pub fn discard(self) -> Arena {
        let mut arena = self.arena;
        arena.get_mut().reset();
        arena.into_inner()
    }
}

unsafe impl Send for ArenaSkiplist {}
unsafe impl Sync for ArenaSkiplist {}

pub struct ArenaSkiplistIterator<'a> {
    skiplist: Arc<ArenaSkiplist>,
    level: u8,
    /// Current position in the skiplist, represented as a tuple of:
    /// `(node_ptr, key, key_metadata, value)`.
    current: (&'a Node, &'a [u8], KeyMetadata, &'a [u8]),
}

impl ArenaSkiplistIterator<'_> {
    fn new<'a>(skiplist: Arc<ArenaSkiplist>) -> ArenaSkiplistIterator<'a> {
        // SAFETY: The skiplist head is guaranteed to be valid as long as the skiplist exists.
        let head = unsafe { &*skiplist.head };
        let key = &[];
        let value = &[];
        let key_metadata = head.key_metadata;

        ArenaSkiplistIterator {
            skiplist,
            level: 0,
            current: (head, key, key_metadata, value),
        }
    }

    fn seek_to_ge(&mut self, target: &[u8]) -> (&'_ Node, &'_ [u8], KeyMetadata, &'_ [u8]) {
        // SAFETY: The skiplist head is guaranteed to be valid as long as the skiplist exists.
        let head = unsafe { &*self.skiplist.head };
        self.current = (head, &[], head.key_metadata, &[]);

        todo!("seek_to_ge is not yet implemented");
    }

    fn seek_to_first(&mut self) {
        // SAFETY: The skiplist head is guaranteed to be valid as long as the skiplist exists.
        let head = unsafe { &*self.skiplist.head };
        self.current = (head, &[], head.key_metadata, &[]);
    }

    fn seek_to_last(&mut self) {
        // SAFETY: The skiplist tail is guaranteed to be valid as long as the skiplist exists.
        let tail = unsafe { &*self.skiplist.tail };
        self.current = (tail, &[], tail.key_metadata, &[]);
    }
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct KeyMetadata(u64);

impl KeyMetadata {
    fn new(kind: KeyKind, seq_num: u64) -> Self {
        // PERF: This assert can be removed if we are sure that the input is always valid.
        assert!(seq_num <= (1 << 56) - 1, "seq_num must be <= 2^56 - 1");
        Self((seq_num << 8) | (kind as u64))
    }

    fn kind(&self) -> KeyKind {
        match (self.0 & 0xFF) as u8 {
            v if v == KeyKind::Delete as u8 => KeyKind::Delete,
            v if v == KeyKind::Set as u8 => KeyKind::Set,
            v => panic!("Invalid key kind in metadata: {}", v),
        }
    }

    fn seq_num(&self) -> u64 {
        self.0 >> 8
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum KeyKind {
    Delete = 0,
    Set = 1,
}

pub enum KeyKindFromRawError {
    InvalidKeyKind,
}

impl TryFrom<u8> for KeyKind {
    type Error = KeyKindFromRawError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(KeyKind::Delete),
            1 => Ok(KeyKind::Set),
            _ => Err(KeyKindFromRawError::InvalidKeyKind),
        }
    }
}

#[derive(Debug, Default)]
#[repr(C)]
struct NodeLinks {
    next_offset: AtomicU32,
    prev_offset: AtomicU32,
}

impl NodeLinks {
    fn init(&self, value: u32) {
        self.next_offset
            .store(value, std::sync::atomic::Ordering::Relaxed);
        self.prev_offset
            .store(value, std::sync::atomic::Ordering::Relaxed);
    }
}

/// A node in the skiplist, which can be at different heights.
///
/// # Encoding scheme
/// - `next_offset`: i32 (4 bytes) - Offset to the next node in the skiplist.
/// - `height`: u8 (1 byte) - Height of the node in the skiplist (0-indexed).
/// - If `height == 0` (base level):
///   - `key_len`: u32 (4 bytes) - Length of the key.
///   - `key`: [u8] (variable length) - The key bytes.
///   - `value`: u64 (8 bytes) - The value associated with the key.
/// - If `height > 0` (higher levels):
///   - `below_offset`: i32 (4 bytes) - Offset to the node below in the skiplist.
///
/// Total size of a highway node: 13 bytes.
/// Total size of a base node: 17 bytes + length of the key.
#[derive(Debug)]
#[repr(C)]
struct Node {
    /// Offset to the start of the key-value data within the arena.
    data_offset: u32,
    /// Size of the key in bytes.
    key_size: u32,
    /// Metadata containing the kind of key and its sequence number.
    key_metadata: KeyMetadata,
    /// Size of the value in bytes.
    value_size: u32,

    _padding: [u8; 4], // Padding to align the next field to 8 bytes

    tower: [NodeLinks; MAX_HEIGHT as usize], // Links for each level in the skiplist
}

const MAX_NODE_SIZE: u32 = std::mem::size_of::<Node>() as u32;

impl Node {
    fn get_key(&self) -> &[u8] {
        // SAFETY: We assume that the arena is valid and that the data_offset
        // points to a valid location within the arena.
        unsafe {
            let key_ptr = (self as *const Node as *const u8).add(self.data_offset as usize);
            std::slice::from_raw_parts(key_ptr, self.key_size as usize)
        }
    }

    fn get_value(&self) -> &[u8] {
        // SAFETY: We assume that the arena is valid and that the data_offset
        // points to a valid location within the arena.
        unsafe {
            let value_ptr = (self as *const Node as *const u8)
                .add(self.data_offset as usize + self.key_size as usize);
            std::slice::from_raw_parts(value_ptr, self.value_size as usize)
        }
    }

    /// Retrieves the absolute offset to the previous node at the given height in the arena.
    /// If there is no previous node, offset is own offset.
    fn prev_offset(&self, height: u8) -> u32 {
        self.tower[height as usize]
            .prev_offset
            .load(std::sync::atomic::Ordering::SeqCst)
    }

    /// Retrieves the offset to the next node at the given height.
    /// If there is no next node, returns 0.
    fn next_offset(&self, height: u8) -> u32 {
        self.tower[height as usize]
            .next_offset
            .load(std::sync::atomic::Ordering::SeqCst)
    }

    fn cas_prev_offset(&self, height: u8, old: u32, new: u32) -> bool {
        self.tower[height as usize]
            .prev_offset
            .compare_exchange(
                old,
                new,
                std::sync::atomic::Ordering::SeqCst,
                std::sync::atomic::Ordering::Relaxed,
            )
            .is_ok()
    }

    fn cas_next_offset(&self, height: u8, old: u32, new: u32) -> bool {
        self.tower[height as usize]
            .next_offset
            .compare_exchange(
                old,
                new,
                std::sync::atomic::Ordering::SeqCst,
                std::sync::atomic::Ordering::Relaxed,
            )
            .is_ok()
    }
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.key_metadata.0 == other.key_metadata.0
            && self.key_size == other.key_size
            && self.value_size == other.value_size
            && self.data_offset == other.data_offset
    }
}

impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.get_key().cmp(&other.get_key()).then({
            self.key_metadata
                .seq_num()
                .cmp(&other.key_metadata.seq_num())
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_key_metadata() {
        let km = KeyMetadata::new(KeyKind::Set, 42);
        assert_eq!(km.kind(), KeyKind::Set);
        assert_eq!(km.seq_num(), 42);
    }

    #[test]
    fn test_node_links() {
        let links = NodeLinks::default();
        links.init(10);
        assert_eq!(
            links.next_offset.load(std::sync::atomic::Ordering::Relaxed),
            10
        );
        assert_eq!(
            links.prev_offset.load(std::sync::atomic::Ordering::Relaxed),
            10
        );
    }

    #[test]
    fn test_skiplist_creation() {
        let arena = Arena::new(1024);
        let skiplist = ArenaSkiplist::new_in(arena);
        assert!(!skiplist.head.is_null());
        assert!(!skiplist.tail.is_null());
    }

    #[test]
    fn test_insert_node_raw() {
        let arena = Arena::new(1024);
        let mut skiplist = ArenaSkiplist::new_in(arena);
        let start_offset = skiplist.arena.get_mut().position();

        let node_ptr = skiplist.insert_node_raw(3, 5, 10).unwrap();
        assert!(!node_ptr.is_null());
        let node = unsafe { &*node_ptr };
        assert_eq!(node.key_size, 5);
        assert_eq!(node.value_size, 10);
    }

    #[test]
    fn test_insert_node() {
        let arena = Arena::new(1024);
        let mut skiplist = ArenaSkiplist::new_in(arena);
        let key = b"test_key";
        let value = b"test_value";
        let seq_num = 1;
        let node_ptr = skiplist.insert_node(2, key, KeyMetadata::new(KeyKind::Set, seq_num), value);
        assert!(node_ptr.is_ok());
        let node = unsafe { &*node_ptr.unwrap() };

        assert_eq!(node.key_size, key.len() as u32);
        assert_eq!(node.value_size, value.len() as u32);
        assert_eq!(node.key_metadata.seq_num(), seq_num);
        assert_eq!(node.key_metadata.kind(), KeyKind::Set);
        assert_eq!(node.get_key(), key);
        assert_eq!(node.get_value(), value);
    }

    #[test]
    fn test_skiplist_iterator() {
        let arena = Arena::new(1024);
        let mut skiplist = Arc::new(ArenaSkiplist::new_in(arena));
        skiplist
            .insert_node(1, b"key1", KeyMetadata::new(KeyKind::Set, 1), b"value1")
            .unwrap();
        let mut iter = ArenaSkiplistIterator::new(skiplist.clone());
        iter.seek_to_first();
        let (node, key, key_metadata, value) = iter.current;
        assert_eq!(key.len(), 0);
        assert_eq!(value.len(), 0);
        assert_eq!(key_metadata.seq_num(), 0);
        assert_eq!(key_metadata.kind(), KeyKind::Delete);
        assert_eq!(node.get_key(), &[]); // Head node has no key
        assert_eq!(node.key_size, 0);
        assert_eq!(node.get_value(), &[]);
        assert_eq!(node.value_size, 0);
    }
}
