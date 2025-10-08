use crate::arena::Arena;

use std::sync::{Arc, atomic::AtomicU32};

// An arena-based skiplist implementation.
// It is designed to store key-value pairs in an append-only manner,
// where keys and values are byte slices.
//
// The skiplist is built on top of an `Arena`, which provides efficient
// memory management by allocating a large contiguous block of memory upfront
// and then carving out smaller pieces as needed.
pub(crate) struct ArenaSkiplist {
    arena: Arena,
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
pub(crate) enum InsertError {
    /// Not enough memory in the arena to insert the node.
    /// The value is the number of bytes required.
    OutOfMemory(u32),
}

impl ArenaSkiplist {
    /// Creates a new `ArenaSkiplist` with the given `Arena`.
    /// The arena's capacity must not exceed `MAX_ARENA_SIZE`.
    pub(crate) fn new_in(arena: Arena) -> Self {
        assert!(
            arena.capacity() as i32 <= MAX_ARENA_SIZE as i32,
            "Arena capacity exceeds maximum allowed size"
        );

        let mut skip_list = ArenaSkiplist {
            arena,
            head: std::ptr::null_mut(),
            tail: std::ptr::null_mut(),
        };

        // Initialize the skiplist with a head node at offset 0
        // The head node has maximum height and no key/value
        trace!("Initializing skiplist head and tail nodes");
        let head_ptr = skip_list
            .insert_node_raw(MAX_HEIGHT, 0, 0)
            .expect("Failed to initialize skiplist head node, arena may be too small");
        skip_list.head = head_ptr;
        let head_offset = skip_list.arena.ptr_to_offset(head_ptr as *const u8);
        // SAFETY: We must not access `head.tower` beyond `MAX_HEIGHT`.
        let head = unsafe { &*head_ptr };

        let tail_ptr = skip_list
            .insert_node_raw(MAX_HEIGHT, 0, 0)
            .expect("Failed to initialize skiplist tail node, arena may be too small");
        let tail_offset = skip_list.arena.ptr_to_offset(tail_ptr as *const u8);
        // SAFETY: We must not access `tail.tower` beyond `MAX_HEIGHT`.
        let tail = unsafe { &*tail_ptr };

        trace!(
            "Skiplist head node at offset {}, tail node at offset {}, total size {}",
            head_offset,
            tail_offset,
            skip_list.arena.position(),
        );

        let order = std::sync::atomic::Ordering::SeqCst;

        // Link head with tail at all levels
        for height in 0..MAX_HEIGHT {
            head.tower[height as usize].init(0);
            tail.tower[height as usize].init(0);

            head.tower[height as usize]
                .next_offset
                .store(tail_offset as u32, order);
            tail.tower[height as usize]
                .prev_offset
                .store(head_offset as u32, order);
        }

        skip_list.tail = tail_ptr;
        assert_eq!(head_offset, 0, "Head node must be at offset 0");

        skip_list
    }

    pub(crate) fn insert(
        &mut self,
        key: &[u8],
        value: Option<&[u8]>,
        seq_num: u64,
    ) -> Result<(), InsertError> {
        assert!(!key.is_empty(), "Key must not be empty");

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
        assert_eq!(node.get_key(), key, "Inserted node key mismatch");

        // Implementation for linking the new node into the skiplist
        // This is a placeholder and should be replaced with actual logic

        todo!(
            "insert_set is not yet implemented, key: {:?}, value: {:?}, seq_num: {}, height: {}",
            key,
            value,
            seq_num,
            height
        );
    }

    fn insert_delete(&mut self, key: &[u8], seq_num: u64, height: u8) -> Result<(), InsertError> {
        // Implementation for inserting a delete marker
        todo!(
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
        let combined_size = Node::expected_size(height, key_size, value_size);
        assert!(
            combined_size <= MAX_ARENA_SIZE as u32,
            "combined key and value size exceeds maximum allowed size"
        );
        trace!(
            "Inserting node with height {}, key_size {}, value_size {}",
            height, key_size, value_size
        );

        let node_ptr = self.insert_node_raw(height, key_size, value_size)?;

        // SAFETY: We must not access `node.tower` beyond `height`.
        let node = unsafe { &mut (*node_ptr) };

        // SAFETY: We have just allocated enough space for the key and value
        // at `node.data_offset`, so this pointer is valid.
        unsafe {
            let key_ptr = (node as *mut Node as *mut u8).add(node.data_offset as usize);
            let value_ptr = key_ptr.add(key.len());
            std::ptr::copy_nonoverlapping(key.as_ptr(), key_ptr, key.len());
            std::ptr::copy_nonoverlapping(value.as_ptr(), value_ptr, value.len());
        }

        node.key_metadata = key_metadata;

        for h in 0..height {
            // initialize to 0
            node.tower[h as usize].init(0);

            let (pred_ptr, succ_ptr) = self.find_position_at_level(h, key);
            // SAFETY: pred and succ are guaranteed to be valid as long as the skiplist exists
            let (pred, succ) = unsafe { (&*pred_ptr, &*succ_ptr) };

            assert!(
                !pred_ptr.is_null() && !succ_ptr.is_null(),
                "pred and succ must be valid"
            );
            assert!(
                pred_ptr != succ_ptr,
                "pred and succ must be different nodes"
            );

            // Ensure the new node's key is between pred/head and succ/tail
            assert!(
                pred.get_key() < key, // no need for &[] as &[] is less than any key
                "pred key must be less than new key or pred is head"
            );
            assert!(
                succ.get_key() > key || succ.get_key() == &[] as &[u8],
                "succ key must be greater than new key or succ is tail"
            );

            // Link the new node between pred and succ at level i
            loop {
                if node.link_with(
                    &self.arena,
                    h,
                    self.arena.ptr_to_offset(pred_ptr as *const u8) as u32,
                    self.arena.ptr_to_offset(succ_ptr as *const u8) as u32,
                ) {
                    // Successfully linked at this level
                    break;
                } else {
                    // TODO: Retry linking if it failed due to concurrent modifications
                    // we will need to re-find pred and succ
                    todo!(
                        "Failed to link node at level {}, retrying is not implemented",
                        h
                    );
                }
            }
        }

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
        let tower_size = (MAX_HEIGHT - height) as u32 * std::mem::size_of::<NodeLinks>() as u32;
        let node_size = std::mem::size_of::<Node>() as u32 - tower_size; // Size of Node without unused tower links
        let total_size = node_size + key_size + value_size;
        trace!(
            "Allocating node: height {}, key_size {}, value_size {}, total_size {}",
            height, key_size, value_size, total_size
        );

        // Allocate space for the node and its key/value in the arena
        let arena_offset = self
            .arena
            .alloc(total_size as u64, 8)
            .ok_or(InsertError::OutOfMemory(total_size))?;

        // SAFETY: We have just allocated `total_size` bytes at `arena_offset`,
        // giving us a valid pointer into the arena buffer.
        let node_ptr = self.arena.offset_to_ptr(arena_offset) as *mut Node;

        // SAFETY: We must not access `node.tower` beyond `height`.
        let node = unsafe { &mut *node_ptr };
        node.data_offset = arena_offset as u32 + node_size;
        node.key_size = key_size;
        node.value_size = value_size;

        for i in 0..height {
            // initialize to 0
            node.tower[i as usize].init(0);
        }

        //todo!("Linking the new node into the skiplist is not yet implemented");

        // Return the pointer to the newly allocated node
        Ok(node_ptr)
    }

    /// Discards the `ArenaSkiplist`, returning the underlying `Arena` for reuse.
    pub(crate) fn discard(self) -> Arena {
        let mut arena = self.arena;
        arena.reset();
        arena
    }

    fn find_position_at_level(&self, height: u8, key: &[u8]) -> (*mut Node, *mut Node) {
        // find the correct position to insert the new node
        // and link it into the skiplist
        let tail_offset = self.arena.ptr_to_offset(self.tail as *const u8) as u32;

        let mut current_ptr = self.head;
        let mut current_height = MAX_HEIGHT - 1;

        let pred: *mut Node;
        let succ: *mut Node;

        loop {
            // SAFETY: current is guaranteed to be valid as long as the skiplist exists.
            let current: &Node = unsafe { &*current_ptr };

            let next_offset = current.next_offset(current_height);
            if next_offset == tail_offset {
                if current_height == height {
                    // Reached the target height, return between current and tail
                    pred = current_ptr;
                    succ = self.tail;
                    break;
                } else {
                    // Move down one level to find precise position
                    current_height -= 1;
                    continue;
                }
            }

            let next_ptr = self.arena.offset_to_ptr(next_offset as u64) as *mut Node;

            // SAFETY: next_ptr is guaranteed to be valid as long as the skiplist exists.
            let next: &Node = unsafe { &*next_ptr };

            match next.get_key().cmp(key) {
                std::cmp::Ordering::Less => {
                    // Move right at the same level
                    current_ptr = next_ptr;
                }
                std::cmp::Ordering::Equal => {
                    if current_height == height {
                        // TODO: panic here? this is just finding, maybe check and panic in insert?
                        panic!("Duplicate key insertion is not allowed in this skiplist");
                    } else {
                        // Move down one level to find precise position
                        current_height -= 1;
                        continue;
                    }
                }
                std::cmp::Ordering::Greater => {
                    // Found the position to insert before `next`
                    if current_height == 0 {
                        pred = current_ptr;
                        succ = next_ptr;
                        break;
                    } else {
                        // Move down one level to find precise position
                        current_height -= 1;
                        continue;
                    }
                }
            }
        }

        (pred, succ)
    }
}

unsafe impl Send for ArenaSkiplist {}
unsafe impl Sync for ArenaSkiplist {}

pub(crate) struct ArenaSkiplistIterator<'a> {
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

    fn seek_to_ge(&mut self, _target: &[u8]) -> (&'_ Node, &'_ [u8], KeyMetadata, &'_ [u8]) {
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
pub(crate) struct KeyMetadata(u64);

impl KeyMetadata {
    fn new(kind: KeyKind, seq_num: u64) -> Self {
        // PERF: This assert can be removed if we are sure that the input is always valid.
        assert!(seq_num < (1 << 56), "seq_num must be < 2^56");
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
pub(crate) enum KeyKind {
    Delete = 0,
    Set = 1,
}

pub(crate) enum KeyKindFromRawError {
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
    #[inline]
    fn prev_offset(&self, height: u8) -> u32 {
        self.next_offset_ptr(height)
            .load(std::sync::atomic::Ordering::Relaxed)
    }

    /// Retrieves the offset to the next node at the given height.
    /// If there is no next node, returns 0.
    #[inline]
    fn next_offset(&self, height: u8) -> u32 {
        self.next_offset_ptr(height)
            .load(std::sync::atomic::Ordering::Relaxed)
    }

    /// Returns a pointer to the `next_offset` atomic for the given height.
    #[inline]
    const fn next_offset_ptr(&self, height: u8) -> &AtomicU32 {
        &self.tower[height as usize].next_offset
    }

    /// Returns a pointer to the `prev_offset` atomic for the given height.
    #[inline]
    const fn prev_offset_ptr(&self, height: u8) -> &AtomicU32 {
        &self.tower[height as usize].prev_offset
    }

    /// Links this node with the given predecessor and successor at the specified height.
    /// Returns `true` if the linking was successful, `false` otherwise.
    /// This method uses atomic operations to ensure thread safety.
    /// The caller must ensure that `pred` and `succ` are valid offsets
    /// within the arena.
    ///
    /// # Arguments
    /// - `arena`: The arena where the nodes are stored.
    /// - `height`: The height at which to link the nodes.
    /// - `pred`: The offset of the predecessor node.
    /// - `succ`: The offset of the successor node.
    fn link_with(&self, arena: &Arena, height: u8, pred_offset: u32, succ_offset: u32) -> bool {
        let self_ptr = self as *const Node as *mut Node;
        let self_offset = arena.ptr_to_offset(self_ptr as *const u8) as u32;
        trace!(
            "Linking node at height {}: self_offset {}, pred_offset {}, succ_offset {}",
            height, self_offset, pred_offset, succ_offset
        );

        // NOTE: Phase 1 - 'prepare':
        // Set this node's prev and next offsets to point to pred and succ.
        // This must be done before 'publishing' the new node to the list.
        // Else, other threads may see a partially linked node, resulting in
        // incorrect traversal behavior.
        self.prev_offset_ptr(height)
            .store(pred_offset, std::sync::atomic::Ordering::SeqCst);
        self.next_offset_ptr(height)
            .store(succ_offset, std::sync::atomic::Ordering::SeqCst);
        trace!(
            "Prepared node at height {}: self_offset {}, prev_offset {}, next_offset {}",
            height,
            self_offset,
            self.prev_offset(height),
            self.next_offset(height)
        );

        // NOTE: Phase 2 - 'publish':
        // Now, we need to update pred's next to point to this node,
        // and succ's prev to point to this node.
        // This will 'publish' the new node to the list.
        // We must use compare-and-swap (CAS) operations to ensure that
        // we do not overwrite changes made by other threads.
        // SAFETY: We assume that pred and succ are valid offsets within the arena.
        let pred_ptr = arena.offset_to_ptr(pred_offset as u64) as *mut Node;
        let succ_ptr = arena.offset_to_ptr(succ_offset as u64) as *mut Node;

        // SAFETY: pred_ptr and succ_ptr are guaranteed to be valid as long as the skiplist exists.
        let (pred_node, succ_node) = unsafe { (&*pred_ptr, &*succ_ptr) };

        // Try to link pred's next to this node
        if pred_node
            .next_offset_ptr(height)
            .compare_exchange(
                succ_offset,
                self_offset,
                std::sync::atomic::Ordering::SeqCst,
                std::sync::atomic::Ordering::SeqCst,
            )
            .is_err()
        {
            // CAS failed, another thread modified pred's next, we need to abort and retry
            return false;
        };

        trace!(
            "Linked pred's next at height {}: pred_offset {}, next_offset {}",
            height,
            pred_offset,
            pred_node.next_offset(height)
        );

        // NOTE: Phase 3:
        // Now, we need to link succ's prev to this node.
        // This must be done after linking pred's next to ensure that
        // the list remains consistent during concurrent modifications.
        // Linking succ's prev is done through CAS as well, but failure here
        // is handled differently.
        // If the CAS fails, it means another thread modified succ's prev,
        // by inserting another node between this node and succ.
        // This can be ignored, as the list remains consistent.
        // The new node will still be reachable through pred's next pointer.
        // We log a warning for debugging purposes, but do not retry.
        match succ_node.prev_offset_ptr(height).compare_exchange(
            pred_offset,
            self_offset,
            std::sync::atomic::Ordering::SeqCst,
            std::sync::atomic::Ordering::SeqCst,
        ) {
            Ok(_) => {
                // Linking succeeded
                true
            }
            Err(actual) => {
                // CAS failed, another thread modified succ's prev.
                // This is less critical, we can ignore this failure.
                warn!(
                    "Linking succ's prev failed, actual prev_offset was {}, expected {}",
                    actual, pred_offset
                );
                true
            }
        }
    }

    /// Calculates the expected size of a node given its height, key size, and value size,
    /// when allocating it inside of the skiplist arena.
    #[inline]
    const fn expected_size(height: u8, key_size: u32, value_size: u32) -> u32 {
        let tower_size = (MAX_HEIGHT - height) as u32 * std::mem::size_of::<NodeLinks>() as u32;
        let node_size = std::mem::size_of::<Node>() as u32 - tower_size; // Size of Node without unused tower links
        node_size + key_size + value_size
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
        Some(self.get_key().cmp(other.get_key()).then({
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
        let skiplist = ArenaSkiplist::new_in(arena);

        let node_ptr = skiplist.insert_node_raw(3, 5, 10).unwrap();
        assert!(!node_ptr.is_null());
        let node = unsafe { &*node_ptr };
        assert_eq!(node.key_size, 5);
        assert_eq!(node.value_size, 10);
    }

    #[test]
    fn test_insert_node() {
        let arena = Arena::new(1024);
        let skiplist = ArenaSkiplist::new_in(arena);
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
        let skiplist = Arc::new(ArenaSkiplist::new_in(arena));
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
