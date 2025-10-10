use crate::arena::Arena;

use std::{
    cmp,
    sync::{
        Arc,
        atomic::{AtomicU32, Ordering},
    },
};

// An arena-based skiplist implementation.
// It is designed to store key-value pairs in an append-only manner,
// where keys and values are byte slices.
//
// The skiplist is built on top of an `Arena`, which provides efficient
// memory management by allocating a large contiguous block of memory upfront
// and then carving out smaller pieces as needed.
pub(crate) struct ArenaSkiplist {
    arena: Arena,
    head_offset: u32,
    tail_offset: u32,
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
/// set to 0.5 (1 in 2 chance to increase height).
const P: f64 = 0.5;

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

        let arena_capacity = arena.capacity();

        let mut skiplist = ArenaSkiplist {
            arena,
            head_offset: 0,
            tail_offset: 0,
        };

        // Initialize the skiplist with a head node at offset 0
        // The head node has maximum height and no key/value
        trace!(arena_capacity, "initializing skiplist head and tail nodes");
        let (head, head_offset) = skiplist
            .allocate_node(MAX_HEIGHT, 0, 0)
            .expect("Failed to initialize skiplist head node, arena may be too small");

        // Initialize the skiplist with a tail node at offset 0 + sizeof(head)
        // The tail node has maximum height an no key/value
        let (tail, tail_offset) = skiplist
            .allocate_node(MAX_HEIGHT, 0, 0)
            .expect("Failed to initialize skiplist tail node, arena may be too small");

        // Link head with tail at all levels
        // [head] <- head -> [tail]
        // [head] <- tail -> [tail]
        for height in 1..=MAX_HEIGHT as usize {
            // head -> [tail]
            head.tower[height - 1].set_next(&skiplist, tail);
            // [head] <- head
            head.tower[height - 1].set_prev(&skiplist, head);
            // tail -> [tail]
            tail.tower[height - 1].set_next(&skiplist, tail);
            // [head] <- tail
            tail.tower[height - 1].set_prev(&skiplist, head);
        }

        skiplist.head_offset = head_offset;
        skiplist.tail_offset = tail_offset;

        assert_eq!(head_offset, 0, "Head node should be at offset 0");
        trace!(
            head_offset,
            tail_offset,
            arena_position = skiplist.arena.position(),
            arena_capacity = skiplist.arena.capacity(),
            "skiplist initialized"
        );

        skiplist
    }

    fn head(&self) -> &Node {
        // SAFETY: The skiplist head is guaranteed to be valid as long as the skiplist exists.
        unsafe { &*(self.arena.offset_to_ptr(self.head_offset) as *const Node) }
    }

    fn tail(&self) -> &Node {
        // SAFETY: The skiplist tail is guaranteed to be valid as long as the skiplist exists.
        unsafe { &*(self.arena.offset_to_ptr(self.tail_offset) as *const Node) }
    }

    pub(crate) fn insert(
        &self,
        key: &[u8],
        value: Option<&[u8]>,
        seq_num: u64,
    ) -> Result<(), InsertError> {
        assert!(!key.is_empty(), "Key must not be empty");

        // Determine the height of the new node using a probabilistic method.
        // Each level has a probability `P` of being included, up to `MAX_HEIGHT`
        let height = {
            let mut h = 1;
            while h < MAX_HEIGHT && rand::random::<f64>() < P {
                h += 1;
            }
            h
        };

        assert!(height > 0);

        match value {
            Some(v) => self.insert_set(key, v, seq_num, height),
            None => self.insert_delete(key, seq_num, height),
        }
    }

    fn insert_set(
        &self,
        key: &[u8],
        value: &[u8],
        seq_num: u64,
        height: u8,
    ) -> Result<(), InsertError> {
        let key_metadata = KeyMetadata::new(KeyKind::Set, seq_num);
        let node = self.insert_node(height, key, key_metadata, value)?;

        assert_eq!(node.get_key(), key, "Inserted node key mismatch");
        assert_eq!(node.get_value(), value, "Inserted node value mismatch");
        Ok(())
    }

    fn insert_delete(&self, key: &[u8], seq_num: u64, height: u8) -> Result<(), InsertError> {
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
    ) -> Result<&Node, InsertError> {
        assert!(height <= MAX_HEIGHT, "height exceeds MAX_HEIGHT");
        assert!(
            height > 0,
            "height must be in range 1..=MAX_HEIGHT, got: {}",
            height
        );

        let key_size = key.len() as u32;
        assert!(key_size < u32::MAX, "key size is too large");
        let value_size = value.len() as u32;
        assert!(value_size < u32::MAX, "value size is too large");
        let combined_size = Node::expected_size(height, key_size, value_size);
        assert!(
            combined_size <= MAX_ARENA_SIZE as u32,
            "combined key and value size exceeds maximum allowed size"
        );

        let (node, _node_offset) = self.allocate_node(height, key_size, value_size)?;
        let node_ptr = node as *const Node;

        // SAFETY: We have just allocated enough space for the key and value
        // at `node.data_offset`, so this pointer is valid.
        unsafe {
            let key_ptr = (node_ptr as *mut u8).add(node.data_offset as usize);
            let value_ptr = key_ptr.add(key.len());
            std::ptr::copy_nonoverlapping(key.as_ptr(), key_ptr, key.len());
            std::ptr::copy_nonoverlapping(value.as_ptr(), value_ptr, value.len());
        }

        node.key_metadata = key_metadata;

        for h in 1..=height {
            // initialize to 0
            node.tower[h as usize - 1].init(0);

            loop {
                let (pred, succ) = self.find_position_at_level(h, key_metadata.seq_num(), key);
                let pred_ptr = pred as *const Node;
                let succ_ptr = succ as *const Node;

                assert!(
                    pred as *const Node != succ as *const Node,
                    "pred and succ must be different nodes"
                );

                // Ensure the new node's key is between pred/head and succ/tail
                assert!(
                    pred.get_key() <= key, // no need for &[] as &[] is less than any key
                    "pred key must be <= to new key or pred is head"
                );
                assert!(
                    succ.get_key() >= key || succ.get_key() == &[] as &[u8],
                    "succ key must be >= to new key or succ is tail"
                );

                // Link the new node between pred and succ at current level
                if node.link_with(
                    &self.arena,
                    h,
                    self.arena.ptr_to_offset(pred_ptr as *const u8),
                    self.arena.ptr_to_offset(succ_ptr as *const u8),
                ) {
                    // Successfully linked at this level, continue to next level
                    break;
                } else {
                    warn!(
                        "Failed to link node at level {}, retrying linking process",
                        h
                    );
                    continue;
                }
            }
        }

        Ok(node)
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
    // - `Ok((*mut Node, u32)`: A pointer to the newly allocated node and its offset in the arena.
    // - `Err(InsertError)`: If there is not enough memory in the arena.
    ///
    /// # Safety
    /// The caller must not access `node.tower` beyond `height`.
    fn allocate_node(
        &self,
        height: u8,
        key_size: u32,
        value_size: u32,
    ) -> Result<(&mut Node, u32), InsertError> {
        let tower_size = (MAX_HEIGHT - height) as u32 * std::mem::size_of::<NodeLinks>() as u32;
        let node_size = std::mem::size_of::<Node>() as u32 - tower_size; // Size of Node without unused tower links
        let total_size = node_size + key_size + value_size;
        trace!(height, key_size, value_size, total_size, "allocating node");

        // Allocate space for the node and its key/value in the arena
        let node_offset = self
            .arena
            .alloc(total_size, 8)
            .ok_or(InsertError::OutOfMemory(total_size))?;

        // SAFETY: We have just allocated `total_size` bytes at `arena_offset`,
        // giving us a valid pointer into the arena buffer.
        let node_ptr = self.arena.offset_to_ptr(node_offset) as *mut Node;

        // SAFETY: We must not access `node.tower` beyond `height`.
        let node = unsafe { &mut *node_ptr };

        node.data_offset = node_offset + node_size;
        node.key_size = key_size;
        node.value_size = value_size;

        for i in 0..height {
            // initialize to 0
            node.tower[i as usize].init(0);
        }

        //todo!("Linking the new node into the skiplist is not yet implemented");

        // Return the pointer to the newly allocated node
        Ok((node, node_offset))
    }

    pub(crate) fn get(&self, key: &[u8]) -> Option<&[u8]> {
        assert!(!key.is_empty(), "Key must not be empty");

        self.find_node(key).map(|node| node.get_value())
    }

    /// Finds a node with the given key in the skiplist.
    ///
    /// # Arguments
    /// - `key`: The key to search for.
    ///
    /// # Returns
    /// - `Some(&Node)`: A reference to the node if found. Valid as long as the skiplist exists.
    /// - `None`: If the key is not found.
    ///
    /// # Panics
    /// - If the key is empty.
    fn find_node(&self, key: &[u8]) -> Option<&Node> {
        assert!(!key.is_empty(), "Key must not be empty");
        // SAFETY: The skiplist head is guaranteed to be valid as long as the skiplist exists.
        let mut current = self.head();

        for level in (1..=MAX_HEIGHT).rev() {
            loop {
                let next_offset = current.next_offset(level);
                let next_ptr = self.arena.offset_to_ptr(next_offset) as *const Node;

                if next_ptr == self.tail() {
                    // Reached the end of this level, move down
                    break;
                }

                // SAFETY: next_ptr is guaranteed to be valid as long as the skiplist exists.
                let next = unsafe { &*next_ptr };

                match next.get_key().cmp(key) {
                    std::cmp::Ordering::Less => {
                        // Move right at the same level
                        current = next;
                    }
                    std::cmp::Ordering::Equal => {
                        // Found the key
                        return Some(next);
                    }
                    std::cmp::Ordering::Greater => {
                        // Move down one level
                        break;
                    }
                }
            }
        }

        // Key not found
        None
    }

    /// Discards the `ArenaSkiplist`, returning the underlying `Arena` for reuse.
    pub(crate) fn discard(self) -> Arena {
        let mut arena = self.arena;
        arena.reset();
        arena
    }

    fn find_position_at_level(&self, height: u8, seqnum: u64, key: &[u8]) -> (&Node, &Node) {
        trace!(
            height,
            seqnum,
            key = String::from_utf8_lossy(key).as_ref(),
            "finding correct position for insert"
        );
        let mut current = self.head();
        let mut current_height = MAX_HEIGHT;

        let pred: &Node;
        let succ: &Node;

        loop {
            if current as *const Node == self.tail() as *const Node {
                if current_height == height {
                    // Reached the target height, return between current and tail
                    pred = current;
                    succ = self.tail();
                    break;
                } else {
                    // Move down one level to find precise position
                    current_height -= 1;
                    continue;
                }
            }

            let next_offset = current.next_offset(current_height);

            let next_ptr = self.arena.offset_to_ptr(next_offset) as *const Node;

            // SAFETY: next_ptr is guaranteed to be valid as long as the skiplist exists.
            let next: &Node = unsafe { &*next_ptr };

            // first sort by key
            match next
                .get_key()
                .cmp(key)
                // then by sequence number, with highest (newest) first
                .then_with(|| {
                    trace!(
                        this_key = key,
                        next_key = next.get_key(),
                        this_seqnum = &seqnum,
                        next_seqnum = next.key_metadata.seq_num(),
                        "keys equal, sorting by seqnums",
                    );
                    next.key_metadata.seq_num().cmp(&seqnum).reverse()
                }) {
                std::cmp::Ordering::Less => {
                    // Move right at the same level
                    current = next;
                }
                std::cmp::Ordering::Equal => {
                    // TODO: panic here? this is just finding, maybe check and panic in insert?
                    panic!(
                        "duplicate key insertion is not allowed in this skiplist, key: {}, seqnum: {}",
                        String::from_utf8_lossy(key),
                        seqnum
                    );
                }
                std::cmp::Ordering::Greater => {
                    // Found the position to insert before `next`
                    if current_height == height {
                        pred = current;
                        succ = next;
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

impl std::fmt::Debug for ArenaSkiplist {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ArenaSkiplist")
            .field("max_height", &MAX_HEIGHT)
            .field("p", &P)
            // TODO: arena
            // TODO:.field("head", &self.head())
            // TODO: .field("tail", &self.tail())
            // TODO: contents
            .finish()
    }
}

// SAFETY: Arena is safe to insert and read from concurrently without blocking
unsafe impl Send for ArenaSkiplist {}
// SAFETY: Arena is safe to insert and read from concurrently without blocking
unsafe impl Sync for ArenaSkiplist {}

pub(crate) struct ArenaSkiplistIterator<'a> {
    skiplist: &'a ArenaSkiplist,
    height: u8,
    /// Current position in the skiplist, represented as a tuple of:
    /// `(node_ptr, key, key_metadata, value)`.
    current: &'a Node,
}

impl ArenaSkiplistIterator<'_> {
    fn seek_to_ge(&mut self, _target: &[u8]) -> (&'_ Node, &'_ [u8], KeyMetadata, &'_ [u8]) {
        todo!("seek_to_ge is not yet implemented");
    }

    fn seek_to_first(&mut self) {
        self.current = self.skiplist.head();
    }

    fn seek_to_last(&mut self) {
        self.current = self.skiplist.tail();
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
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
        self.next_offset.store(value, Ordering::Relaxed);
        self.prev_offset.store(value, Ordering::Relaxed);
    }

    fn set_prev(&self, skiplist: &ArenaSkiplist, node: &Node) {
        let prev_offset = skiplist
            .arena
            .ptr_to_offset(node as *const Node as *const u8);
        self.prev_offset.store(prev_offset, Ordering::Relaxed);
    }

    fn set_next(&self, skiplist: &ArenaSkiplist, node: &Node) {
        let next_offset = skiplist
            .arena
            .ptr_to_offset(node as *const Node as *const u8);
        self.next_offset.store(next_offset, Ordering::Relaxed);
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

    /// This contains the links for each level in the skiplist,
    /// or rather reduces the need of raw pointer arithmetics
    /// through C-style fixed-length arrays, where array[i]
    /// in T[] corresponds to (&array) + size_of(T) * i.
    ///
    /// While the length is technically always equal to `MAX_HEIGHT`,
    /// meaning you could access up to node.tower[MAX_HEIGHT - 1],
    /// arbitrary access could lead to data corruption in the arena.
    /// The height is known during initialization/linking, where
    /// it is randomly generated, and when searching the list, where
    /// the height slowly decrements, with the `covariant`, that a link
    /// on height X from node A to B means, that B.tower will be at least
    /// X links tall.
    tower: [NodeLinks; MAX_HEIGHT as usize],
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

    fn set_prev(&self, height: u8, skiplist: ArenaSkiplist, node: &Node) {
        self.tower[height as usize - 1].set_prev(&skiplist, node);
    }

    fn set_next(&self, height: u8, skiplist: ArenaSkiplist, node: &Node) {
        self.tower[height as usize - 1].set_next(&skiplist, node);
    }

    /// Retrieves the absolute offset to the previous node at the given height in the arena.
    /// If there is no previous node, offset is own offset.
    #[inline]
    fn prev_offset(&self, height: u8) -> u32 {
        self.next_offset_ptr(height).load(Ordering::Relaxed)
    }

    /// Retrieves the offset to the next node at the given height.
    /// If there is no next node, returns 0.
    #[inline]
    fn next_offset(&self, height: u8) -> u32 {
        self.next_offset_ptr(height).load(Ordering::Relaxed)
    }

    /// Returns a pointer to the `next_offset` atomic for the given height.
    #[inline]
    const fn next_offset_ptr(&self, height: u8) -> &AtomicU32 {
        assert!(height > 0, "height must be in range 1..=MAX_HEIGHT",);
        &self.tower[height as usize - 1].next_offset
    }

    /// Returns a pointer to the `prev_offset` atomic for the given height.
    #[inline]
    const fn prev_offset_ptr(&self, height: u8) -> &AtomicU32 {
        assert!(
            height > 0 && height <= MAX_HEIGHT,
            "height must be in range 1..=MAX_HEIGHT"
        );
        &self.tower[height as usize - 1].prev_offset
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
    ///
    /// # Returns
    /// - true if linking was successful
    /// - false if linking failed and should be retried
    fn link_with(&self, arena: &Arena, height: u8, pred_offset: u32, succ_offset: u32) -> bool {
        assert!(
            height > 0,
            "height must be in range 1..=MAX_HEIGHT, got: {}",
            height
        );
        let self_ptr = self as *const Node;
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
            .store(pred_offset, Ordering::SeqCst);
        self.next_offset_ptr(height)
            .store(succ_offset, Ordering::SeqCst);
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
        let pred_ptr = arena.offset_to_ptr(pred_offset) as *mut Node;
        let succ_ptr = arena.offset_to_ptr(succ_offset) as *mut Node;

        // SAFETY: pred_ptr and succ_ptr are guaranteed to be valid as long as the skiplist exists.
        let (pred_node, succ_node) = unsafe { (&*pred_ptr, &*succ_ptr) };

        // Try to link pred's next to this node
        if pred_node
            .next_offset_ptr(height)
            .compare_exchange(succ_offset, self_offset, Ordering::SeqCst, Ordering::SeqCst)
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
            Ordering::SeqCst,
            Ordering::SeqCst,
        ) {
            // NOTE: Linking succeeded! All four links are connected
            Ok(_) => true,
            Err(actual) => {
                // NOTE: CAS failed, another thread modified succ's prev.
                // This is less critical, we can ignore this failure.
                // It occurs, when another Node finishes linkage between
                // succ and this node, after this node completed stage 2,
                // but before completing stage 3.
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
        let tower_size_remain =
            (MAX_HEIGHT - height) as u32 * std::mem::size_of::<NodeLinks>() as u32;
        let node_size = std::mem::size_of::<Node>() as u32 - tower_size_remain; // Size of Node without unused tower links
        node_size + key_size + value_size
    }
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.key_metadata.eq(&other.key_metadata)
    }
}

impl Eq for Node {}

impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.get_key().cmp(other.get_key()).then({
            // if keys are equal, compare by seq_num in descending order
            // this means that higher seq_num (newer) comes first, so the
            // newest version of a key is found and returned first during search
            self.key_metadata
                .seq_num()
                .cmp(&other.key_metadata.seq_num())
                .reverse()
        }))
    }
}

#[cfg(test)]
mod tests {
    use crate::init;

    use super::*;

    #[test]
    fn test_key_metadata() {
        init!();

        let km = KeyMetadata::new(KeyKind::Set, 42);
        assert_eq!(km.kind(), KeyKind::Set);
        assert_eq!(km.seq_num(), 42);
    }

    #[test]
    fn test_node_links() {
        init!();

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
    fn test_allocate_node() {
        init!();

        let arena = Arena::new(1024);
        let skiplist = ArenaSkiplist::new_in(arena);
        let (node, _node_offset) = skiplist.allocate_node(3, 5, 10).unwrap();
        assert_eq!(node.key_size, 5);
        assert_eq!(node.value_size, 10);
    }

    #[test]
    fn test_insert_node() {
        init!();

        let arena = Arena::new(1024);
        let skiplist = ArenaSkiplist::new_in(arena);
        let key = b"test_key";
        let value = b"test_value";
        let seq_num = 1;
        let node = skiplist
            .insert_node(2, key, KeyMetadata::new(KeyKind::Set, seq_num), value)
            .unwrap();

        assert_eq!(node.key_size, key.len() as u32);
        assert_eq!(node.value_size, value.len() as u32);
        assert_eq!(node.key_metadata.seq_num(), seq_num);
        assert_eq!(node.key_metadata.kind(), KeyKind::Set);
        assert_eq!(node.get_key(), key);
        assert_eq!(node.get_value(), value);
    }

    /*#[test]
    fn test_skiplist_iterator() {
        init!();

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
    }*/

    #[test]
    fn test_node_expected_size() {
        init!();

        let result = Node::expected_size(1, 0, 0);
        assert_eq!(result, 32, "smallest node size must be 32, got: {}", result);
    }
}
