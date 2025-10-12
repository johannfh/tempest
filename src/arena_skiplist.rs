use std::sync::atomic::AtomicU32;

use crate::arena::Arena;

/// Maximum height of the skiplist.
pub const MAX_HEIGHT: u8 = 12;
/// Probability of increasing the height of a node.
pub const P: f64 = 0.25;

/// Stores the links for a node in the skiplist.
/// Each node has a `next` and `prev` pointer.
/// They are represented as offsets into the arena.
/// The `prev` pointer allows for efficient reverse traversal.
#[repr(C)]
struct NodeLink {
    prev: AtomicU32,
    next: AtomicU32,
}

impl NodeLink {
    fn prev(&self) -> u32 {
        self.prev.load(std::sync::atomic::Ordering::SeqCst)
    }

    fn next(&self) -> u32 {
        self.next.load(std::sync::atomic::Ordering::SeqCst)
    }

    fn set_prev(&self, skiplist: &ArenaSkiplist, prev: &Node) {
        let prev_offset = skiplist.arena.ref_to_offset(prev);
        self.prev
            .store(prev_offset, std::sync::atomic::Ordering::SeqCst);
    }

    fn set_next(&self, skiplist: &ArenaSkiplist, next: &Node) {
        let next_offset = skiplist.arena.ref_to_offset(next);
        self.next
            .store(next_offset, std::sync::atomic::Ordering::SeqCst);
    }
}

/// Type of the key-value entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum KeyKind {
    /// A regular key-value entry.
    Value = 0,
    /// A deletion marker for a key.
    Deletion = 1,
}

impl From<u8> for KeyKind {
    fn from(value: u8) -> Self {
        match value {
            0 => KeyKind::Value,
            1 => KeyKind::Deletion,
            _ => panic!("invalid key kind"),
        }
    }
}

#[repr(transparent)]
pub(crate) struct KeyTrailer(u64);

impl KeyTrailer {
    fn new(seqnum: u64, kind: KeyKind) -> Self {
        Self(seqnum << 8 | (kind as u64))
    }

    fn seqnum(&self) -> u64 {
        self.0 >> 8
    }

    fn kind(&self) -> KeyKind {
        KeyKind::from((self.0 & 0xff) as u8)
    }
}

#[repr(C)]
struct Node {
    /// Offset to the key-value data in the arena.
    data_offset: u32,
    /// Length of the key.
    key_size: u32,
    /// Metadata about the key (e.g. type, seqnum)
    key_trailer: KeyTrailer,
    /// Length of the value.
    value_size: u32,
    // padding for alignment
    _padding: [u8; 4],

    /// Links for each level of the skiplist.
    /// `links[0]` is the lowest level (level `1`).
    /// `links[MAX_HEIGHT - 1]` is the highest level (level `MAX_HEIGHT`).
    links: [NodeLink; MAX_HEIGHT as usize],
}

impl Node {
    /// Calculates the size of a node with the given height.
    /// This is the size of the `Node` struct minus the size of the unused [`NodeLink`]s.
    #[inline]
    const fn size_node(height: u8) -> u32 {
        let unused_links_size =
            (MAX_HEIGHT - height) as u32 * std::mem::size_of::<NodeLink>() as u32;
        let node_size = std::mem::size_of::<Node>() as u32;
        node_size - unused_links_size
    }

    /// Calculates the size of the key-value data.
    /// This is the sum of the key size and value size.
    #[inline]
    const fn size_data(key_size: u32, value_size: u32) -> u32 {
        key_size + value_size
    }

    /// Calculates the total size of a node with the given height and key-value data sizes.
    /// This is the sum of the node size and the key-value data size.
    #[inline]
    const fn size_total(height: u8, key_size: u32, value_size: u32) -> u32 {
        Self::size_node(height) + Self::size_data(key_size, value_size)
    }

    fn prev(&self, height: u8) -> u32 {
        assert!(height > 0 && height <= MAX_HEIGHT, "invalid height");
        self.links[height as usize - 1].prev()
    }

    fn next(&self, height: u8) -> u32 {
        assert!(height > 0 && height <= MAX_HEIGHT, "invalid height");
        self.links[height as usize - 1].next()
    }

    fn set_prev(&self, skiplist: &ArenaSkiplist, height: u8, prev: &Node) {
        assert!(height > 0 && height <= MAX_HEIGHT, "invalid height");
        self.links[height as usize - 1].set_prev(skiplist, prev);
    }

    fn set_next(&self, skiplist: &ArenaSkiplist, height: u8, next: &Node) {
        assert!(height > 0 && height <= MAX_HEIGHT, "invalid height");
        self.links[height as usize - 1].set_next(skiplist, next);
    }

    fn prev_atomic(&self, height: u8) -> &AtomicU32 {
        &self.links[height as usize - 1].prev
    }

    fn next_atomic(&self, height: u8) -> &AtomicU32 {
        &self.links[height as usize - 1].next
    }

    /// Returns a slice of the key.
    fn key(&self) -> &[u8] {
        // SAFETY: key_size is set at allocation time and should be valid.
        let ptr = self as *const Node as *const u8;
        unsafe {
            std::slice::from_raw_parts(ptr.add(self.data_offset as usize), self.key_size as usize)
        }
    }

    /// Returns a slice of the value.
    fn value(&self) -> &[u8] {
        // SAFETY: value_size is set at allocation time and should be valid.
        unsafe {
            std::slice::from_raw_parts(
                (self as *const Node as *const u8)
                    .add(self.data_offset as usize + self.key_size as usize),
                self.value_size as usize,
            )
        }
    }

    fn set_key(&mut self, key: &[u8]) {
        assert!(
            key.len() as u32 == self.key_size,
            "key length must match allocated size"
        );
        // SAFETY: key_size is set at allocation time and should be valid.
        let self_ptr = self as *mut Node as *mut u8;
        unsafe {
            let dst = self_ptr.add(self.data_offset as usize);
            std::ptr::copy_nonoverlapping(key.as_ptr(), dst, self.key_size as usize);
        }
    }

    fn set_value(&mut self, value: &[u8]) {
        assert!(
            value.len() as u32 == self.value_size,
            "value length must match allocated size"
        );
        // SAFETY: value_size is set at allocation time and should be valid.
        let self_ptr = self as *mut Node as *mut u8;
        unsafe {
            let dst = self_ptr.add(self.data_offset as usize + self.key_size as usize);
            std::ptr::copy_nonoverlapping(value.as_ptr(), dst, self.value_size as usize);
        }
    }
}

#[derive(Debug)]
pub(crate) enum InsertError {
    /// The skiplist is out of memory.
    /// The value is the requested size in bytes for the node.
    OutOfMemory(u32),
}

pub(crate) struct ArenaSkiplist {
    arena: Arena,
    head_offset: u32,
    tail_offset: u32,
}

impl ArenaSkiplist {
    pub(crate) fn new_in(arena: Arena) -> Self {
        let required_size = std::mem::size_of::<Node>() as u32 * 2;
        let capacity = arena.capacity();
        assert!(
            capacity >= required_size,
            "arena must be large enough to hold at least two nodes (head and tail), got capacity {}, required {}",
            capacity,
            required_size
        );

        let mut skiplist = ArenaSkiplist {
            arena,
            head_offset: 0,
            tail_offset: 0,
        };

        let (head, head_offset) = skiplist
            .allocate_node(MAX_HEIGHT, 0, 0)
            .expect("allocate head node");

        let (tail, tail_offset) = skiplist
            .allocate_node(MAX_HEIGHT, 0, 0)
            .expect("allocate tail node");

        // Set the head and tail links
        // [<-> [head] <-> [tail] <->]
        for height in 1..=MAX_HEIGHT {
            head.set_prev(&skiplist, height, head);
            head.set_next(&skiplist, height, tail);
            tail.set_prev(&skiplist, height, head);
            tail.set_next(&skiplist, height, tail);
        }

        skiplist.head_offset = head_offset;
        skiplist.tail_offset = tail_offset;

        skiplist
    }

    /// Discards the skiplist and returns the underlying arena.
    /// The arena is reset to its initial state, allowing for reuse.
    pub(crate) fn discard(self) -> Arena {
        let mut arena = self.arena;
        arena.reset();
        arena
    }

    fn allocate_node(
        &self,
        height: u8,
        key_size: u32,
        value_size: u32,
    ) -> Result<(&mut Node, u32), InsertError> {
        // calculate the total size needed for the node and its data
        let size_total = Node::size_total(height, key_size, value_size);

        // allocate memory for the node and its data
        let offset = self
            .arena
            .alloc(size_total, std::mem::align_of::<Node>() as u32)
            .ok_or(InsertError::OutOfMemory(size_total))?;
        let node = self.arena.get_mut::<Node>(offset);

        // data section begins right after the node struct
        let size_node = Node::size_node(height);
        node.data_offset = offset + size_node;
        node.key_size = key_size;
        node.value_size = value_size;
        trace!(
            offset,
            size_total, size_node, key_size, value_size, "allocated node in skiplist",
        );
        Ok((node, offset))
    }

    /// Finds the position to insert a new node at the specified height.
    ///
    /// # Returns
    /// A tuple of references to the previous and next nodes, along with their offsets.
    /// The new node should be inserted between these two nodes.
    /// `(prev, prev_offset, next, next_offset)`
    ///
    /// # Panics
    /// - if the target height is invalid (not in `1..=MAX_HEIGHT`).
    /// - if a duplicate key-seqnum pair is found in the skiplist.
    fn find_insert_position(&self, node: &Node, target_height: u8) -> (&Node, u32, &Node, u32) {
        assert!(
            target_height > 0 && target_height <= MAX_HEIGHT,
            "invalid height"
        );

        trace!(
            target_height,
            node_key = String::from_utf8_lossy(node.key()).as_ref(),
            node_seqnum = node.key_trailer.seqnum(),
            "finding insert position in skiplist"
        );

        // traverse the skiplist from top to bottom
        let mut current_height = MAX_HEIGHT;

        // start from the head node
        let mut prev_offset = self.head_offset;
        let mut prev = self.arena.get::<Node>(prev_offset);
        loop {
            // get the next node at the current height
            let next_offset = prev.next(current_height);
            let next = self.arena.get::<Node>(next_offset);

            if next_offset == self.tail_offset {
                if current_height == target_height {
                    // found the position at height to insert the node at
                    trace!(
                        current_height,
                        target_height, prev_offset, next_offset, "found insert position"
                    );
                    return (prev, prev_offset, next, next_offset);
                } else {
                    // move down one level
                    trace!(current_height, prev_offset, next_offset, "moving down");
                    current_height -= 1;
                    continue;
                }
            }

            // compare keys and seqnums to find the correct position
            match node
                // sort ascending by key
                .key()
                .cmp(next.key())
                // sort descending by seqnum for same keys
                .then_with(|| {
                    node.key_trailer
                        .seqnum()
                        .cmp(&next.key_trailer.seqnum())
                        .reverse()
                }) {
                std::cmp::Ordering::Less => {
                    if current_height == target_height {
                        // found the position at height to insert the node at
                        trace!(
                            current_height,
                            target_height, prev_offset, next_offset, "found insert position"
                        );
                        return (prev, prev_offset, next, next_offset);
                    } else {
                        // move down one level
                        current_height -= 1;
                        continue;
                    }
                }
                std::cmp::Ordering::Greater => {
                    // current has a larger seqnum, so move to the next node
                    prev_offset = next_offset;
                    prev = next;
                    continue;
                }
                std::cmp::Ordering::Equal => {
                    // keys and seqnums are equal, this should not happen in a well-formed skiplist
                    // TODO: This function assumes that the skiplist is well-formed and does not contain duplicate
                    // key-seqnum pairs. If such a pair is found, the function will panic.
                    // This is a simplification for this implementation and should be handled properly
                    // in a production system (e.g., by returning an error).
                    panic!(
                        "duplicate key-seqnum-pair found in skiplist, key: {:?}, seqnum: {}, height: {}",
                        String::from_utf8_lossy(node.key()),
                        node.key_trailer.seqnum(),
                        target_height
                    );
                }
            }
        }
    }

    fn link_node_at_height(&self, node: &Node, height: u8) {
        assert!(height > 0 && height <= MAX_HEIGHT, "invalid height");
        let node_offset = self.arena.ref_to_offset(node);
        loop {
            // find the position to insert the node at height `h`
            let (prev, prev_offset, next, next_offset) = self.find_insert_position(node, height);

            // set the outgoing links of the node
            node.set_prev(self, height, prev);
            node.set_next(self, height, next);

            // CAS loop to update the previous node's next link to point to the new node
            match node.prev_atomic(height).compare_exchange_weak(
                prev_offset,
                self.arena.ref_to_offset(node),
                std::sync::atomic::Ordering::SeqCst,
                std::sync::atomic::Ordering::SeqCst,
            ) {
                Ok(_) => {
                    // successfully updated the previous node's next link
                    trace!(
                        height,
                        node_offset, prev_offset, "linked node successfully: prev -> this"
                    );
                }
                Err(atomic_value) => {
                    // failed to update, retry finding the position
                    trace!(
                        height,
                        node_offset,
                        prev_offset,
                        atomic_value,
                        "failed to link nodes: prev -> this, retrying"
                    );
                    continue;
                }
            }

            match node.next_atomic(height).compare_exchange(
                next_offset,
                self.arena.ref_to_offset(node),
                std::sync::atomic::Ordering::SeqCst,
                std::sync::atomic::Ordering::SeqCst,
            ) {
                Ok(_) => {
                    // successfully updated the next node's previous link
                    trace!(
                        height = height,
                        node_offset, next_offset, "linked node successfully: this <- next"
                    );
                }
                Err(atomic_value) => {
                    // failed to update, this is fine, since it means another thread already
                    // inserted a node between this and next and updated next's prev link
                    trace!(
                        height = height,
                        node_offset,
                        next_offset,
                        atomic_value,
                        "failed to link nodes: this <- next, proceeding"
                    );
                }
            }

            // successfully linked at this height
            return;
        }
    }

    fn link_node(&self, node: &Node, height: u8) {
        let node_offset = self.arena.ref_to_offset(node);
        trace!(
            node_offset,
            height,
            node_key = String::from_utf8_lossy(node.key()).as_ref(),
            node_seqnum = node.key_trailer.seqnum(),
            "linking node into skiplist",
        );
        for h in 1..=height {
            self.link_node_at_height(node, h);
            trace!(node_offset, h, "linked node at height");
        }
    }

    /// Inserts a new key-value pair into the skiplist with the specified height.
    /// This function is used for testing purposes to allow deterministic heights.
    ///
    /// For outside use, [`Self::insert()`] is available, which uses a probabilistic
    /// method to determine the height based on a fixed probability `P`.
    fn insert_impl(
        &self,
        key: &[u8],
        key_trailer: KeyTrailer,
        value: &[u8],
        height: u8,
    ) -> Result<(), InsertError> {
        let key_size = key.len() as u32;
        let value_size = value.len() as u32;

        assert!(
            key_trailer.kind() != KeyKind::Deletion || value_size == 0,
            "deletion marker must have empty value"
        );

        trace!(
            seqnum = key_trailer.seqnum(),
            kind = ?key_trailer.kind(),
            key = String::from_utf8_lossy(key).as_ref(),
            value = String::from_utf8_lossy(value).as_ref(),
            height,
            "inserting key-value pair into skiplist",
        );

        // allocate a new node in the arena
        let (node, node_offset) = self.allocate_node(height, key_size, value_size)?;

        // copy key and value into the node's data section
        let key_offset = node.data_offset;
        let value_offset = key_offset + key.len() as u32;

        node.set_key(key);
        node.set_value(value);

        trace!(
            node_offset,
            seqnum = key_trailer.seqnum(),
            kind = ?key_trailer.kind(),
            key_offset,
            key = String::from_utf8_lossy(key).as_ref(),
            key_raw = key,
            value_offset,
            value = String::from_utf8_lossy(value).as_ref(),
            value_raw = value,
            height,
            "initialized node for linkage",
        );

        assert_eq!(node.key(), key, "key should be copied correctly");
        assert_eq!(node.value(), value, "value should be copied correctly");

        self.link_node(node, height);

        Ok(())
    }

    pub(crate) fn insert(
        &self,
        key: &[u8],
        key_trailer: KeyTrailer,
        value: &[u8],
    ) -> Result<(), InsertError> {
        // determine the height of the new node using a probabilistic method
        let mut height = 1;
        while height < MAX_HEIGHT && rand::random::<f64>() < P {
            height += 1;
        }

        self.insert_impl(key, key_trailer, value, height)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init;

    #[test]
    fn test_node_size() {
        init!();

        assert_eq!(
            Node::size_node(MAX_HEIGHT),
            std::mem::size_of::<Node>() as u32,
            "node size with max height should be equal to size of Node struct"
        );
    }

    #[test]
    fn test_allocate_node() {
        init!();

        let arena = Arena::new(1024);
        let skiplist = ArenaSkiplist::new_in(arena);
        let old_pos = skiplist.arena.position();

        let (_node, _node_offset) = skiplist.allocate_node(4, 10, 20).unwrap();
        assert_eq!(
            skiplist.arena.position(),
            old_pos + Node::size_total(4, 10, 20),
            "arena position should advance by the size of the allocated node"
        );
    }

    #[test]
    fn test_insert_impl() {
        init!();

        let arena = Arena::new(4096);
        let skiplist = ArenaSkiplist::new_in(arena);

        let key = b"key1";
        let value = b"value1";
        let key_trailer = KeyTrailer::new(1, KeyKind::Value);
        skiplist.insert_impl(key, key_trailer, value, 2).unwrap();

        let key2 = b"key2";
        let value2 = b"value2";
        let key_trailer2 = KeyTrailer::new(2, KeyKind::Value);
        skiplist.insert_impl(key2, key_trailer2, value2, 3).unwrap();

        let key3 = b"key1"; // same key as key1 but higher seqnum
        let value3 = b"value3";
        let key_trailer3 = KeyTrailer::new(3, KeyKind::Value);
        skiplist.insert_impl(key3, key_trailer3, value3, 1).unwrap();
    }
}
