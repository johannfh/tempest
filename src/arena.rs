use std::sync::atomic::{AtomicU64, Ordering};

#[derive(Debug, PartialEq)]
pub enum ArenaError {
    OutOfMemory,
}

pub struct Arena {
    buffer: Box<[u8]>,
    position: AtomicU64,
}

impl Arena {
    pub fn new(cap: usize) -> Self {
        assert!(cap > 0, "capacity must be greater than 0");
        assert!(
            cap <= u32::MAX as usize,
            "capacity must be less than or equal to {}",
            u32::MAX
        );
        Self {
            buffer: vec![0; cap].into_boxed_slice(),
            position: 0.into(),
        }
    }

    /// Allocates `n` bytes with the given `align`ment in the arena,
    /// checking for out-of-memory conditions and alignment.
    ///
    /// Returns the offset of the allocated memory on success.
    ///
    /// # Returns
    /// - `Ok(offset)` on success, where `offset` is the offset of the allocated memory.
    /// - `Err(ArenaError::OutOfMemory)` if there is not enough space in the arena.
    ///
    /// # Panics
    /// - if `n` is zero.
    /// - if `align` is not a power of two.
    pub fn alloc(&self, n: u32, align: u32) -> Result<u32, ArenaError> {
        assert!(n > 0, "n must be greater than 0");
        assert!(
            align.is_power_of_two(),
            "align must be a power of two, got {}",
            align
        );

        let align_mask = (align - 1) as u64;
        let capacity = self.buffer.len() as u64;

        loop {
            // read the position at start of the transaction
            let start = self.position.load(Ordering::Relaxed) as u64;

            // compute the aligned start and new position
            let aligned_start = (start + align_mask) & !align_mask;
            let new_position = aligned_start + (n as u64);

            // check for out of memory,
            // this could always occur due to concurrent allocations
            if new_position > capacity {
                return Err(ArenaError::OutOfMemory);
            }

            // TODO: read up on compare_exchange_weak vs strong
            match self.position.compare_exchange_weak(
                start,
                new_position,
                Ordering::SeqCst,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    // CAS succeeded, we have reserved the space
                    return Ok(aligned_start as u32);
                }
                Err(_) => {
                    // CAS failed, another thread modified the position during transaction, retry
                    continue;
                }
            };
        }
    }

    pub fn reset(&mut self) {
        self.position = 0.into();
    }

    /// Returns the current allocation position in the arena.
    /// This is the offset where the next allocation will occur,
    /// + distance to the alignment boundary if needed.
    pub fn position(&self) -> u32 {
        self.position.load(Ordering::Relaxed) as u32
    }

    /// Returns the total capacity of the arena in bytes.
    pub fn capacity(&self) -> u32 {
        self.buffer.len() as u32
    }

    /// Returns the remaining capacity in the arena in bytes.
    /// This is the number of bytes that can still be allocated.
    /// It is equal to `capacity() - position()`.
    pub fn remaining_capacity(&self) -> u32 {
        self.capacity() - self.position()
    }

    /// Returns a pointer into the arena at the given offset.
    ///
    /// # Panics
    /// Panics if the offset is out of bounds, i.e., if `offset >= capacity()`,
    /// to prevent undefined behavior.
    pub fn ptr_at(&self, offset: u32) -> *mut u8 {
        assert!(
            (offset as usize) < self.buffer.len(),
            "index {} out of range",
            offset
        );
        // SAFETY: The offset is guaranteed to be within bounds by the assertion above.
        unsafe { self.buffer.as_ptr().add(offset as usize) as *mut u8 }
    }

    /// Returns a pointer into the arena at the given offset without bounds checking.
    ///
    /// # Safety
    /// The caller must ensure that the offset is within bounds, i.e., `offset < capacity()`.
    /// Failing to do so may lead to undefined behavior.
    pub unsafe fn offset_to_ptr(&self, offset: u32) -> *mut u8 {
        // SAFETY: Caller must ensure offset is within bounds.
        unsafe { self.buffer.as_ptr().add(offset as usize) as *mut u8 }
    }

    pub fn ptr_to_offset(&self, ptr: *const u8) -> Option<u32> {
        let base_ptr = self.buffer.as_ptr();
        // SAFETY: We are only doing pointer arithmetic within the bounds of the buffer.
        let end_ptr = unsafe { base_ptr.add(self.buffer.len()) };

        if ptr >= base_ptr && ptr < end_ptr {
            // SAFETY: checked that ptr is within bounds.
            Some(unsafe { ptr.offset_from(base_ptr) as u32 })
        } else {
            None
        }
    }

    /// Returns the offset of the given pointer from the start of the arena without bounds
    /// checking.
    ///
    /// # Safety
    /// The caller must ensure that the pointer is within bounds, i.e.,
    /// `ptr >= base_ptr && ptr < base_ptr + capacity()`.
    pub unsafe fn offset_of_unchecked(&self, ptr: *const u8) -> u32 {
        let base_ptr = self.buffer.as_ptr();
        // SAFETY: Caller must ensure ptr is within bounds.
        unsafe { ptr.offset_from(base_ptr) as u32 }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arena_alloc() {
        let arena = Arena::new(10);
        arena.alloc(5, 1).unwrap();
        assert_eq!(arena.position(), 5);
        assert_eq!(arena.alloc(6, 1), Err(ArenaError::OutOfMemory));
        assert_eq!(arena.position(), 5); // position should remain unchanged
        arena.alloc(5, 1).unwrap();
        assert_eq!(arena.position(), 10);
    }

    #[test]
    #[should_panic(expected = "n must be greater than 0")]
    fn test_arena_alloc_zero() {
        let arena = Arena::new(10);
        arena.alloc(0, 1).unwrap();
    }

    #[test]
    #[should_panic(expected = "align must be a power of two")]
    fn test_arena_alloc_non_power_of_two_align() {
        let arena = Arena::new(10);
        arena.alloc(5, 3).unwrap();
    }

    #[test]
    fn test_arena_reset() {
        let mut arena = Arena::new(10);
        arena.alloc(5, 1).unwrap();
        assert_eq!(arena.position(), 5);
        arena.reset();
        assert_eq!(arena.position(), 0);
    }

    #[test]
    fn test_arena_ptr_at() {
        let arena = Arena::new(10);
        let offset = arena.alloc(4, 4).unwrap();
        let ptr = arena.ptr_at(offset) as *mut u32;
        unsafe {
            *ptr = 424242;
            assert_eq!(*ptr, 424242);
        }
    }
}
