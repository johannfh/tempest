use crate::sync::atomic::{AtomicBool, AtomicU64, Ordering};

pub struct Arena {
    buffer: Box<[u8]>,
    position: AtomicU64,
    /// Current running allocation count
    allocation_count: AtomicU64,
    closed: AtomicBool,
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
            allocation_count: 0.into(),
            closed: false.into(),
        }
    }

    /// Allocates `n` bytes with the given `align`ment in the arena,
    /// checking for out-of-memory conditions and alignment.
    ///
    /// Returns the offset of the allocated memory on success.
    ///
    /// # Returns
    /// - `Some(offset)` on success, where `offset` is the offset of the allocated memory.
    /// - `None` if there is not enough space in the arena or if the arena is closed.
    ///
    /// # Panics
    /// - if `n` is zero.
    /// - if `align` is not a power of two.
    pub fn alloc(&self, n: u64, align: u64) -> Option<u64> {
        trace!("Arena address: {:p}", self as *const Self);
        trace!("Arena::alloc: n={}, align={}", n, align);
        trace!("Arena buffer address: {:p}", self.buffer.as_ptr());
        // if arena is closed, return None
        if self.closed.load(Ordering::SeqCst) {
            return None;
        }

        // increment allocation count, since we're starting an allocation
        // TODO: move this into a seperate function to ensure that allocations
        // to the `offset` are completed before any other processing.
        self.allocation_count.fetch_add(1, Ordering::SeqCst);

        assert!(n > 0, "n must be greater than 0");
        assert!(
            align.is_power_of_two(),
            "align must be a power of two, got {}",
            align
        );

        let align_mask = align - 1;
        let capacity = self.buffer.len() as u64;

        loop {
            // read the position at start of the transaction
            let start = self.position.load(Ordering::Relaxed);

            // compute the aligned start and new position
            let aligned_start = (start + align_mask) & !align_mask;
            let new_position = aligned_start + n;
            trace!(
                "Arena::alloc: start={}, aligned_start={}, new_position={}, n={}, align={}",
                start, aligned_start, new_position, n, align
            );

            // check for out of memory,
            // this could always occur due to concurrent allocations
            if new_position > capacity {
                // decrement allocation count, since allocation failed
                self.allocation_count.fetch_sub(1, Ordering::SeqCst);
                return None;
            }

            // PERF: use weak here, since we're inside a retry loop
            // NOTE: Also known as "compare-and-swap" (CAS)
            // See also: https://en.m.wikipedia.org/wiki/Compare-and-swap
            match self.position.compare_exchange_weak(
                start,
                new_position,
                Ordering::SeqCst,
                Ordering::Relaxed,
            ) {
                // CAS succeeded, we have reserved the space
                Ok(_) => {
                    // decrement allocation count, since allocation is done
                    self.allocation_count.fetch_sub(1, Ordering::SeqCst);
                    return Some(aligned_start);
                }
                // CAS failed, another thread modified the position during transaction, retry
                Err(_) => continue,
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
    /// The caller must ensure that the offset is within bounds.
    ///
    /// # Safety
    /// - Caller must ensure that `offset` is within bounds of the arena.
    /// - Caller must ensure that the returned pointer is not used after the arena is dropped.
    /// - Caller must ensure that the returned pointer is not used after the arena is reset.
    /// - Caller must ensure that the returned pointer is not used after the arena is closed.
    ///
    /// # Panics
    /// - if `offset` is out of bounds of the arena.
    pub fn offset_to_ptr(&self, offset: u64) -> *mut u8 {
        assert!(
            offset < self.buffer.len() as u64,
            "index {} out of range (capacity {})",
            offset,
            self.buffer.len()
        );
        // SAFETY: Caller must ensure offset is within bounds when using
        unsafe { self.buffer.as_ptr().add(offset as usize) as *mut u8 }
    }

    /// Returns a pointer into the arena at the given offset with bounds checking.
    ///
    /// # Panics
    /// - if `ptr` is out of bounds of the arena.
    pub fn ptr_to_offset(&self, ptr: *const u8) -> u64 {
        assert!(
            (ptr as usize) >= (self.buffer.as_ptr() as usize)
                && (ptr as usize) < (self.buffer.as_ptr() as usize + self.buffer.len()),
            "pointer {:p} out of bounds of arena [{:p}, {:p})",
            ptr,
            self.buffer.as_ptr(),
            unsafe { self.buffer.as_ptr().add(self.buffer.len()) }
        );
        let base_ptr = self.buffer.as_ptr();

        //if ptr >= base_ptr && ptr < end_ptr {
        // SAFETY: checked that ptr is within bounds.
        unsafe { ptr.offset_from(base_ptr) as u64 }
    }

    /// Returns true if all allocations have completed.
    /// This means that the allocation count is zero.
    pub fn allocations_complete(&self) -> bool {
        self.allocation_count.load(Ordering::SeqCst) == 0
    }

    /// Prevents any further allocations in the arena.
    /// There may still be ongoing allocations that will complete.
    pub fn close(&self) {
        self.closed.store(true, Ordering::SeqCst);
    }
}

#[cfg(test)]
mod tests {
    use crate::tests::exec;

    use super::*;

    #[test]
    fn test_arena_alloc() {
        let test = || {
            let arena = Arena::new(10);
            arena.alloc(5, 1).unwrap();
            assert_eq!(arena.position(), 5);
            assert_eq!(arena.alloc(6, 1), None);
            assert_eq!(arena.position(), 5); // position should remain unchanged
            arena.alloc(5, 1).unwrap();
            assert_eq!(arena.position(), 10);
        };
        exec(test);
    }

    #[test]
    fn test_arena_alloc_racy() {
        let test = || {
            use crate::sync::Arc;
            use crate::thread;

            let arena = Arc::new(Arena::new(1000));
            let mut handles = vec![];

            for _ in 0..10 {
                let arena = arena.clone();
                let handle = thread::spawn(move || {
                    for _ in 0..100 {
                        let offset = arena.alloc(5, 1).unwrap();
                        let ptr = arena.offset_to_ptr(offset) as *mut u32;
                        unsafe {
                            *ptr = 424242;
                            assert_eq!(*ptr, 424242);
                        }
                    }
                });
                handles.push(handle);
            }

            for handle in handles {
                handle.join().unwrap();
            }

            assert_eq!(arena.position(), 500);
        };
        exec(test);
    }

    #[test]
    #[should_panic(expected = "n must be greater than 0")]
    fn test_arena_alloc_zero() {
        let test = || {
            let arena = Arena::new(10);
            arena.alloc(0, 1).unwrap();
        };
        exec(test);
    }

    #[test]
    #[should_panic(expected = "align must be a power of two")]
    fn test_arena_alloc_non_power_of_two_align() {
        let test = || {
            let arena = Arena::new(10);
            arena.alloc(5, 3).unwrap();
        };
        exec(test);
    }

    #[test]
    fn test_arena_reset() {
        let test = || {
            let mut arena = Arena::new(10);
            arena.alloc(5, 1).unwrap();
            assert_eq!(arena.position(), 5);
            arena.reset();
            assert_eq!(arena.position(), 0);
        };
        exec(test);
    }

    #[test]
    fn test_arena_ptr_at() {
        let test = || {
            let arena = Arena::new(10);
            let offset = arena.alloc(4, 4).unwrap();
            let ptr = arena.offset_to_ptr(offset) as *mut u32;
            unsafe {
                *ptr = 424242;
                assert_eq!(*ptr, 424242);
            }
        };
        exec(test);
    }

    #[test]
    #[should_panic(expected = "index 10 out of range")]
    fn test_arena_ptr_at_out_of_bounds() {
        let test = || {
            let arena = Arena::new(10);
            let _ptr = arena.offset_to_ptr(10);
        };
        exec(test);
    }
}
