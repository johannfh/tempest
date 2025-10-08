use std::sync::atomic::{AtomicU64, Ordering};

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
    /// - `Some(offset)` on success, where `offset` is the offset of the allocated memory.
    /// - `None` if there is not enough space in the arena or if the arena is closed.
    ///
    /// # Panics
    /// - if `n` is zero.
    /// - if `align` is not a power of two.
    pub fn alloc(&self, n: u64, align: u64) -> Option<u64> {
        println!("Arena address: {:p}", self as *const Self);
        println!("Arena::alloc: n={}, align={}", n, align);
        println!("Arena buffer address: {:p}", self.buffer.as_ptr());

        assert!(n > 0, "n must be greater than 0");
        assert!(
            align.is_power_of_two(),
            "align must be a power of two, got {}",
            align
        );

        let align_mask = align - 1;
        let capacity = self.buffer.len() as u64;

        loop {
            let old_pos = self.position();
            let aligned_pos = (old_pos + (align - 1)) & !align_mask;
            let new_pos = aligned_pos.checked_add(n)?;

            // return early if we are out of memory
            if new_pos > capacity {
                return None;
            }

            // try to update the position atomically
            if self
                .position
                .compare_exchange_weak(old_pos, new_pos, Ordering::SeqCst, Ordering::SeqCst)
                .is_ok()
            {
                return Some(aligned_pos);
            }
        }
    }

    pub fn reset(&mut self) {
        self.position.store(0, Ordering::Relaxed);
    }

    /// Returns the current allocation position in the arena.
    /// This is the offset where the next allocation will occur,
    /// + distance to the alignment boundary if needed.
    pub fn position(&self) -> u64 {
        self.position.load(Ordering::Relaxed)
    }

    /// Returns the total capacity of the arena in bytes.
    pub fn capacity(&self) -> u64 {
        self.buffer.len() as u64
    }

    /// Returns the remaining capacity in the arena in bytes.
    /// This is the number of bytes that can still be allocated.
    /// It is equal to `capacity() - position()`.
    pub fn remaining_capacity(&self) -> u64 {
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
        trace!("Arena::offset_to_ptr: offset={}", offset);
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arena_alloc() {
        let arena = Arena::new(10);
        arena.alloc(5, 1).unwrap();
        assert_eq!(arena.position(), 5);
        arena.alloc(4, 1).unwrap();
        // position is not updated on failed alloc
        assert_eq!(arena.position(), 9);
        // 11 > 10, should fail
        assert!(arena.alloc(2, 1).is_none());
    }

    #[test]
    #[should_panic(expected = "n must be greater than 0")]
    fn test_arena_alloc_zero() {
        let arena = Arena::new(10);
        arena.alloc(0, 1);
    }

    #[test]
    #[should_panic(expected = "align must be a power of two")]
    fn test_arena_alloc_non_power_of_two_align() {
        let arena = Arena::new(10);
        arena.alloc(5, 3);
    }

    #[test]
    fn test_arena_reset() {
        let mut arena = Arena::new(1024);
        arena.alloc(5, 1).unwrap();
        assert_eq!(arena.position(), 5);
        arena.reset();
        assert_eq!(arena.position(), 0);
    }

    #[test]
    fn test_arena_offset_to_ptr() {
        let arena = Arena::new(1024);
        let offset = arena.alloc(4, 4).expect("alloc should succeed");
        let ptr = arena.offset_to_ptr(offset) as *mut u32;
        unsafe {
            *ptr = 424242;
            assert_eq!(*ptr, 424242);
        }
    }

    #[test]
    #[should_panic(expected = "index 10 out of range")]
    fn test_arena_offset_to_ptr_oob() {
        let arena = Arena::new(10);
        let _ptr = arena.offset_to_ptr(10);
    }

    #[test]
    fn test_arena_alloc_racy() {
        use std::sync::Arc;
        use std::thread;

        let arena = Arc::new(Arena::new(1024 * 1024));
        let mut handles = vec![];

        for _ in 0..10 {
            let arena = arena.clone();
            let handle = thread::spawn(move || {
                for _ in 0..100 {
                    let offset = arena.alloc(4, 4).unwrap();
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

        let minimum_size = 10 * 100 * 4;
        assert!(
            arena.position() >= minimum_size,
            "all allocations should succeed and allocate at least {} bytes, got {}",
            minimum_size,
            arena.position()
        );
    }
}
