use std::sync::atomic::{AtomicU32, Ordering};

pub(crate) const MAX_ARENA_SIZE: u32 = u32::MAX;

pub(crate) struct Arena {
    buffer: Box<[u8]>,
    position: AtomicU32,
}

impl Arena {
    pub(crate) fn new(cap: usize) -> Self {
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
    #[instrument(name = "arena_alloc", level = "trace", skip_all, fields(
        size = n,
        align,
    ))]
    pub(crate) fn alloc(&self, n: u32, align: u32) -> Option<u32> {
        assert!(n > 0, "n must be greater than 0");
        assert!(
            align.is_power_of_two(),
            "align must be a power of two, got {}",
            align
        );

        let align_mask = align - 1;
        let capacity = self.capacity();

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
                let remaining_capacity = capacity - new_pos;

                trace!(
                    size = n,
                    align,
                    old_pos,
                    aligned_pos,
                    new_pos,
                    capacity,
                    remaining_capacity,
                    "allocated memory in arena",
                );
                return Some(aligned_pos);
            }
        }
    }

    #[inline]
    pub(crate) fn reset(&mut self) {
        self.position.store(0, Ordering::SeqCst);
    }

    /// Returns the current allocation position in the arena.
    /// This is the offset where the next allocation will occur,
    /// + distance to the alignment boundary if needed.
    #[inline]
    pub(crate) fn position(&self) -> u32 {
        self.position.load(Ordering::SeqCst)
    }

    /// Returns the total capacity of the arena in bytes.
    #[inline]
    pub(crate) fn capacity(&self) -> u32 {
        self.buffer.len() as u32
    }

    /// Returns the remaining capacity in the arena in bytes.
    /// This is the number of bytes that can still be allocated.
    /// It is equal to `capacity() - position()`.
    #[inline]
    pub(crate) fn remaining_capacity(&self) -> u32 {
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
    #[inline]
    pub(crate) fn offset_to_ptr(&self, offset: u32) -> *mut u8 {
        assert!(
            offset < self.buffer.len() as u32,
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
    /// - if `ptr` is not within bounds
    #[inline]
    pub(crate) fn ptr_to_offset(&self, ptr: *const u8) -> u32 {
        assert!(
            ptr >= self.buffer.as_ptr()
                // SAFETY: performing ptr arithmetic within the bounds of the buffer
                && ptr < unsafe { self.buffer.as_ptr().add(self.buffer.len()) },
            "pointer {:p} out of bounds (capacity {})",
            ptr,
            self.buffer.len()
        );
        let base_ptr = self.buffer.as_ptr();

        // SAFETY: checked that ptr is within bounds.
        unsafe { ptr.offset_from(base_ptr) as u32 }
    }

    pub(crate) fn ref_to_offset<T>(&self, r: &T) -> u32 {
        self.ptr_to_offset(r as *const T as *const u8)
    }

    pub(crate) fn offset_to_ref<T>(&self, offset: u32) -> &T {
        self.get(offset)
    }

    pub(crate) fn offset_to_ref_mut<T>(&self, offset: u32) -> &mut T {
        self.get_mut(offset)
    }

    /// Returns a reference to a value of type `T` at the given offset.
    ///
    /// # Safety
    /// - Caller must ensure that `offset` is within bounds of the arena.
    #[inline]
    pub(crate) fn get<T: Sized>(&self, offset: u32) -> &T {
        let ptr = self.offset_to_ptr(offset) as *const T;
        // SAFETY: Caller must ensure offset is within bounds when using
        unsafe { &*ptr }
    }

    /// Returns a mutable reference to a value of type `T` at the given offset.
    ///
    /// # Safety
    /// - Caller must ensure that `offset` is within bounds of the arena.
    #[inline]
    pub(crate) fn get_mut<T: Sized>(&self, offset: u32) -> &mut T {
        let ptr = self.offset_to_ptr(offset) as *mut T;
        // SAFETY: Caller must ensure offset is within bounds when using
        unsafe { &mut *ptr }
    }

    /// Returns a byte slice of length `len` at the given offset.
    ///
    /// # Safety
    /// - Caller must ensure that `offset + len` is within bounds of the arena.
    #[inline]
    pub(crate) fn get_slice(&self, offset: u32, len: u32) -> &[u8] {
        let ptr = self.offset_to_ptr(offset);
        // SAFETY: Caller must ensure offset is within bounds when using
        unsafe { std::slice::from_raw_parts(ptr, len as usize) }
    }

    /// Returns a mutable byte slice of length `len` at the given offset.
    ///
    /// # Safety
    /// - Caller must ensure that `offset + len` is within bounds of the arena.
    #[inline]
    pub(crate) fn get_slice_mut(&self, offset: u32, len: u32) -> &mut [u8] {
        let ptr = self.offset_to_ptr(offset);
        // SAFETY: Caller must ensure offset is within bounds when using
        unsafe { std::slice::from_raw_parts_mut(ptr, len as usize) }
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

    #[test]
    fn test_arena_get() {
        let arena = Arena::new(1024);
        let offset = arena.alloc(4, 4).unwrap();
        let ptr = arena.offset_to_ptr(offset) as *mut u32;
        // manually write to the allocated memory
        unsafe {
            *ptr = 123456;
        }
        // now read it back using get
        let value: &u32 = arena.get(offset);
        assert_eq!(*value, 123456);
    }

    #[test]
    fn test_arena_get_mut() {
        let arena = Arena::new(1024);
        let offset = arena.alloc(4, 4).unwrap();
        let value: &mut u32 = arena.get_mut(offset);
        for i in 0..=4000 {
            // write a different value each iteration
            let val = i * 4 + 1 - i / 3;
            *value = val;
            assert_eq!(*value, val);
        }
    }

    #[test]
    fn test_arena_get_slice() {
        let arena = Arena::new(1024);
        let offset = arena.alloc(10, 1).unwrap();
        let slice = arena.get_slice(offset, 10);
        assert_eq!(slice.len(), 10);
        for i in 0..10 {
            assert_eq!(slice[i], 0);
        }
        let slice_mut = arena.get_slice_mut(offset, 10);
        for i in 0..10 {
            slice_mut[i] = i as u8;
        }
        let slice = arena.get_slice(offset, 10);
        for i in 0..10 {
            assert_eq!(slice[i], i as u8);
        }
    }

    #[test]
    fn test_arena_ref_to_offset_and_back() {
        let arena = Arena::new(1024);
        let offset = arena.alloc(4, 4).unwrap();
        let value: &mut u32 = arena.get_mut(offset);
        *value = 987654;
        let offset2 = arena.ref_to_offset(value);
        assert_eq!(offset, offset2);
        let value2: &u32 = arena.offset_to_ref(offset2);
        assert_eq!(*value, *value2);
    }
}
