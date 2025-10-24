//! A specifically fit implementation of a bump pointer arena allocator.
//! It has incredibly fast allocation times, as it only requires moving a
//! pointer forward by the size of the allocated object.
//! In concurrency scenarios like here, it can be made lock-free by using atomic
//! operations to move the pointer forward, specifically atomic load and
//! compare-and-swap (CAS) operation.
//!
//! The main disadvantage of this allocator type is that it does not support
//! deallocation of individual objects. Instead, the entire arena can be
//! deallocated at once, by using the [`Arena::reset`] method.
//!
//! For the skiplist implementation, this is not a problem, as the skiplist
//! has the property of being append only. Thus, nodes are only added to the
//! skiplist, and never removed. When the skiplist is no longer needed, the
//! entire arena can be reset, freeing all memory used by the skiplist.
//! After being reset, the arena may be reused for allocating new objects.
//!
//! This allows for implementing an arena-pool, that allows reusing old arenas
//! for new skiplists, reducing the number of allocations needed dramatically.
//!
//! # Safety
//!
//! The whole public API of this module is marked as unsafe, as the user must uphold
//! a number of invariants to ensure memory safety.
//! Specifics about these invariants are documented in the respective method doc comments.

use std::{
    cell::UnsafeCell,
    sync::atomic::{AtomicU32, Ordering},
};

pub(crate) struct Arena {
    buffer: UnsafeCell<Box<[u8]>>,
    position: AtomicU32,
    capacity: u32,
}

impl Arena {
    /// The maximum capacity of the arena in bytes.
    /// Equal to `min(u32::MAX, isize::MAX)`.
    ///
    /// This limit is due to the fact that LLVM uses signed integers for pointer
    /// arithmetic, so we cannot allocate more than `isize::MAX` bytes.
    /// This results in a maximum capacity of `2_147_483_647` (2^31 - 1) bytes on
    /// 32-bit systems, and `4_294_967_295` (2^32 - 1) bytes on 64-bit systems.
    pub(crate) const MAX_CAPACITY: u32 = {
        let u32_max = u32::MAX as usize;
        let isize_max = isize::MAX as usize;
        if u32_max > isize_max {
            isize_max as u32
        } else {
            u32::MAX
        }
    };

    /// Creates a new arena with the specified capacity in bytes.
    ///
    /// # Arguments
    /// - `capacity`: The total capacity of the arena in bytes.
    ///   Must not exceed [`Arena::MAX_CAPACITY`]. For best performance,
    ///   it is recommended to align the capacity to a power of two.
    ///
    /// # Safety
    /// - The caller must ensure that `capacity` does not exceed [`Arena::MAX_CAPACITY`].
    /// - The caller must always uphold the safety invariants of the public API, else
    ///   memory safety may be violated and undefined behavior may occur.
    pub(crate) unsafe fn new(capacity: u32) -> Self {
        debug_assert!(
            capacity <= Self::MAX_CAPACITY,
            "capacity must not exceed MAX_CAPACITY ({} bytes)",
            Self::MAX_CAPACITY
        );

        let buffer = vec![0u8; capacity as usize].into_boxed_slice();
        Self {
            buffer: UnsafeCell::new(buffer),
            position: AtomicU32::new(0),
            capacity,
        }
    }

    /// Allocates a block of memory of `size` bytes with the specified `align` alignment.
    /// Returns the offset of the allocated block within the arena's buffer on success,
    /// or `None` if there is not enough space left in the arena.
    ///
    /// # Arguments
    /// - `size`: The size of the block to allocate, in bytes. Must be greater than zero.
    /// - `align`: The alignment of the block to allocate in memory, in bytes. Must be a power of two.
    ///
    /// # Returns
    /// - `Some(offset)`: The offset of the allocated block within the arena's buffer.
    /// - `None`: If there is not enough space left in the arena to satisfy the allocation request.
    ///
    /// `offset` can be used with the [`Arena::get_ptr`] and [`Arena::get_mut_ptr`] methods to
    /// obtain pointers to the allocated memory.
    ///
    /// NB: The `offset` may not be aligned to `align` itself, but the pointer obtained
    /// from `get_ptr` or `get_mut_ptr` using the `offset` will be properly aligned.
    ///
    /// # Safety
    /// - `align` must be a power of two.
    /// - `size` must be greater than zero.
    pub(crate) unsafe fn allocate(&self, size: u32, align: u32) -> Option<u32> {
        debug_assert!(align.is_power_of_two(), "align must be a power of two");
        debug_assert!(size > 0, "size must be greater than zero");

        // SAFETY: We allocated the buffer in `new` with the specified capacity.
        // Dereferencing the pointer is safe, since Box<T> always points to valid memory.
        let base_ptr = unsafe { (*self.buffer.get()).as_ptr() };

        loop {
            let current_pos = self.position.load(Ordering::Relaxed);
            let current_ptr = unsafe { base_ptr.add(current_pos as usize) };

            let misalignment = current_ptr.align_offset(align as usize);
            if misalignment == usize::MAX {
                // Alignment not possible, e.g., due to insufficient space.
                return None;
            }

            let aligned_pos = current_pos.checked_add(misalignment as u32)?;

            let new_pos = aligned_pos.checked_add(size)?;

            if new_pos > self.capacity {
                return None;
            }

            if self
                .position
                .compare_exchange(current_pos, new_pos, Ordering::SeqCst, Ordering::Relaxed)
                .is_ok()
            {
                return Some(aligned_pos);
            }
        }
    }

    /// Resets the arena, making all previously allocated memory available for reuse.
    /// This does not deallocate any memory, but simply sets the allocation pointer
    /// back to the beginning of the buffer.
    ///
    /// # Safety
    /// The caller must ensure that no references to previously allocated memory
    /// are used after this call, as they may now point to invalid or reused memory.
    pub(crate) unsafe fn reset(&self) {
        self.position.store(0, Ordering::SeqCst);
    }

    /// Returns the total capacity of the arena in bytes.
    #[inline(always)]
    pub(crate) const fn capacity(&self) -> u32 {
        self.capacity
    }

    /// Returns a constant pointer to the memory at the given offset within the arena's buffer.
    ///
    /// # Arguments
    /// - `offset`: The offset within the arena's buffer to get the pointer to.
    ///
    /// # Safety
    /// - `offset` must be less than the arena's capacity.
    /// - The caller must ensure that the returned pointer is used safely,
    ///   respecting Rust's aliasing rules.
    /// - The `*const u8` pointer must not be used after the arena has been reset.
    /// - The caller must ensure that no mutable references to the same memory exist.
    #[inline(always)]
    pub(super) unsafe fn get_ptr(&self, offset: u32) -> *const u8 {
        debug_assert!(offset < self.capacity, "offset must be less than capacity");

        // SAFETY: We allocated the buffer in `new` with the specified capacity.
        // Dereferencing the pointer is safe, since Box<T> always points to valid memory.
        let buf_ptr = unsafe { (*self.buffer.get()).as_ptr() };
        // SAFETY: The caller must ensure that `offset` is within bounds.
        unsafe { buf_ptr.add(offset as usize) }
    }

    /// Returns a mutable pointer to the memory at the given offset within the arena's buffer.
    ///
    /// # Arguments
    /// - `offset`: The offset within the arena's buffer to get the pointer to.
    ///
    /// # Safety
    /// - `offset` must be less than the arena's capacity.
    /// - The caller must ensure that the returned pointer is used safely,
    ///   respecting Rust's aliasing and mutability rules.
    /// - The `*mut u8` pointer must not be used after the arena has been reset.
    /// - The caller must ensure that no other mutable references to the same memory exist.
    #[inline(always)]
    pub(super) unsafe fn get_mut_ptr(&self, offset: u32) -> *mut u8 {
        debug_assert!(offset < self.capacity, "offset must be less than capacity");

        // SAFETY: We allocated the buffer in `new` with the specified capacity.
        // Dereferencing the pointer is safe, since Box<T> always points to valid memory.
        let buf_ptr = unsafe { (*self.buffer.get()).as_ptr() };
        // SAFETY: The caller must ensure that `offset` is within bounds,
        // and that no other mutable references to the same memory exist.
        unsafe { buf_ptr.add(offset as usize).cast_mut() }
    }
}

// SAFETY: Arena can be safely sent between threads, as long as the user
// upholds the safety invariants of the public API.
unsafe impl Send for Arena {}
// SAFETY: Arena can be safely shared between threads, as long as the user upholds
// the safety invariants of the public API.
unsafe impl Sync for Arena {}

#[cfg(test)]
mod tests {
    use super::Arena;

    #[test]
    fn test_arena_allocation() {
        unsafe {
            let arena = Arena::new(1024);

            let offset1 = arena.allocate(16, 8).expect("Allocation 1 failed");
            let ptr1 = arena.get_ptr(offset1);
            assert!(!ptr1.is_null());
            assert_eq!(ptr1.align_offset(8), 0);

            let offset2 = arena.allocate(32, 16).expect("Allocation 2 failed");
            let ptr2 = arena.get_mut_ptr(offset2);
            assert!(!ptr2.is_null());
            assert_eq!(ptr2.align_offset(16), 0);

            let offset3 = arena.allocate(64, 32).expect("Allocation 3 failed");
            let ptr3 = arena.get_ptr(offset3);
            assert!(!ptr3.is_null());
            assert_eq!(ptr3.align_offset(32), 0);

            let offset4 = arena.allocate(8, 8).expect("Allocation 4 failed");
            let ptr4 = arena.get_mut_ptr(offset4);
            assert!(!ptr4.is_null());
            assert_eq!(ptr4.align_offset(8), 0);

            let offset5 = arena.allocate(128, 64).expect("Allocation 5 failed");
            let ptr5 = arena.get_ptr(offset5);
            assert!(!ptr5.is_null());
            assert_eq!(ptr5.align_offset(64), 0);

            assert!(
                arena.allocate(1024, 8).is_none(),
                "Allocation should have failed, not enough space"
            );

            arena.reset();

            let offset6 = arena
                .allocate(128, 64)
                .expect("Allocation after reset failed");
            let ptr6 = arena.get_ptr(offset6);
            assert!(!ptr6.is_null());
            assert_eq!(ptr6.align_offset(64), 0);
        }
    }
}
