use super::Metadata;
use std::{
    alloc::{AllocError, Allocator, Layout, LayoutError, handle_alloc_error},
    mem::{MaybeUninit, needs_drop},
    ptr::{self, NonNull},
    sync::atomic::{self, Ordering},
};

#[repr(C)]
pub(crate) struct Allocation<T: ?Sized> {
    pub(crate) metadata: Metadata,
    pub(crate) data: T,
}

impl<T: ?Sized> Allocation<T> {
    /// Deallocates the memory pointed at by `non_null` in the provided allocator.
    ///
    /// # Safety
    ///
    /// See [`std::alloc::Allocator::deallocate`].
    pub(crate) unsafe fn deallocate_in<A: Allocator>(non_null: NonNull<Self>, allocator: &A) {
        // SAFETY: User-upheld invariants.
        unsafe {
            let layout = Layout::for_value(&*non_null.as_ptr());
            (&raw mut (*non_null.as_ptr()).metadata).drop_in_place();
            if needs_drop::<T>() {
                (&raw mut (*non_null.as_ptr()).data).drop_in_place();
            }
            allocator.deallocate(non_null.cast(), layout);
        }
    }

    /// Decrements the reference counter and deallolcates the pointee if the counter becomes nil
    /// without checking whether the counter is non-zero before the decrement.
    ///
    /// # Safety
    ///
    /// See [`LockState::fetch_decrement_counter_unchecked`] and [`Allocation::deallocate_in`].
    pub(crate) unsafe fn drop_in_unchecked<A: Allocator>(non_null: NonNull<Self>, allocator: &A) {
        // SAFETY: User-upheld invariants.
        if unsafe {
            Allocation::get_metadata_disjoint(non_null)
                .state
                .fetch_decrement_counter_unchecked(Ordering::Release)
        } == 1
        {
            atomic::fence(Ordering::Acquire);
            // SAFETY: User-upheld invariants.
            unsafe {
                Allocation::deallocate_in(non_null, allocator);
            }
        }
    }

    /// Returns whether there exists only a single guard to the allocation.
    ///
    /// # Safety
    ///
    /// `non_null` must point to a valid instance of `Allocation<T>`
    #[inline]
    pub(crate) unsafe fn is_exclusive(non_null: NonNull<Self>) -> bool {
        // SAFETY: User-upheld invariant.
        1 == unsafe { Self::get_metadata_disjoint(non_null).state.get_counter() }
    }

    /// Returns a pointer to the data part of the allocation pointed at by `non_null`.
    ///
    /// # Safety
    ///
    /// `non_null` must point to a valid and live instance of `Allocation<T>`.
    #[inline]
    pub(crate) unsafe fn get_data_non_null(non_null: NonNull<Self>) -> NonNull<T> {
        // SAFETY: A raw pointer to a field is never null.
        unsafe {
            NonNull::new_unchecked(
                // SAFETY: User-upheld invariant.
                &raw mut (*non_null.as_ptr()).data,
            )
        }
    }

    /// Returns a reference to the metadata of the `Allocation` referenced by `non_null`
    /// without constructing a reference to the whole object.
    ///
    /// # Safety
    ///
    /// `non_null` must point to a valid instance of `Allocation<T>` that outlives `'a`.
    #[inline]
    pub(crate) const unsafe fn get_metadata_disjoint<'a>(non_null: NonNull<Self>) -> &'a Metadata {
        unsafe { &(*non_null.as_ptr()).metadata }
    }

    /// Returns a reference to the data part of the allocation pointed at by `non_null`
    /// without constructing a (mutable) reference to the whole object.
    ///
    /// # Safety
    ///
    /// - `non_null` must point to a valid instance of `Allocation<T>` that outlives `'a`.
    /// - The returned reference must not violate aliasing rules.
    #[inline]
    pub(crate) const unsafe fn get_data_ref_disjoint<'a>(non_null: NonNull<Self>) -> &'a T {
        // SAFETY: User-upheld invariants.
        unsafe { &(*non_null.as_ptr()).data }
    }

    /// Returns a mutable reference to the data part of the allocation pointed at by `non_null`
    /// without constructing a (mutable) reference to the whole object.
    ///
    /// # Safety
    ///
    /// - `non_null` must point to a valid instance of `Allocation<T>` that outlives `'a`.
    /// - The returned reference must not violate aliasing rules.
    #[inline]
    pub(crate) const unsafe fn get_data_mut_disjoint<'a>(non_null: NonNull<Self>) -> &'a mut T {
        // SAFETY: User-upheld invariants.
        unsafe { &mut (*non_null.as_ptr()).data }
    }
}

impl<T> Allocation<[T]> {
    /// Returns the layout that describes an `Allocation<[T]>`.
    #[inline]
    fn get_layout(len: usize) -> Result<Layout, LayoutError> {
        Layout::new::<Metadata>()
            .pad_to_align()
            .extend(Layout::array::<T>(len)?)
            .map(|(layout, _)| layout)
    }

    /// Returns the length of the underlying slice pointed at by `non_null`.
    pub(crate) const fn len(non_null: NonNull<Self>) -> usize {
        non_null.to_raw_parts().1
    }

    /// Returns a reference to a subslice of the underlying slice pointed at by `non_null`
    /// without constructing a (mutable) reference to the whole object.
    ///
    /// # Safety
    ///
    /// - `non_null` must point to a valid instance of `Allocation<[T]>` that outlives `'a`.
    /// - The returned reference must not violate aliasing rules.
    #[inline]
    pub(crate) const unsafe fn get_subslice_disjoint<'a>(non_null: NonNull<Self>, start: usize, len: usize) -> &'a [T] {
        // SAFETY: User-upheld invariants.
        unsafe { &*ptr::from_raw_parts((&raw const (*non_null.as_ptr()).data).cast::<T>().add(start), len) }
    }

    /// Returns a mutable reference to a subslice of the underlying slice pointed at by `non_null`
    /// without constructing a (mutable) reference to the whole object.
    ///
    /// # Safety
    ///
    /// - `non_null` must point to a valid instance of `Allocation<T>` that outlives `'a`.
    /// - The returned reference must not violate aliasing rules.
    #[inline]
    pub(crate) const unsafe fn get_subslice_mut_disjoint<'a>(non_null: NonNull<Self>, start: usize, len: usize) -> &'a mut [T] {
        // SAFETY: User-upheld invariants.
        unsafe { &mut *ptr::from_raw_parts_mut((&raw mut (*non_null.as_ptr()).data).cast::<T>().add(start), len) }
    }

    /// Returns a reference to a constant-sized subslice of the underlying slice pointed at by `non_null`
    /// without constructing a (mutable) reference to the whole object.
    ///
    /// # Safety
    ///
    /// - `non_null` must point to a valid instance of `Allocation<[T]>` that outlives `'a`.
    /// - The returned reference must not violate aliasing rules.
    #[inline]
    pub(crate) const unsafe fn get_array_disjoint<'a, const N: usize>(non_null: NonNull<Self>, start: usize) -> &'a [T; N] {
        // SAFETY: User-upheld invariants.
        unsafe { &*(&raw const (*non_null.as_ptr()).data).cast::<T>().add(start).cast() }
    }

    /// Returns a mutable reference to a constant-sized subslice of the underlying slice pointed at by `non_null`
    /// without constructing a (mutable) reference to the whole object.
    ///
    /// # Safety
    ///
    /// - `non_null` must point to a valid instance of `Allocation<[T]>` that outlives `'a`.
    /// - The returned reference must not violate aliasing rules.
    #[inline]
    pub(crate) const unsafe fn get_array_mut_disjoint<'a, const N: usize>(non_null: NonNull<Self>, start: usize) -> &'a mut [T; N] {
        // SAFETY: User-upheld invariants.
        unsafe { &mut *(&raw mut (*non_null.as_ptr()).data).cast::<T>().add(start).cast() }
    }

    /// Returns a reference to an element of the underlying slice pointed at by `non_null`
    /// without constructing a (mutable) reference to the whole object.
    ///
    /// # Safety
    ///
    /// - `non_null` must point to a valid instance of `Allocation<[T]>` that outlives `'a`.
    /// - The returned reference must not violate aliasing rules.
    #[inline]
    pub(crate) const unsafe fn get_element_disjoint<'a>(non_null: NonNull<Self>, idx: usize) -> &'a T {
        // SAFETY: User-upheld invariants.
        unsafe { &*(&raw const (*non_null.as_ptr()).data).cast::<T>().add(idx) }
    }

    /// Returns a mutable reference to an element of the underlying slice pointed at by `non_null`
    /// without constructing a (mutable) reference to the whole object.
    ///
    /// # Safety
    ///
    /// - `non_null` must point to a valid instance of `Allocation<[T]>` that outlives `'a`.
    /// - The returned reference must not violate aliasing rules.
    #[inline]
    pub(crate) const unsafe fn get_element_mut_disjoint<'a>(non_null: NonNull<Self>, idx: usize) -> &'a mut T {
        // SAFETY: User-upheld invariants.
        unsafe { &mut *(&raw mut (*non_null.as_ptr()).data).cast::<T>().add(idx) }
    }
}

impl<T> Allocation<[MaybeUninit<T>]> {
    /// Allocates an instance of an `Allocation` with uninitialized contents in the provided allocator.
    pub(crate) fn allocate_uninit_in<A: Allocator>(len: usize, allocator: &A) -> NonNull<Self> {
        let layout = Self::get_layout(len).unwrap();
        let non_null = NonNull::<Self>::from_raw_parts(allocator.allocate(layout).unwrap_or_else(|_| handle_alloc_error(layout)).cast::<()>(), len);
        // SAFETY: `non_null` points to a valid allocation and has exclusive access to it.
        unsafe {
            (&raw mut (*non_null.as_ptr()).metadata).write(Metadata::new());
        }
        non_null
    }

    /// Allocates an instance of an `Allocation` with uninitialized contents in the provided allocator,
    /// returning an error if the allocation fails.
    pub(crate) fn try_allocate_uninit_in<A: Allocator>(len: usize, allocator: &A) -> Result<NonNull<Self>, AllocError> {
        let layout = match Self::get_layout(len) {
            Ok(layout) => layout,
            Err(_) => return Err(AllocError),
        };
        let non_null = NonNull::<Self>::from_raw_parts(allocator.allocate(layout)?.cast::<()>(), len);
        // SAFETY: `non_null` points to a valid allocation and has exclusive access to it.
        unsafe {
            (&raw mut (*non_null.as_ptr()).metadata).write(Metadata::new());
        }
        Ok(non_null)
    }

    /// Allocates an instance of an `Allocation` with uninitialized contents,
    /// with the `slice` field being filled with `0` bytes in the provided allocator.
    pub(crate) fn allocate_zeroed_in<A: Allocator>(len: usize, allocator: &A) -> NonNull<Self> {
        let layout = Self::get_layout(len).unwrap();
        let non_null = NonNull::<Self>::from_raw_parts(
            allocator.allocate_zeroed(layout).unwrap_or_else(|_| handle_alloc_error(layout)).cast::<()>(),
            len,
        );
        // SAFETY: `non_null` points to a valid allocation and has exclusive access to it.
        unsafe {
            (&raw mut (*non_null.as_ptr()).metadata).write(Metadata::new());
        }
        non_null
    }

    /// Allocates an instance of an `Allocation` with uninitialized contents,
    /// with the `slice` field being filled with `0` bytes in the provided allocator,
    /// returning an error if allocation fails.
    pub(crate) fn try_allocate_zeroed_in<A: Allocator>(len: usize, allocator: &A) -> Result<NonNull<Self>, AllocError> {
        let layout = match Self::get_layout(len) {
            Ok(layout) => layout,
            Err(_) => return Err(AllocError),
        };
        let non_null = NonNull::<Self>::from_raw_parts(allocator.allocate_zeroed(layout)?.cast::<()>(), len);
        // SAFETY: `non_null` points to a valid allocation and has exclusive access to it.
        unsafe {
            (&raw mut (*non_null.as_ptr()).metadata).write(Metadata::new());
        }
        Ok(non_null)
    }
}
