//! This crate exapnds upon the `RwLock` primitive from Rust's standard library.
//!
//! [`RwLock`] is a synchronization primitive which allows one to access shared data in to modes: mutably (single writer) and immutably (multiple readers).
//! It does so by separating write and read operations in time via synchronization - if a thread asks for an access mode that cannot, at this moment, be granted,
//! it will be blocked until the aliasing rules may be satisfied.
//!
//! This approach, however, disregards 'spacial' separation of access - that is, if multiple threads share data and only
//! access non-ooverlapping regions of said data, they cannot do so using an `RwLock`, for it protects the whole entity and does not
//! care about its internals.
//!
//! The locks in this crate allow one to concurrently share disjoint regions of memory associated with a slice
//! and mutate the fragments in parallel while upholding Rust's ownership rules.
//!
//! The allowed access modes are:
//! * Shared global access - read only access to the whole slice.
//! * Exclusive access - read and write access to a specific subslice or element of the slice.
//! * Exclusive global access - read and write access to the whole slice.
//! At any moment any number of locks may hold shared global access or exclusive access, but not both at the same time.
//! If there exists a lock holding exclusive global access, no other lock may access the slice in any way.
//! Similarly, as long as the slice is accessed by another lock in any way, there can be no locks possesing exclusive global access.
//!
//! These rules ensure no two locks will write to data that is being read at the same time.

#![cfg_attr(feature = "strip_trim_prefix_suffix", feature(slice_pattern))]
#![cfg_attr(test, feature(assert_matches), feature(integer_atomics))]
#![feature(ptr_metadata, allocator_api, one_sided_range, unsize, coerce_unsized)]
#![allow(dead_code)]

mod array;
mod core;
mod element;
mod slice;
mod whole;

#[rustfmt::skip]
pub use crate::{
    element::{
        lock::ElementRwLock,
        read_all::ElementRwlockReadAllGuard,
        write::ElementRwlockWriteGuard,
        write_all::ElementRwlockWriteAllGuard,
    },
    array::{
        lock::ArrayRwLock,
        read_all::ArrayRwLockReadAllGuard,
        write::ArrayRwLockWriteGuard,
        write_all::ArrayRwLockWriteAllGuard
    },
    slice::{
        lock::SliceRwLock,
        read_all::SliceRwLockReadAllGuard,
        write::SliceRwLockWriteGuard,
        write_all::SliceRwLockWriteAllGuard,
        iter::Iter,
        array_chunks::ArrayChunks,
        chunks::Chunks,
        chunks_exact::ChunksExact,
        rarray_chunks::RArrayChunks,
        rchunks::RChunks,
        rchunks_exact::RChunksExact,
        chunk_by::ChunkBy,
        split::Split,
        split_inclusive::SplitInclusive,
        rsplit::RSplit,
        splitn::SplitN,
        rsplitn::RSplitN,
    }
};

#[cfg(feature = "mapped_guards")]
#[rustfmt::skip]
pub use crate::{
    element::{
        read_all::mapped::MappedElementRwlockReadAllGuard,
        write::mapped::MappedElementRwlockWriteGuard,
        write_all::mapped::MappedElementRwlockWriteAllGuard,
    },
    array::{
        read_all::mapped::MappedArrayRwLockReadAllGuard,
        write::mapped::MappedArrayRwLockWriteGuard,
        write_all::mapped::MappedArrayRwLockWriteAllGuard
    },
    slice::{
        read_all::mapped::MappedSliceRwLockReadAllGuard,
        write::mapped::MappedSliceRwLockWriteGuard,
        write_all::mapped::MappedSliceRwLockWriteAllGuard
    }
};

#[cfg(test)]
mod tests {}
