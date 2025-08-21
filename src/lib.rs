#![feature(ptr_metadata, allocator_api)]
#![allow(dead_code)]

mod inner;

mod elem;

mod elem_rw_lock;

#[rustfmt::skip]
pub use crate::elem::{
    lock::ElemRwLock, 
    write::ElemRwLockWriteGuard,
    read_all::ElemRwLockReadAllGuard,
    write_all::ElemRwLockWriteAllGuard,
};

#[cfg(feature = "mapped_guards")]
pub use crate::elem::write::mapped::MappedElemRwLockWriteGuard;

#[cfg(test)]
mod tests {}
