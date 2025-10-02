#![feature(ptr_metadata, allocator_api)]
#![allow(dead_code)]

mod array;
mod elem;
mod inner;
mod slice;

#[rustfmt::skip]
pub use crate::{
    elem::{
        lock::ElemRwLock, 
        read_all::ElemRwLockReadAllGuard,
        write::ElemRwLockWriteGuard,
        write_all::ElemRwLockWriteAllGuard,
    },
    array::{
        lock::ArrayRwLock,
        read_all::ArrayRwLockReadAllGuard,
        write::ArrayRwLockWriteGuard,
        write_all::ArrayRwLockWriteAllGuard
    }
};

#[cfg(feature = "mapped_guards")]
#[rustfmt::skip]
pub use crate::{
    elem::{
        read_all::mapped::MappedElemRwLockReadAllGuard, 
        write::mapped::MappedElemRwLockWriteGuard,
        write_all::mapped::MappedElemRwLockWriteAllGuard,
    },
    array::{
        read_all::mapped::MappedArrayRwLockReadAllGuard,
        write::mapped::MappedArrayRwLockWriteGuard,
        write_all::mapped::MappedArrayRwLockWriteAllGuard
    }
};

#[cfg(test)]
mod tests {}
