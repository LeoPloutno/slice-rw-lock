#![feature(ptr_metadata, vec_into_raw_parts)]
//#![allow(dead_code)]

#[cold]
#[inline(always)]
fn unlikely(val: bool) -> bool {
    val
}

mod inner;

mod elem_rw_lock;
mod chunk_rw_lock;

#[rustfmt::skip]
pub use crate::elem_rw_lock::{
    iter::Iter as Iter, 
    lock::RwLock as ElemRwLock, 
    read_slice::RwLockReadSliceGuard as ElemRwLockReadSliceGuard, 
    write::RwLockWriteGuard as ElemRwLockWriteGuard,
    write_slice::RwLockWriteSliceGuard as ElemRwLockWriteSliceGuard,
};

#[cfg(test)]
mod tests {}
