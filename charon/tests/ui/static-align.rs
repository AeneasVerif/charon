//@ charon-args=--print-layouts
//! `#[rustc_align_static]` raises the alignment of a static above that of its type.
#![feature(static_align)]

#[rustc_align_static(64)]
pub static OVER_ALIGNED: u8 = 0;

// The attribute can't lower the alignment below that of the type.
#[rustc_align_static(1)]
pub static UNDER_ALIGNED: u64 = 0;

pub static NOT_ALIGNED: u8 = 0;
