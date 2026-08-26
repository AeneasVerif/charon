//! Regression test: `Span`s nested inside `AttributeKind` must be remapped when
//! merging targets, and ignored when deduplicating items across targets.
//!
//! `AttributeKind` used to be declared `skip_but_eq` in the visitor group, i.e.
//! opaque to normal visitors and compared with `PartialEq` by `ZipAst`. It is
//! not a leaf though: `Inline(_, Span)`, `TrackCaller(Span)`, `TargetFeature {
//! attr_span, .. }` and others embed a `Span`, and hence a `FileId`. So (a)
//! `CrateMerger`'s `RemapIdsVisitor` could not descend into it and left those
//! `FileId`s pointing at whatever file happened to hold that id in the
//! per-target crate, and (b) `ItemComparer` compared the spans it contains
//! instead of ignoring them via `visit_span`.
//!
//! Together those made every item carrying a builtin attribute (`#[inline]`,
//! `#[track_caller]`, ...) compare unequal across targets as soon as the targets
//! registered their files in a different order, so target-independent functions
//! were needlessly given a per-target copy and a dispatcher.
//!
//! Two files are required: the attributed item's `FileId` has to differ between
//! targets, and a single-file crate registers its only file first, so that id is
//! stable. `only_on_x86` below exists on one target only and is registered
//! before `common`, which is what shifts the `FileId` of `common.rs`. The
//! functions in `common` must nevertheless be deduplicated into single items
//! with no target suffix and no dispatcher.
#![no_std]

#[cfg(target_arch = "x86_64")]
pub fn only_on_x86(x: u32) -> u32 {
    x.wrapping_add(1)
}

pub mod common;
