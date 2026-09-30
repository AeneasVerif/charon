//@ rustc-args=--target x86_64-unknown-linux-gnu
#![feature(effective_target_features)]

#[unsafe(export_name = "exported")]
fn export_name() {}

#[unsafe(link_section = "__TEXT,__custom")]
fn link_section() {}

#[target_feature(enable = "avx")]
fn target_feature() {}

#[unsafe(force_target_feature(enable = "avx"))]
fn force_target_feature() {}
