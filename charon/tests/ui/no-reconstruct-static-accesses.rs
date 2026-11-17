//@ charon-args=--no-reconstruct-static-accesses
#![feature(thread_local)]

static SHARED: u32 = 0;
static mut MUT: u32 = 0;
#[thread_local]
static THREAD_LOCAL: u32 = 0;

fn read_shared() -> u32 {
    SHARED
}

fn ref_shared() -> &'static u32 {
    &SHARED
}

fn read_mut() -> u32 {
    unsafe { MUT }
}

fn write_mut() {
    unsafe { MUT = 1 }
}

fn read_thread_local() -> u32 {
    THREAD_LOCAL
}

fn raw_mut() -> *const u32 {
    &raw const MUT
}
