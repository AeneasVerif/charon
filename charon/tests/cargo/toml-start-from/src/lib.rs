// fn_a should appear in the charon output (it is in the start_from module).
// fn_b should not appear (its module is not reachable from the entry point).
pub mod included {
    pub fn fn_a() -> u32 {
        1
    }
}

pub mod excluded {
    pub fn fn_b() -> u32 {
        2
    }
}
