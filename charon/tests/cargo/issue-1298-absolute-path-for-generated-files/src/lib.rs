pub mod generated {
    include!(concat!(env!("OUT_DIR"), "/generated.rs"));
}

pub fn get_value(g: &generated::Generated) -> u32 {
    g.value
}
