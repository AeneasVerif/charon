use dependency::Record;

pub fn read_visible(value: u32) -> u32 {
    Record::new(value).visible
}
