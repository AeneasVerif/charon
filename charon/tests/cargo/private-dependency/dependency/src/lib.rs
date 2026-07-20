pub struct Record {
    pub visible: u32,
    hidden: u32,
}

fn increment(value: u32) -> u32 {
    value + 1
}

impl Record {
    pub fn new(value: u32) -> Self {
        Self {
            visible: value,
            hidden: increment(value),
        }
    }

    pub fn hidden(&self) -> u32 {
        self.hidden
    }
}
