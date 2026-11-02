//@ revisions=ullbc,llbc,forward-break
//@[ullbc] charon-args=--ullbc --print-ullbc
//@[forward-break] charon-args=--no-code-duplication

pub struct Ticket(pub u8);

impl Drop for Ticket {
    fn drop(&mut self) {}
}

fn adds_an_unwind_edge() {}

pub fn cleanup_dag(fail: bool, tag: u8) -> u8 {
    let _a = Ticket(tag);
    let _b = Ticket(tag);
    let _c = Ticket(tag);
    let _d = Ticket(tag);
    adds_an_unwind_edge();
    adds_an_unwind_edge();
    adds_an_unwind_edge();
    adds_an_unwind_edge();
    7
}
