//@ revisions=values,bytes
//@[values] charon-args=--consts=values
//@[bytes] charon-args=--consts=bytes
//@ charon-args=--raw-consts
const REF: &u32 = &42;
static ARR: [u32; 3] = [10, 20, 30];
const ARR_START: *const u32 = unsafe { (&raw const ARR).cast::<u32>() };
const ARR_INDICES: [*const u32; 4] = const {
    unsafe {
        [
            ARR_START.add(0),
            ARR_START.add(1),
            ARR_START.add(2),
            ARR_START.add(3),
        ]
    }
};
