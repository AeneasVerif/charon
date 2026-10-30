//@ charon-args=--consts=values --raw-consts

const REPEATED: [u32; 4] = [7, 7, 7, 7];
const DISTINCT: [u32; 4] = [7, 7, 8, 7];
const EMPTY: [u32; 0] = [];
const SINGLE: [u32; 1] = [7];
const NESTED: [[u32; 2]; 3] = [[7, 7], [7, 7], [7, 7]];

struct NonCopy(u32);
const NON_COPY: [NonCopy; 2] = [NonCopy(7), NonCopy(7)];
