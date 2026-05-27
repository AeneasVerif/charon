struct NoCopy(u8);

fn move_values(flag: bool) {
    let x = NoCopy(4);
    let _v = vec![x];
    if flag {
        let y = NoCopy(5);
        let _w = vec![y];
    }
}
