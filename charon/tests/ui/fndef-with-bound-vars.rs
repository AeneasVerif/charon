fn bar<T>() {}

fn main() {
    let _ = || {
        let i = bar::<&()>;
        move || i
    };
}
