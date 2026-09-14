fn consume(_: String) {}

pub fn handle_request(input: String) {
    let _background_job = std::thread::spawn(move || {
        consume(input);
    });
}
