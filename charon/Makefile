.PHONY: all
all: build test

.PHONY: build
build:
	cargo build

.PHONY: test
test:
	cargo run tests/src/nested_borrows.rs --dest tests/cfim
	cargo run tests/src/no_nested_borrows.rs --dest tests/cfim
	cargo run tests/src/loops.rs --dest tests/cfim
