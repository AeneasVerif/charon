.PHONY: all
all: build test

.PHONY: build
build:
	cargo build

.PHONY: test
test:
	cargo run examples/nested_borrows.rs --dest examples/cfim
	cargo run examples/no_nested_borrows.rs --dest examples/cfim
	cargo run examples/loops.rs --dest examples/cfim
