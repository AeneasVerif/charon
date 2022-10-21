.PHONY: all
all: build test doc

.PHONY: build
build:
	cargo build

.PHONY: test
test:
	cargo test

# Build the doc.
# For some reason, I don't manage to build all the packages in one command.
.PHONY: doc
doc:
	cargo doc --no-deps -p macros
	cargo doc --no-deps
