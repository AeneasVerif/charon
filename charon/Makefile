.PHONY: all
all: build

.PHONY: build
build: format
	cargo build --release

.PHONY: format
format:
	cargo fmt

.PHONY: test
test:
	cargo test

# Build the doc.
# For some reason, I don't manage to build all the packages in one command.
.PHONY: doc
doc:
	cargo doc --no-deps -p macros --document-private-items
	cargo doc --no-deps --document-private-items

.PHONY: clean
clean:
	rm -rf target
	rm -f tests/**/*.llbc
