.PHONY: all
all: build

.PHONY: build
build: format
	CARGO_PROFILE_RELEASE_DEBUG=true cargo build --release

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

.PHONY: clean-generated
clean-generated:
	rm -f tests/**/*.llbc

.PHONY: clean
clean: clean-generated
	rm -rf target
