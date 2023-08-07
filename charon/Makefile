.PHONY: all
all: build

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
	cargo doc --no-deps -p macros --document-private-items
	cargo doc --no-deps --document-private-items
