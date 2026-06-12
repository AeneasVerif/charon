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
	$(MAKE) test
	$(MAKE) clippy

.PHONY: test-noclippy
test-noclippy:
	cargo test

.PHONY: clippy
clippy:
	cargo clippy --all-targets --fix --allow-dirty

.PHONY: generate-asts
generate-asts:
	cargo build --bins
	cargo run --bin generate-asts
	cargo fmt

.PHONY: generate-asts-keep-llbc
generate-asts-keep-llbc:
	CHARON_GENERATE_REUSE_LLBC=1 $(MAKE) generate-asts

.PHONY: test-popular-crates
test-popular-crates:
	cargo test --release --features popular-crates-test --test popular-crates -- --test-threads 8

# Build the doc.
# For some reason, I don't manage to build all the packages in one command.
.PHONY: doc
doc:
	cargo doc --no-deps -p macros --document-private-items
	cargo doc --no-deps --document-private-items

.PHONY: clean-generated
clean-generated:
	find tests -name '*.llbc' -delete
	find tests -name '*.ullbc' -delete
	find tests -name '*.postcard' -delete

.PHONY: clean
clean: clean-generated
	rm -rf target
