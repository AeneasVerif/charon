CURRENT_DIR = $(shell pwd)
CHARON ?= $(CURRENT_DIR)/../charon/target/debug/cargo-charon
DEST ?= .
OPTIONS =
CHARON_CMD :=

.PHONY: all
all: build tests

.PHONY: build
build:
	cargo build

.PHONY: tests
tests: cargo-tests charon-tests

.PHONY: cargo-tests
cargo-tests: build
	cargo test

.PHONY: charon-tests
charon-tests: \
	test-nested_borrows test-no_nested_borrows test-loops test-hashmap \
	test-paper test-hashmap_main \
	test-matches test-matches_duplicate test-external \
	test-constants

test-nested_borrows: OPTIONS += --no-code-duplication
test-no_nested_borrows: OPTIONS += --no-code-duplication
test-loops: OPTIONS += --no-code-duplication
# test-hashmap: OPTIONS += --no-code-duplication
# test-hashmap_main: OPTIONS += --no-code-duplication
test-hashmap_main: OPTIONS += --opaque=hashmap_utils
test-paper: OPTIONS += --no-code-duplication
test-constants: OPTIONS += --no-code-duplication
# Possible to add `OPTIONS += --no-code-duplication` if we use the optimized MIR
test-matches:
test-external: OPTIONS += --no-code-duplication
test-matches_duplicate:

.PHONY: test-%
test-%: CHARON_CMD = $(CHARON) --crate $* --input src/$*.rs $(OPTIONS)
test-%: build
	$(CHARON_CMD) --dest $(DEST)/llbc
	$(CHARON_CMD) --dest $(DEST)/llbc_opt --mir_optimized
	$(CHARON_CMD) --dest $(DEST)/llbc_release --release
	$(CHARON_CMD) --dest $(DEST)/llbc_release_opt --release --mir_optimized 
