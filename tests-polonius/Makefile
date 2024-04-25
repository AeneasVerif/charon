CURRENT_DIR = $(shell pwd)
# Call `charon` instead of `charon-driver` because we have dependencies in `Cargo.toml`.
CHARON ?= $(CURRENT_DIR)/../bin/charon
DEST ?= .
OPTIONS += --polonius

.PHONY: all
all: build tests

.PHONY: build
build: format
	cargo rustc -- -Zpolonius

.PHONY: format
format:
	cargo fmt

.PHONY: tests
tests: cargo-tests charon-tests

.PHONY: cargo-tests
cargo-tests: build-tests
	cd target/debug/ && ./tests

.PHONY: build-tests
build-tests:
	cargo rustc -- --test -Zpolonius

.PHONY: charon-tests
charon-tests: \
	test-polonius_list test-betree_main

# test-polonius_list: OPTIONS += --no-code-duplication
test-polonius_list:
# Possible to add `OPTIONS += --no-code-duplication` if we use the optimized MIR
# test-betree_main: OPTIONS += --no-code-duplication
test-betree_main: OPTIONS += --opaque=betree_utils

# =============================================================================
# The tests.
# =============================================================================

.PHONY: test-%
test-%: build
	$(CHARON) --crate $* --input src/$*.rs $(OPTIONS) --dest $(DEST)/llbc
