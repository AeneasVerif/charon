CURRENT_DIR = $(shell pwd)
CHARON ?= $(CURRENT_DIR)/../charon/target/debug/cargo-charon
DEST ?= .
OPTIONS = --polonius

.PHONY: all
all: build tests

.PHONY: build
build:
	cargo rustc -- -Zpolonius

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
	test-betree_polonius test-betree_main

# test-betree_polonius: OPTIONS += --no-code-duplication
test-betree_polonius:
# Possible to add `OPTIONS += --no-code-duplication` if we use the optimized MIR
# test-betree_main: OPTIONS += --no-code-duplication
test-betree_main: OPTIONS += --opaque=betree_utils

.PHONY: test-%
test-%: CHARON_CMD = $(CHARON) --crate $* --input src/$*.rs $(OPTIONS)
test-%: build
	$(CHARON_CMD) --dest $(DEST)/llbc
	$(CHARON_CMD) --dest $(DEST)/llbc_opt --mir_optimized
	$(CHARON_CMD) --dest $(DEST)/llbc_release --release
	$(CHARON_CMD) --dest $(DEST)/llbc_release_opt --release --mir_optimized 
