CURRENT_DIR = $(shell pwd)
CHARON ?= $(CURRENT_DIR)/../bin/charon
DEST ?= .

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
cargo-tests:
	cargo rustc -- --test -Zpolonius
	cd target/debug/ && ./betree

# =============================================================================
# The tests.
# =============================================================================

.PHONY: charon-tests
charon-tests: $(DEST)/llbc/betree.llbc

# Possible to add `--no-code-duplication` if we use the optimized MIR
$(DEST)/llbc/betree.llbc: build
	$(CHARON) --polonius --opaque=betree_utils --crate betree_main --dest $(DEST)/llbc

.PHONY: test-betree
test-betree: $(DEST)/llbc/betree.llbc

.PHONY: clean
clean:
	cargo clean
	rm -f $(DEST)/llbc/*
