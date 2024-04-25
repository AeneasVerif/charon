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

# =============================================================================
# The tests.
# =============================================================================

# We only test these two files
TESTS = polonius_list betree_main
RUST_SRCS = $(addprefix src/,$(addsuffix .rs,$(TESTS)))

# This depends on `llbc/<file>.llbc` for each `src/<file>.rs` we care about
.PHONY: charon-tests
charon-tests: $(subst src/,$(DEST)/llbc/,$(patsubst %.rs,%.llbc,$(RUST_SRCS)))

# llbc/polonius_list.llbc: OPTIONS += --no-code-duplication
# Possible to add `OPTIONS += --no-code-duplication` if we use the optimized MIR
# llbc/betree_main.llbc: OPTIONS += --no-code-duplication
$(DEST)/llbc/betree_main.llbc: OPTIONS += --opaque=betree_utils

$(DEST)/llbc/%.llbc: build
	$(CHARON) --crate $* --input src/$*.rs $(OPTIONS) --dest $(DEST)/llbc

.PHONY: test-%
test-%: $(DEST)/llbc/%.llbc
