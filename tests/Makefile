CURRENT_DIR = $(shell pwd)
CHARON ?= $(CURRENT_DIR)/../bin/charon
DEST ?= .
OPTIONS ?=
CHARON_CMD :=

.PHONY: all
all: build tests

.PHONY: build
build: format
	cargo build

.PHONY: format
format:
	cargo fmt

.PHONY: tests
tests: cargo-tests charon-tests

.PHONY: cargo-tests
cargo-tests: build
	cargo test

# =============================================================================
# The tests.
# =============================================================================

#  List the `.rs` files in `src/`
RUST_SRCS = $(wildcard src/*.rs)
# We test all rust files except these.
RUST_SRCS := $(filter-out src/lib.rs, $(RUST_SRCS))
RUST_SRCS := $(filter-out src/hashmap_utils.rs, $(RUST_SRCS))
RUST_SRCS := $(filter-out src/test_borrows.rs, $(RUST_SRCS))
RUST_SRCS := $(filter-out src/traits_special.rs, $(RUST_SRCS))

# This depends on `llbc/<file>.llbc` for each `src/<file>.rs` we care about
.PHONY: charon-tests
charon-tests: $(subst src/,$(DEST)/llbc/,$(patsubst %.rs,%.llbc,$(RUST_SRCS)))

$(DEST)/llbc/hashmap_main.llbc: OPTIONS += --opaque=hashmap_utils
$(DEST)/llbc/nested_borrows.llbc: OPTIONS += --no-code-duplication
$(DEST)/llbc/no_nested_borrows.llbc: OPTIONS += --no-code-duplication
$(DEST)/llbc/paper.llbc: OPTIONS += --no-code-duplication
$(DEST)/llbc/constants.llbc: OPTIONS += --no-code-duplication
# Possible to add `OPTIONS += --no-code-duplication` if we use the optimized MIR
$(DEST)/llbc/matches.llbc:
$(DEST)/llbc/external.llbc: OPTIONS += --no-code-duplication

$(DEST)/llbc/%.llbc: build
	$(CHARON) --no-cargo --input src/$*.rs --crate $* $(OPTIONS) --dest $(DEST)/llbc

.PHONY: test-%
test-%: $(DEST)/llbc/%.llbc
	@true

.PHONY: clean
clean:
	cargo clean
	rm -f $(DEST)/llbc/*
