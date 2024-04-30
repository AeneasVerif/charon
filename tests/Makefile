CURRENT_DIR = $(shell pwd)
CHARON ?= $(CURRENT_DIR)/../bin/charon
DEST ?= .
OPTIONS ?=
CHARON_CMD :=

.PHONY: all
all: tests

.PHONY: format
format:
	rustfmt src/*.rs

.PHONY: tests
tests: charon-tests

# =============================================================================
# The tests.
# =============================================================================

#  List the `.rs` files in `src/`
RUST_SRCS = $(wildcard src/*.rs)
# We test all rust files except this one.
RUST_SRCS := $(filter-out src/hashmap_utils.rs, $(RUST_SRCS))

# This depends on `llbc/<file>.llbc` for each `src/<file>.rs` we care about
.PHONY: charon-tests
charon-tests: $(subst src/,$(DEST)/llbc/,$(patsubst %.rs,%.llbc,$(RUST_SRCS)))

$(DEST)/llbc/hashmap_main.llbc: OPTIONS += --opaque=hashmap_utils
$(DEST)/llbc/nested_borrows.llbc: OPTIONS += --no-code-duplication
$(DEST)/llbc/no_nested_borrows.llbc: OPTIONS += --no-code-duplication
$(DEST)/llbc/paper.llbc: OPTIONS += --no-code-duplication
$(DEST)/llbc/constants.llbc: OPTIONS += --no-code-duplication
$(DEST)/llbc/external.llbc: OPTIONS += --no-code-duplication
$(DEST)/llbc/polonius_list.llbc: OPTIONS += --polonius

$(DEST)/llbc/%.llbc: format
	$(CHARON) --no-cargo --input src/$*.rs --crate $* $(OPTIONS) --dest $(DEST)/llbc

.PHONY: test-%
test-%: $(DEST)/llbc/%.llbc
	@true

.PHONY: clean
clean:
	rm -rf target/
	rm -f $(DEST)/llbc/*
