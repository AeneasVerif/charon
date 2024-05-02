CURRENT_DIR = $(shell pwd)
CHARON ?= $(CURRENT_DIR)/../bin/charon
DEST ?= $(PWD)
OPTIONS ?=
CHARON_CMD :=
IN_CI ?=

.PHONY: all
all: tests

.PHONY: format
format:
	rustfmt src/*.rs
	cd src/betree && $(MAKE) format

.PHONY: tests
tests: charon-tests cargo-tests

.PHONY: cargo-tests
cargo-tests:
	cd src/betree && $(MAKE) build && $(MAKE) test

# =============================================================================
# The tests.
# =============================================================================

#  List the `.rs` files in `src/`
INDIVIDUAL_RUST_SRCS = $(wildcard src/*.rs)
# We test all rust files except this one.
INDIVIDUAL_RUST_SRCS := $(filter-out src/hashmap_utils.rs, $(INDIVIDUAL_RUST_SRCS))
INDIVIDUAL_LLBCS := $(subst src/,$(DEST)/llbc/,$(patsubst %.rs,%.llbc,$(INDIVIDUAL_RUST_SRCS)))

# This depends on `llbc/<file>.llbc` for each `src/<file>.rs` we care about, plus the whole-crate test.
.PHONY: charon-tests
charon-tests: $(INDIVIDUAL_LLBCS) $(DEST)/llbc/betree_main.llbc

$(DEST)/llbc/hashmap_main.llbc: OPTIONS += --opaque=hashmap_utils
$(DEST)/llbc/nested_borrows.llbc: OPTIONS += --no-code-duplication
$(DEST)/llbc/no_nested_borrows.llbc: OPTIONS += --no-code-duplication
$(DEST)/llbc/paper.llbc: OPTIONS += --no-code-duplication
$(DEST)/llbc/constants.llbc: OPTIONS += --no-code-duplication
$(DEST)/llbc/external.llbc: OPTIONS += --no-code-duplication
$(DEST)/llbc/polonius_list.llbc: OPTIONS += --polonius

$(DEST)/llbc/%.llbc: format
	$(CHARON) --no-cargo --input src/$*.rs --crate $* $(OPTIONS) --dest $(DEST)/llbc

# In CI, this llbc file is build separately to manage cargo dependencies.
ifndef IN_CI
# Special rule for the whole-crate test.
# Possible to add `--no-code-duplication` if we use the optimized MIR
$(DEST)/llbc/betree_main.llbc: OPTIONS += --polonius --opaque=betree_utils --crate betree_main
$(DEST)/llbc/betree_main.llbc:
	cd src/betree && $(CHARON) $(OPTIONS) --dest $(DEST)/llbc
else
$(DEST)/llbc/betree_main.llbc:
	@echo 'ERROR: `betree_main.llbc` should be built separately in CI'
	@false
endif

.PHONY: test-%
test-%: $(DEST)/llbc/%.llbc
	@true

.PHONY: clean
clean:
	rm -rf target/
	rm -rf $(DEST)/llbc
	cd src/betree && $(MAKE) clean
