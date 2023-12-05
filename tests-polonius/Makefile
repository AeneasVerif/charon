CURRENT_DIR = $(shell pwd)
CHARON ?= $(CURRENT_DIR)/../bin/charon
DEST ?= .
OPTIONS += --polonius
NOT_ALL_TESTS ?=

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
	test-polonius_list test-betree_main

# test-polonius_list: OPTIONS += --no-code-duplication
test-polonius_list:
# Possible to add `OPTIONS += --no-code-duplication` if we use the optimized MIR
# test-betree_main: OPTIONS += --no-code-duplication
test-betree_main: OPTIONS += --opaque=betree_utils

# =============================================================================
# The tests.
# We use the NOT_ALL_TESTS variable to switch between the full test suite and a
# smaller one.
# =============================================================================

.PHONY: test-%
test-%: CHARON_CMD = $(CHARON) --crate $* --input src/$*.rs $(OPTIONS)
test-%: build

ifeq (, $(NOT_ALL_TESTS))

test-%:
	$(CHARON_CMD) --dest $(DEST)/llbc
#	$(CHARON_CMD) --dest $(DEST)/ullbc --ullbc
# TODO: this fails for now (it seems some closures are turned into globals,
# and I don't know how to handle them).
#	$(CHARON_CMD) --dest $(DEST)/llbc_prom --mir_promoted
# TODO: this fails for now (there is some very low-level desugaring happening)
#	$(CHARON_CMD) --dest $(DEST)/llbc_opt --mir_optimized

else

.PHONY: test-%
test-%:
	$(CHARON_CMD) --dest $(DEST)/llbc

endif
