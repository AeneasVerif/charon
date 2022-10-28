CURRENT_DIR = $(shell pwd)
CHARON ?= $(CURRENT_DIR)/../charon/target/debug/cargo-charon
DEST ?= .
OPTIONS = --polonius
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
	test-betree_polonius test-betree_main

# test-betree_polonius: OPTIONS += --no-code-duplication
test-betree_polonius:
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
	$(CHARON_CMD) --dest $(DEST)/ullbc --ullbc
	$(CHARON_CMD) --dest $(DEST)/llbc_prom --mir_promoted
	$(CHARON_CMD) --dest $(DEST)/llbc_opt --mir_optimized
	$(CHARON_CMD) --dest $(DEST)/llbc_release --release
	$(CHARON_CMD) --dest $(DEST)/llbc_release_prom --release --mir_promoted
# TODO: this fails for now (there is some very low-level desugaring happening)
#	$(CHARON_CMD) --dest $(DEST)/llbc_release_opt --release --mir_optimized 

else

.PHONY: test-%
test-%:
	$(CHARON_CMD) --dest $(DEST)/llbc

endif
