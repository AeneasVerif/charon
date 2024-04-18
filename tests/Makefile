CURRENT_DIR = $(shell pwd)
# Outside of CI, ensure the correct toolchain is available (for the dynamic libraries).
# FIXME: don't hardcode the toolchain
TOOLCHAIN := nightly-2023-06-02-x86_64-unknown-linux-gnu
CHARON_DRIVER ?= rustup run $(TOOLCHAIN) $(CURRENT_DIR)/../bin/charon-driver
DEST ?= .
OPTIONS ?=
CHARON_CMD :=
NOT_ALL_TESTS ?=

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

.PHONY: charon-tests
charon-tests: \
	test-nested_borrows test-no_nested_borrows \
	test-loops test-loops_cfg test-hashmap \
	test-paper test-hashmap_main \
	test-matches test-matches_duplicate test-external \
	test-constants test-arrays test-arrays_const_generics test-traits \
	test-closures test-bitwise test-demo

test-nested_borrows: OPTIONS += --no-code-duplication
test-no_nested_borrows: OPTIONS += --no-code-duplication
test-loops:
test-loops_cfg:
test-hashmap:
test-hashmap_main: OPTIONS += --opaque=hashmap_utils
test-paper: OPTIONS += --no-code-duplication
test-constants: OPTIONS += --no-code-duplication
# Possible to add `OPTIONS += --no-code-duplication` if we use the optimized MIR
test-matches:
test-external: OPTIONS += --no-code-duplication
test-matches_duplicate:
test-arrays:
test-arrays_const_generics:
test-traits:
test-traits_special:
test-closures:
test-bitwise:
test-demo:

# =============================================================================
# The tests.
# We use the NOT_ALL_TESTS variable to switch between the full test suite and a
# smaller one.
# =============================================================================

.PHONY: test-%
# The opt-level is set by default by cargo; some tests need it.
test-%: CHARON_CMD = $(CHARON_DRIVER) rustc src/$*.rs -C opt-level=3 -- --crate $* $(OPTIONS)
test-%: build

.PHONY: clean
clean:
	rm -f $(DEST)/llbc/* \
	rm -f $(DEST)/ullbc/* \
	rm -f $(DEST)/llbc_prom/* \
	rm -f $(DEST)/llbc_opt/*

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

test-%:
	$(CHARON_CMD) --dest $(DEST)/llbc

endif
