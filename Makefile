ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

.PHONY: all
all: tests

# We use Rust nightly in order to:
# - be able to write a Rustc plugin
# - use Polonius in some tests
# We keep the nightly version in sync in all the crates by copy-pasting
# a template file for the toolchain.
# Rem.: this is not really necessary for the `tests` crate.
.PHONY: generate-rust-toolchain
generate-rust-toolchain:
	cp rust-toolchain.template charon/rust-toolchain
	cp rust-toolchain.template tests/rust-toolchain
	cp rust-toolchain.template tests-nll/rust-toolchain

.PHONY: build
build: generate-rust-toolchain
	cd charon && $(MAKE)

CURRENT_DIR = $(shell pwd)
OPTIONS = --dest llbc
CHARON = $(CURRENT_DIR)/charon/target/debug/cargo-charon

.PHONY: build-tests
build-tests:
	cd tests && $(MAKE)

.PHONY: build-tests-nll
build-tests-nll:
	cd tests-nll && $(MAKE)

.PHONY: tests
tests: build build-tests build-tests-nll \
	test-nested_borrows test-no_nested_borrows test-loops test-hashmap \
	test-paper test-hashmap_main \
	test-matches test-matches_duplicate test-external \
        test-constants \
	test-nll-betree_nll test-nll-betree_main

test-nested_borrows: OPTIONS += --no-code-duplication
test-no_nested_borrows: OPTIONS += --no-code-duplication
test-loops: OPTIONS += --no-code-duplication
#test-hashmap: OPTIONS += --no-code-duplication
#test-hashmap_main: OPTIONS += --no-code-duplication
test-hashmap_main: OPTIONS += --opaque=hashmap_utils
test-paper: OPTIONS += --no-code-duplication
test-constants: OPTIONS += --no-code-duplication
# Possible to add `OPTIONS += --no-code-duplication` if we use the optimized MIR
test-matches:
test-external: OPTIONS += --no-code-duplication
test-matches_duplicate:
#test-nll-betree_nll: OPTIONS += --no-code-duplication
# Possible to add `OPTIONS += --no-code-duplication` if we use the optimized MIR
test-nll-betree_main:
test-nll-betree_main: OPTIONS += --opaque=betree_utils

.PHONY: test-nll-%
test-nll-%: OPTIONS += --nll
test-nll-%: build
	cd tests-nll && $(CHARON) --crate $* --input src/$*.rs $(OPTIONS)

.PHONY: test-%
test-%: build
	cd tests && $(CHARON) --crate $* --input src/$*.rs $(OPTIONS)

.PHONY: clean
clean:
	cd attributes && cargo clean
	cd charon && cargo clean
	cd charon/macros && cargo clean
	cd tests && cargo clean
	cd tests-nll && cargo clean
	rm -rf tests/llbc
	rm -rf tests-nll/llbc
