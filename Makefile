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
	cp rust-toolchain.template tests-polonius/rust-toolchain

.PHONY: build
build: generate-rust-toolchain
	cd charon && $(MAKE)

CURRENT_DIR = $(shell pwd)
OPTIONS = --dest llbc
CHARON = $(CURRENT_DIR)/charon/target/debug/cargo-charon

.PHONY: build-tests
build-tests:
	cd tests && $(MAKE)

.PHONY: build-tests-polonius
build-tests-polonius:
	cd tests-polonius && $(MAKE)

.PHONY: tests
tests: build build-tests build-tests-polonius \
	test-nested_borrows test-no_nested_borrows test-loops test-hashmap \
	test-paper test-hashmap_main \
	test-matches test-matches_duplicate test-external \
        test-constants \
	test-polonius-betree_polonius test-polonius-betree_main

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
#test-polonius-betree_polonius: OPTIONS += --no-code-duplication
test-polonius-betree_polonius:
# Possible to add `OPTIONS += --no-code-duplication` if we use the optimized MIR
test-polonius-betree_main:
test-polonius-betree_main: OPTIONS += --opaque=betree_utils

.PHONY: test-polonius-%
test-polonius-%: OPTIONS += --polonius
test-polonius-%: build
	cd tests-polonius && $(CHARON) --crate $* --input src/$*.rs $(OPTIONS)

.PHONY: test-%
test-%: build
	cd tests && $(CHARON) --crate $* --input src/$*.rs $(OPTIONS)

.PHONY: clean
clean:
	cd attributes && cargo clean
	cd charon && cargo clean
	cd charon/macros && cargo clean
	cd tests && cargo clean
	cd tests-polonius && cargo clean
	rm -rf tests/llbc
	rm -rf tests-polonius/llbc

.PHONY: nix-build
nix-build:
	nix build

.PHONY: nix-tests
nix-tests:
	nix build .#hydraJobs.tests.x86_64-linux --show-trace

.PHONY: nix-tests-polonius
nix-tests-polonius:
	nix build .#hydraJobs.tests-polonius.x86_64-linux --show-trace
