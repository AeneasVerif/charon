ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

.PHONY: all
all: build tests

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

# Build the tests crate, and run the cargo tests
.PHONY: build-tests
build-tests:
	cd tests && $(MAKE) build && $(MAKE) cargo-tests

# Build the tests-polonius crate, and run the cargo tests
.PHONY: build-tests-polonius
build-tests-polonius:
	cd tests-polonius && $(MAKE) build && $(MAKE) cargo-tests

# Build and run the tests
.PHONY: tests
tests: build-tests build-tests-polonius charon-tests

# Run Charon on various test files
.PHONY: charon-tests
charon-tests: charon-tests-regular charon-tests-polonius

# Run Charon on the files in the tests crate
.PHONY: charon-tests-regular
charon-tests-regular: build-tests
	echo "# Starting the regular tests"
	cd tests && make charon-tests
	echo "# Finished the regular tests"

# Run Charon on the files in the tests-polonius crate
.PHONY: charon-tests-polonius
charon-tests-polonius: build-tests-polonius
	echo "# Starting the Polonius tests"
	cd tests-polonius && make charon-tests
	echo "# Finished the Polonius tests"

.PHONY: clean
clean:
	cd attributes && cargo clean
	cd charon && cargo clean
	cd charon/macros && cargo clean
	cd tests && cargo clean
	cd tests-polonius && cargo clean
	rm -rf tests/llbc
	rm -rf tests-polonius/llbc

# Build the Nix packages
.PHONY: nix
nix: nix-tests nix-tests-polonius

.PHONY: nix-tests
nix-tests:
	nix build .#hydraJobs.tests.x86_64-linux --show-trace -L

.PHONY: nix-tests-polonius
nix-tests-polonius:
	nix build .#hydraJobs.tests-polonius.x86_64-linux --show-trace -L
