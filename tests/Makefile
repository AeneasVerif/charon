CURRENT_DIR = $(shell pwd)
CHARON ?= $(CURRENT_DIR)/../charon/target/debug/cargo-charon
DEST ?= .
OPTIONS =
CHARON_CMD :=

.PHONY: all
all: build tests

.PHONY: build
build:
	cargo build

.PHONY: tests
tests: cargo-tests charon-tests

.PHONY: cargo-tests
cargo-tests: build
	cargo test

.PHONY: charon-tests
charon-tests: \
	all-tests-nested_borrows all-tests-no_nested_borrows \
	all-tests-loops all-tests-hashmap \
	all-tests-paper all-tests-hashmap_main \
	all-tests-matches all-tests-matches_duplicate all-tests-external \
	all-tests-constants

all-tests-nested_borrows: OPTIONS += --no-code-duplication
all-tests-no_nested_borrows: OPTIONS += --no-code-duplication
all-tests-loops: OPTIONS += --no-code-duplication
# all-tests-hashmap: OPTIONS += --no-code-duplication
# all-tests-hashmap_main: OPTIONS += --no-code-duplication
all-tests-hashmap_main: OPTIONS += --opaque=hashmap_utils
all-tests-paper: OPTIONS += --no-code-duplication
all-tests-constants: OPTIONS += --no-code-duplication
# Possible to add `OPTIONS += --no-code-duplication` if we use the optimized MIR
all-tests-matches:
all-tests-external: OPTIONS += --no-code-duplication
all-tests-matches_duplicate:

.PHONY: all-tests-%
all-tests-%: CHARON_CMD = $(CHARON) --crate $* --input src/$*.rs $(OPTIONS)
all-tests-%: build test-%
	$(CHARON_CMD) --dest $(DEST)/ullbc --ullbc
	$(CHARON_CMD) --dest $(DEST)/llbc_prom --mir_promoted
	$(CHARON_CMD) --dest $(DEST)/llbc_opt --mir_optimized
	$(CHARON_CMD) --dest $(DEST)/llbc_release --release
	$(CHARON_CMD) --dest $(DEST)/llbc_release_prom --release --mir_promoted
# TODO: this fails for now (there is some very low-level desugaring happening)
#	$(CHARON_CMD) --dest $(DEST)/llbc_release_opt --release --mir_optimized 

test-%: build
	$(CHARON_CMD) --dest $(DEST)/llbc
