CURRENT_DIR = $(shell pwd)
CHARON ?= $(CURRENT_DIR)/../bin/charon
DEST ?= .

.PHONY: all
all: build tests

.PHONY: build
build: format
	cargo rustc -- -Zpolonius

ifdef IN_CI
# In CI, error if formatting is not done.
format: RUSTFMT_FLAGS := --check
endif

.PHONY: format
format:
	cargo fmt $(RUSTFMT_FLAGS)

.PHONY: test
test:
	cargo rustc -- --test -Zpolonius
	cd target/debug/ && ./betree

.PHONY: clean
clean:
	cargo clean
