CURRENT_DIR = $(shell pwd)
CHARON ?= $(CURRENT_DIR)/../bin/charon
DEST ?= .

.PHONY: all
all: build tests

.PHONY: build
build: format
	cargo rustc -- -Zpolonius

.PHONY: format
format:
	cargo fmt

.PHONY: test
test:
	cargo rustc -- --test -Zpolonius
	cd target/debug/ && ./betree

.PHONY: clean
clean:
	cargo clean
