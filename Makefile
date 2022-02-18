.PHONY: all
all: build tests

.PHONY: build
build:
	cd charon && cargo build

TESTS = ../tests
SRC = $(TESTS)/src
OPTIONS = --dest $(TESTS)/cfim

.PHONY: tests
tests: test-nested_borrows test-no_nested_borrows test-loops test-hashmap test-paper

.PHONY: test-%
test-%:
	cd charon && cargo run $(SRC)/$*.rs $(OPTIONS)
