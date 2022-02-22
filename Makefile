.PHONY: all
all: build tests

.PHONY: build
build:
	cd charon && cargo build

TESTS = ../tests
SRC = $(TESTS)/src
OPTIONS = --dest $(TESTS)/cfim

.PHONY: tests
tests: test-nested_borrows test-no_nested_borrows test-loops test-hashmap test-paper \
	test-matches test-matches_duplicate

test-nested_borrows: OPTIONS += --no-code-duplication
test-no_nested_borrows: OPTIONS += --no-code-duplication
test-loops: OPTIONS += --no-code-duplication
test-hashmap: OPTIONS += --no-code-duplication
test-paper: OPTIONS += --no-code-duplication
test-matches: OPTIONS += --no-code-duplication
test-matches_duplicate:

.PHONY: test-%
test-%:
	cd charon && cargo run $(SRC)/$*.rs $(OPTIONS)
