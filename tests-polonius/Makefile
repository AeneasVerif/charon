.PHONY: all
all: build tests

.PHONY: build
build:
	cargo rustc -- -Zpolonius

.PHONY: build-tests
build-tests:
	cargo rustc -- --test -Zpolonius

.PHONY: tests
tests: build-tests
	cd target/debug/ && ./tests
