# We use Polonius

.PHONY: all
all: build tests

.PHONY: build
build:
	cargo +nightly rustc -- -Zpolonius

.PHONY: build-tests
build-tests:
	cargo +nightly rustc -- --test -Zpolonius

.PHONY: tests
tests: build-tests
	cd target/debug/ && ./tests
