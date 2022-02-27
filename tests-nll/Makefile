# We use Polonius

.PHONY: all
all: build tests

.PHONY: build
build:
	cargo +nightly-2022-01-29 -v rustc -- -Zpolonius

.PHONY: build-tests
build-tests:
	cargo +nightly-2022-01-29 rustc -- --test -Zpolonius

.PHONY: tests
tests: build-tests
	cd target/debug/ && ./tests
