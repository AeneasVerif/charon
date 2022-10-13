# We use Polonius.
# Note that we need to make sure the files are compiled with a very specific
# version of rustc (the same which is used by Charon), otherwise Charon can't
# use the already compiled external dependencies.

NIGHTLY = +nightly-2022-01-29

.PHONY: all
all: build tests

.PHONY: build
build:
	cargo $(NIGHTLY) rustc -- -Zpolonius

.PHONY: build-tests
build-tests:
	cargo $(NIGHTLY) rustc -- --test -Zpolonius

.PHONY: tests
tests: build-tests
	cd target/debug/ && ./tests
