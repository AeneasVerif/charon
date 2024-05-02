# Build, after formatting the code
.PHONY: build
build: format build-dev

# Build, without formatting the code
.PHONY: build-dev
build-dev:
	dune build && dune build @doc

# The tests.
# You can use the environment variable "CHARON_LOG" to activate the log.
# For instance: `CHARON_LOG=1 make tests`.
.PHONY: tests
tests: build copy-tests
	dune test

# Reformat the code
.PHONY: format
format:
	@# `dune fmt` returns false if it had to change code; we don't care about that.
	dune fmt || true

# WARNING: This requires the llbc-building tests to have been run. Prefer using
# `make test` in the root directory.
.PHONY: copy-tests
copy-tests:
	mkdir -p tests/serialized
	rm -f tests/serialized/*
	cp ../charon/tests/**/*.llbc tests/serialized
