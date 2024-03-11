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
	dune promote

.PHONY: copy-tests
copy-tests:
	mkdir -p tests/serialized
	cp ../tests/llbc/* tests/serialized
	cp ../tests-polonius/llbc/* tests/serialized
