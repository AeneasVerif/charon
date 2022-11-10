.PHONY: build
build:
	dune build && dune build @doc

# The tests.
# You can use the environment variable "CHARON_LOG" to activate the log.
# For instance: `CHARON_LOG=1 make tests`.
.PHONY: tests
tests: build copy-tests
	dune runtest -p charon

# Reformat the code
.PHONY: format
format:
	dune promote

.PHONY: copy-tests
copy-tests:
	mkdir -p tests/serialized
	cp ../tests/ullbc/* tests/serialized
	cp ../tests/llbc/* tests/serialized
	cp ../tests-polonius/ullbc/* tests/serialized
	cp ../tests-polonius/llbc/* tests/serialized
