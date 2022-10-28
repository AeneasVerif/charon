OPTIONS ?=

.PHONY: build
build:
	dune build && dune build @doc

.PHONY: tests
tests: build
	dune exec tests/test_deserialize.exe -- $(OPTIONS) ../tests/ullbc/
	dune exec tests/test_deserialize.exe -- $(OPTIONS) ../tests/llbc/
	dune exec tests/test_deserialize.exe -- $(OPTIONS) ../tests-polonius/ullbc/
	dune exec tests/test_deserialize.exe -- $(OPTIONS) ../tests-polonius/llbc/

# Reformat the code
.PHONY: format
format:
	dune promote
