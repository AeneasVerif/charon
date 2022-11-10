.PHONY: build
build:
	dune build && dune build @doc

.PHONY: tests
tests: build copy-tests
	dune runtest -p charon

.PHONY: tests
tests-cmd: build
	dune exec tests/test_cmd.exe -- $(OPTIONS) ../tests/ullbc/
	dune exec tests/test_cmd.exe -- $(OPTIONS) ../tests/llbc/
	dune exec tests/test_cmd.exe -- $(OPTIONS) ../tests-polonius/ullbc/
	dune exec tests/test_cmd.exe -- $(OPTIONS) ../tests-polonius/llbc/

.PHONY: copy-tests
copy-tests:
	mkdir -p tests/serialized
	cp ../tests/ullbc/* tests/serialized
	cp ../tests/llbc/* tests/serialized
	cp ../tests-polonius/ullbc/* tests/serialized
	cp ../tests-polonius/llbc/* tests/serialized

# Reformat the code
.PHONY: format
format:
	dune promote
