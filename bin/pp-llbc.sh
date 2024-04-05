#!/usr/bin/env bash
CHARON_ARGS='{"print_llbc":true,"no_serialize_llbc":true}' ./bin/charon-driver rustc "$@"
