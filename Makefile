.PHONY: build clean help

build:
	opam exec dune -- build

test_parsing: build
	./test -1 ./pyretc.exe

test_typing: build
	./test -2 ./pyretc.exe

test_exec: build
	./test -3 ./pyretc.exe

test_file: build
	./pyretc.exe ./test_exec.arr
	gcc -g -no-pie test_exec.s
	./a.out

clean:
	opam exec dune -- clean

help:
	@echo "Available targets:"
	@echo "  test_parsing - Run parsing tests"
	@echo "  test_typing  - Run typing tests"
	@echo "  test_exec    - Run execution tests"
	@echo "  build   - Build the project with dune"
	@echo "  clean   - Clean build artifacts"
	@echo "  help    - Show this help message"

.DEFAULT_GOAL := build