# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: default build clean

default: build

build:
	dune build

clean:
	dune clean
