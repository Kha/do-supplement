.PHONY: all lean alectryon clean

all: lean

lean:
	lake build

%.html: %.lean
	PATH=$$PATH:$$PWD/../LeanInk/build/bin ../alectryon/alectryon.py --frontend lean4+rst $< -o $@ --lake lakefile.lean

SRC=$(shell find . -name '*.lean')
alectryon: $(patsubst %.lean,%.html,$(SRC))

clean:
	rm -rf build/
	find . -name '*.html' -delete
