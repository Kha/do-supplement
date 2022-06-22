.PHONY: all lean LeanInk html clean

all: lean

lean:
	lake build

LeanInk:
	cd LeanInk; lake build

%.html: %.lean | LeanInk
	PATH=$$PATH:$$PWD/LeanInk/build/bin alectryon --frontend lean4+rst $< -o $@ --lake lakefile.lean

SRC=$(shell find Do -name '*.lean')
html: $(patsubst %.lean,%.html,$(SRC))

clean:
	rm -rf build/
	find . -name '*.html' -delete
