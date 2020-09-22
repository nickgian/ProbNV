.PHONY: test clean

default:
	dune build src/exe/main.exe
	cp _build/default/src/exe/main.exe probNv


doc:
	dune build @doc

clean:
	dune clean
	rm -f probNv
