
reporting: reporting.ml
	ocamlc -I .. -o reporting str.cma unix.cma ../common.cmo ../rdf.cmo ../lisql.cmo ../permalink.cmo reporting.ml

clean:
	rm -f *.cm[ioax]

.SUFFIXES: .ml .mli .cmo .cmi

%.cmo: %.ml
	ocamlfind ocamlc -package js_of_ocaml -c $<

