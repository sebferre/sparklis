
OBJ=jsutils.cmo rdf.cmo sparql.cmo sparql_endpoint.cmo lisql.cmo lisql2sparql.cmo lisql2nl.cmo permalink.cmo lis.cmo html.cmo

osparklis: $(OBJ)
	ocamlfind ocamlc -package js_of_ocaml -package js_of_ocaml.syntax -syntax camlp4o -linkpkg -o osparklis.byte $(OBJ) osparklis.ml
	js_of_ocaml osparklis.byte

install:
	cp osparklis.html /local/ferre/web/ferre/sparklis
	cp osparklis.css /local/ferre/web/ferre/sparklis
	cp osparklis.js /local/ferre/web/ferre/sparklis
	cp *.png /local/ferre/web/ferre/sparklis
	cp *.jpg /local/ferre/web/ferre/sparklis
	cp examples.html /local/ferre/web/ferre/sparklis

clean:
	rm -f *.cm[ioax]


.SUFFIXES: .ml .mli .cmo .cmi

%.cmo: %.ml
	ocamlfind ocamlc -package js_of_ocaml -package js_of_ocaml.syntax -syntax camlp4o -c $<
