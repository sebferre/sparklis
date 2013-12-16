
osparklis:
	ocamlfind ocamlc -package js_of_ocaml -package js_of_ocaml.syntax -syntax camlp4o -linkpkg -o osparklis.byte osparklis.ml
	js_of_ocaml osparklis.byte

install:
	cp osparklis.html /local/ferre/web/ferre/sparklis
	cp osparklis.css /local/ferre/web/ferre/sparklis
	cp osparklis.js /local/ferre/web/ferre/sparklis

