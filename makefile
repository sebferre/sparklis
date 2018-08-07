
OBJ=common.cmo cache.cmo jsutils.cmo config.cmo rdf.cmo sparql.cmo sparql_endpoint.cmo ontology.cmo lisql.cmo lisql_annot.cmo lexicon.cmo grammar.cmo lisql2nl.cmo lisql2sparql.cmo lisql_type.cmo lis.cmo permalink.cmo html.cmo

osparklis: $(OBJ)
	ocamlfind ocamlc -package lwt -package js_of_ocaml -package js_of_ocaml.syntax -syntax camlp4o -linkpkg -o osparklis.byte $(OBJ) osparklis.ml
	js_of_ocaml osparklis.byte

install:
	cp log/*.php /local/ferre/web/ferre/sparklis/log
	cp yasgui.min.css /local/ferre/web/ferre/sparklis
	cp yasgui.min.js /local/ferre/web/ferre/sparklis
	cp osparklis.html /local/ferre/web/ferre/sparklis
	cp osparklis.html /local/ferre/web/ferre/sparklis/index.html
	cp osparklis.css /local/ferre/web/ferre/sparklis
	cp osparklis.js /local/ferre/web/ferre/sparklis
	cp *.png /local/ferre/web/ferre/sparklis
	cp *.jpg /local/ferre/web/ferre/sparklis
	cp examples.html /local/ferre/web/ferre/sparklis

install-dev:
	cp yasgui.min.css /local/ferre/web/ferre/sparklis-dev
	cp yasgui.min.js /local/ferre/web/ferre/sparklis-dev
	cp osparklis.html /local/ferre/web/ferre/sparklis-dev
	cp osparklis.html /local/ferre/web/ferre/sparklis-dev/index.html
	cp osparklis.css /local/ferre/web/ferre/sparklis-dev
	cp osparklis.js /local/ferre/web/ferre/sparklis-dev
	cp *.png /local/ferre/web/ferre/sparklis-dev
	cp *.jpg /local/ferre/web/ferre/sparklis-dev
	cp examples.html /local/ferre/web/ferre/sparklis-dev

clean:
	rm -f *.cm[ioax]


.SUFFIXES: .ml .mli .cmo .cmi

%.cmo: %.ml
	ocamlfind ocamlc -package js_of_ocaml -package js_of_ocaml.syntax -syntax camlp4o -c $<
