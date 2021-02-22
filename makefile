
OBJ=common.cmo find_merge.cmo cache.cmo jsutils.cmo config.cmo rdf.cmo sparql.cmo sparql_endpoint.cmo ontology.cmo lisql.cmo lisql_annot.cmo lexicon.cmo grammar.cmo lisql2nl.cmo lisql2sparql.cmo lisql_type.cmo lis.cmo permalink.cmo html.cmo

osparklis: $(OBJ)
	ocamlfind ocamlc -package csv,lwt,js_of_ocaml,js_of_ocaml-lwt,lwt_ppx,js_of_ocaml-ppx -linkpkg -o osparklis.byte $(OBJ) osparklis.ml
	js_of_ocaml osparklis.byte
	mv osparklis.js webapp/

install:
	cp -r webapp/* /local/ferre/web/ferre/sparklis

install-dev:
	cp -r webapp/* /local/ferre/web/ferre/sparklis-dev

pack: webapp/osparklis.js
	zip -r sparklis-webapp.zip webapp

clean:
	rm -f *.cm[ioax]


.SUFFIXES: .ml .mli .cmo .cmi

permalink.cmo: permalink.ml
	ocamlfind ocamlc -package lwt,js_of_ocaml,js_of_ocaml-lwt,lwt_ppx,js_of_ocaml-ppx -pp camlp5o -c $<

%.cmo: %.ml
	ocamlfind ocamlc -package csv,lwt,js_of_ocaml,js_of_ocaml-lwt,lwt_ppx,js_of_ocaml-ppx -c $<
