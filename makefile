
OBJ=common.cmo find_merge.cmo jsutils.cmo cache.cmo config.cmo rdf.cmo sparql.cmo sparql_endpoint.cmo ontology.cmo lisql.cmo lisql_annot.cmo lexicon.cmo grammar.cmo lisql2nl.cmo lisql2sparql.cmo lisql_type.cmo lis.cmo permalink.cmo html.cmo

FLAGS = # -g
#JSOO_FLAGS = --pretty --no-inline --debug-info # for dev
JSOO_FLAGS = --opt 3 # for prod

osparklis: $(OBJ)
	ocamlfind ocamlc -package csv,lwt,js_of_ocaml,js_of_ocaml-lwt,lwt_ppx,js_of_ocaml-ppx -linkpkg $(FLAGS) -o osparklis.byte $(OBJ) osparklis.ml
	js_of_ocaml $(JSOO_FLAGS) osparklis.byte
	mv osparklis.js webapp/

install:
	cp -r webapp/* /local/ferre/web/ferre/sparklis

install-dev:
	cp -r webapp/* /local/ferre/web/ferre/sparklis-dev

pack: webapp/osparklis.js
	rm -f sparklis-webapp.zip
	zip -j sparklis-webapp.zip webapp/osparklis.html webapp/osparklis.css webapp/osparklis.js webapp/examples.html webapp/release_notes.html webapp/irisa.jpg webapp/semlis.png webapp/UR1.png webapp/youtube.jpg webapp/example_extension.js

clean:
	rm -f *.cm[ioax]


.SUFFIXES: .ml .mli .cmo .cmi

permalink.cmo: permalink.ml
	ocamlfind ocamlc -package lwt,js_of_ocaml,js_of_ocaml-lwt,lwt_ppx,js_of_ocaml-ppx -pp camlp5o -c $(FLAGS) $<

%.cmo: %.ml
	ocamlfind ocamlc -g -package csv,lwt,js_of_ocaml,js_of_ocaml-lwt,lwt_ppx,js_of_ocaml-ppx -c $(FLAGS) $<
