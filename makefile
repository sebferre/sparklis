
OBJ=common.cmo find_merge.cmo cache.cmo jsutils.cmo config.cmo rdf.cmo sparql.cmo sparql_endpoint.cmo ontology.cmo lisql.cmo lisql_annot.cmo lexicon.cmo grammar.cmo lisql2nl.cmo lisql2sparql.cmo lisql_type.cmo lis.cmo permalink.cmo html.cmo

osparklis: $(OBJ)
	ocamlfind ocamlc -package lwt,js_of_ocaml,js_of_ocaml-lwt,lwt_ppx,js_of_ocaml-ppx -linkpkg -o osparklis.byte $(OBJ) osparklis.ml
	js_of_ocaml osparklis.byte

install:
	cp log/.htaccess /local/ferre/web/ferre/sparklis/log
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
	cp release_notes.html /local/ferre/web/ferre/sparklis

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
	cp release_notes.html /local/ferre/web/ferre/sparklis-dev

pack: osparklis.js
	rm -f package/*
	cp osparklis.html package/index.html
	cp osparklis.css package/
	cp osparklis.js package/
	cp *.png package/
	cp *.jpg package/
	cp examples.html package/
	cp release_notes.html package/
	zip sparklis-package.zip package/*

clean:
	rm -f *.cm[ioax]


.SUFFIXES: .ml .mli .cmo .cmi

permalink.cmo: permalink.ml
	ocamlfind ocamlc -package lwt,js_of_ocaml,js_of_ocaml-lwt,lwt_ppx,js_of_ocaml-ppx -pp camlp5o -c $<

%.cmo: %.ml
	ocamlfind ocamlc -package lwt,js_of_ocaml,js_of_ocaml-lwt,lwt_ppx,js_of_ocaml-ppx -c $<
