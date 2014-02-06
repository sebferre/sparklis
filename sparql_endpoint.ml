
open Js
open XmlHttpRequest
open Jsutils

(* SPARQL results JSon <--> OCaml *)

type results =
    { dim : int;
      vars : (string * int) list; (* the int is the rank of the string in the list *)
      length : int;
      bindings : Rdf.term option array list;
    }

let empty_results = { dim=0; vars=[]; length=0; bindings=[]; }

module Xml =
struct
  let find (elt : Dom.element t) (tag : string) : Dom.element t =
    let nodelist = elt##getElementsByTagName(string tag) in
    Opt.get (nodelist##item(0))
      (fun () -> failwith ("Xml.find: unfound tag: " ^ tag))

  let find_all (elt : Dom.element t) (tag : string) : Dom.element t list =
    let nodelist = elt##getElementsByTagName(string tag) in
    let l = nodelist##length in
    let res = ref [] in
    for i = l-1 downto 0 do
      Opt.case (nodelist##item(i))
	(fun () -> ())
	(fun e -> res := e::!res)
    done;
    !res

  let get_text (elt : Dom.element t) : string =
    Opt.case (elt##firstChild)
      (fun () -> "")
      (fun node ->
	if node##nodeType = Dom.TEXT
	then
	  Opt.case (node##nodeValue)
	    (fun () -> "")
	    (fun s -> to_string s)
	else "")
end

let results_of_xml (doc_xml : Dom.element Dom.document t) =
  Firebug.console##log(string "Entering sparql_results_of_xml");
  try
    let elt_xml : Dom.element t = doc_xml##documentElement in
    (try
      let elt_boolean = Xml.find elt_xml "boolean" in
      match Xml.get_text elt_boolean with
	| "true" -> { dim=0; vars=[]; length=1; bindings=[ [||] ]; }
	| _ -> empty_results
    with _ ->
      let elt_head : Dom.element t = Xml.find elt_xml "head" in
      let elts_var = Xml.find_all elt_head "variable" in
      let dim, rev_vars =
	List.fold_left
	  (fun (i, vars as res) elt_var ->
	    Opt.case (elt_var##getAttribute(string "name"))
	      (fun _ -> res)
	      (fun v ->
		let v = to_string v in
		if v = "_star_fake"
		then res
		else (i+1, (v,i)::vars)))
	  (0,[]) elts_var in
      let vars = List.rev rev_vars in
      let elt_results = Xml.find elt_xml "results" in
      let elts_result = Xml.find_all elt_results "result" in
      let length, rev_bindings =
	List.fold_left
	  (fun (j,l) elt_result ->
	    let binding = Array.make dim None in
	    let elts_binding = Xml.find_all elt_result "binding" in
	    List.iter
	      (fun elt_binding ->
		Opt.case (elt_binding##getAttribute(string "name"))
		  (fun () -> ())
		  (fun v ->
		    let i = List.assoc (to_string v) vars in
		    let term_opt =
		      try
			let elt_uri = Xml.find elt_binding "uri" in
			let uri = Xml.get_text elt_uri in
			Some (Rdf.URI uri)
		      with _ ->
			try
			  let elt_lit = Xml.find elt_binding "literal" in
			  let s = Xml.get_text elt_lit in
			  Opt.case (elt_lit##getAttribute(string "xml:lang"))
			    (fun () ->
			      Opt.case (elt_lit##getAttribute(string "datatype"))
				(fun () -> Some (Rdf.PlainLiteral (s, "")))
				(fun dt ->
				  try Some (Rdf.Number (float_of_string s, s, to_string dt))
				  with _ -> Some (Rdf.TypedLiteral (s, to_string dt))))
			    (fun lang -> Some (Rdf.PlainLiteral (s, to_string lang)))
			with _ ->
			  try
			    let elt_bnode = Xml.find elt_binding "bnode" in
			    let id = Xml.get_text elt_bnode in
			    Some (Rdf.Bnode id)
			  with _ ->
			    None in
		    binding.(i) <- term_opt))
	      elts_binding;
	    (j+1, binding::l))
	  (0,[]) elts_result in
      let bindings = List.rev rev_bindings in
      { dim; vars; length; bindings; })
  with exn ->
    Firebug.console##log(string (Printexc.to_string exn));
    empty_results

let results_of_json s_json =
  try
    let ojson = Json.unsafe_input (string s_json) in
    let ohead = Unsafe.get ojson (string "head") in
    let ovars = Unsafe.get ohead (string "vars") in
    let m = truncate (to_float (Unsafe.get ovars (string "length"))) in
    let dim, vars =
      let dim = ref 0 in
      let vars = ref [] in
      for i = m-1 downto 0 do
	let ovar = Unsafe.get ovars (string (string_of_int i)) in
	let var = to_string (Unsafe.get ovar (string "fullBytes")) in
	if var <> "_star_fake"
	then begin incr dim; vars := (var,i)::!vars end
      done;
      !dim, !vars in
    let oresults = Unsafe.get ojson (string "results") in
    let obindings = Unsafe.get oresults (string "bindings") in
    let n = truncate (to_float (Unsafe.get obindings (string "length"))) in
    let length, bindings =
      let len = ref 0 in
      let res = ref [] in
      for j = n-1 downto 0 do
	let obinding = Unsafe.get obindings (string (string_of_int j)) in
	let binding = Array.make m None in
	List.iter
	  (fun (var,i) ->
	    try
	      let ocell = Unsafe.get obinding (string var) in
	      let otype = Unsafe.get ocell (string "type") in
	      let ovalue = Unsafe.get ocell (string "value") in
	      let term =
		let v = Unsafe.get ovalue (string "fullBytes") in
		match to_string (Unsafe.get otype (string "fullBytes")) with
		  | "uri" -> Rdf.URI (to_string v (*decodeURI v*))
		  | "bnode" -> Rdf.Bnode (to_string v)
		  | "typed-literal" ->
		    let odatatype = Unsafe.get ocell (string "datatype") in
		    let s = to_string v in
		    let dt = to_string (decodeURI (Unsafe.get odatatype (string "fullBytes"))) in
		    (try Rdf.Number (float_of_string s, s, dt)
		     with _ -> Rdf.TypedLiteral (s, dt))
		  | "plain-literal" ->
		    let olang = Unsafe.get ocell (string "xml:lang") in
		    Rdf.PlainLiteral (to_string v, to_string (Unsafe.get olang (string "fullBytes")))
		  | "literal" ->
		    ( try
			let odatatype = Unsafe.get ocell (string "datatype") in
			let s = to_string v in
			let dt = to_string (decodeURI (Unsafe.get odatatype (string "fullBytes"))) in
			(try Rdf.Number (float_of_string s, s, dt)
			 with _ -> Rdf.TypedLiteral (s, dt))
		      with _ ->
			let olang = Unsafe.get ocell (string "xml:lang") in
			Rdf.PlainLiteral (to_string v, to_string (Unsafe.get olang (string "fullBytes"))) )
		  | other ->
		    Firebug.console##log(string ("unexpected value type in SPARQL results: " ^ other));
		    assert false in
	      binding.(i) <- Some term
	    with _ ->
	      binding.(i) <- None)
	  vars;
	incr len;
	res := binding::!res
      done;
      !len, !res in
    { dim; vars; length; bindings; }
  with exn ->
    Firebug.console##log(s_json);
    Firebug.console##log(string (Printexc.to_string exn));
    empty_results

(* HTTP Requests to SPARQL endpoints *)

let ajax (pool : ajax_pool) (endpoint : string) (sparql : string)
    (k1 : results -> unit) (k0 : int -> unit) =
  (*Firebug.console##log(string sparql);*)
  let fields : (string * Form.form_elt) list =
    [("query", `String (string sparql))] in
  let req = create () in
  pool#add req;
  req##_open (Js.string "POST", Js.string endpoint, Js._true);
  req##setRequestHeader (Js.string "Content-type", Js.string "application/x-www-form-urlencoded");
(*  req##setRequestHeader (Js.string "Content-type", Js.string "application/sparql-query"); *)
  req##setRequestHeader (Js.string "Accept", Js.string "application/sparql-results+xml");
(*
  let headers s =
    Opt.case
      (req##getResponseHeader (Js.bytestring s))
      (fun () -> None)
      (fun v -> Some (Js.to_string v)) in  
*)
  let do_check_headers () = () in
  req##onreadystatechange <- Js.wrap_callback
    (fun _ ->
       (match req##readyState with
          (* IE doesn't have the same semantics for HEADERS_RECEIVED.
             so we wait til LOADING to check headers. See:
             http://msdn.microsoft.com/en-us/library/ms534361(v=vs.85).aspx *)
        | HEADERS_RECEIVED when not Dom_html.onIE -> do_check_headers ()
        | LOADING when Dom_html.onIE -> do_check_headers ()
        | DONE ->
	  pool#remove req;
	  do_check_headers ();
	  let code = req##status in
	  Firebug.console##log(string ("HTTP code: " ^ string_of_int code));
	  Firebug.console##log(req##statusText);
	  ( match code / 100 with
	    | 2 ->
	     (*Firebug.console##log(req##responseText);*)
	     (*	let results = results_of_json xhr.content in *)
              let results_opt =
                match Js.Opt.to_option (req##responseXML) with
                  | None -> None
                  | Some doc ->
                    if (Js.some doc##documentElement) == Js.null
                    then None
                    else Some (results_of_xml doc) in
	      ( match results_opt with
		| None ->
		  Firebug.console##log(string "No XML content");
		  ()
		| Some results -> k1 results )
	    | 0 ->
	      alert "The SPARQL endpoint is not responsive. Check that the URL is correct, and that the server is running. Otherwise, a frequent cause for this error is that the SPARQL endpoint does not allow cross-origin HTTP requests. You can contact and ask the endpoint administrator to use the Cross-Origin Resource Sharing mechanism (CORS).";
	      k0 code
	    | 4 ->
	      alert "The query was not understood by the SPARQL endpoint. The reason is probably that some SPARQL features used by Sparklis are not supported by the endpoint. The minimum required SPARQL features are: UNION, DISTINCT, LIMIT. Other features depend on the current query.";
	      k0 code
	    | 5 ->
	      alert "There was an error at the SPARQL endpoint during the evaluation of the query.";
	      k0 code
	    | _ ->
	      alert ("Error " ^ string_of_int code);
	      k0 code )
        | _ -> ()));
  let encode_fields l =
    String.concat "&"
      (List.map
	 (function
           | name,`String s -> ((Url.urlencode name) ^ "=" ^ (Url.urlencode (to_string s)))
           | name,`File s -> ((Url.urlencode name) ^ "=" ^ (Url.urlencode (to_string (s##name)))))
	 l) in
  req##send(Js.some (string (encode_fields fields)))
(*  req##send(Js.some (string sparql)) *)

let rec ajax_list pool endpoint sparql_list k1 k0 =
  match sparql_list with
    | [] -> k1 []
    | s::ls ->
      ajax pool endpoint s
	(fun r ->
	  ajax_list pool endpoint ls
	    (fun rs -> k1 (r::rs))
	    (fun code -> k0 code))
	(fun code -> k0 code)

let ajax_in elts pool endpoint sparql k1 k0 =
  progress elts (ajax pool endpoint sparql) k1 k0
let ajax_list_in elts pool endpoint sparql_list k1 k0 =
  progress elts (ajax_list pool endpoint sparql_list) k1 k0
