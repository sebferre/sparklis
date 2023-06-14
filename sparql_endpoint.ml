(*
   Copyright 2013 Sébastien Ferré, IRISA, Université de Rennes 1, ferre@irisa.fr

   This file is part of Sparklis.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

open Js_of_ocaml
open Js_of_ocaml_lwt
       
open Js
open XmlHttpRequest
open Jsutils

let sparql_ns = "http://www.w3.org/2005/sparql-results#"
		     
(* endpoint-specific aspects *)

let uri_of_id (id : string) : Rdf.uri option =
  if Common.has_prefix id "nodeID://" then Some id (* Virtuoso *)
  else None

(* SPARQL results JSon <--> OCaml *)

type binding = Rdf.term option array
type results =
    { dim : int;
      vars : (string * int) list; (* the int is the rank of the string in the list *)
      length : int;
      bindings : binding list;
    }

let js_binding_map : binding js_map =
  js_map
    (`Array (`Option (js_custom_spec Rdf.js_term_map)))
  
let js_results_map : results js_map =
  let js_cols_map : string list js_map =
    js_map (`List `String) in
  let js_rows_map : binding list js_map =
    js_map (`List (js_custom_spec js_binding_map)) in
  { spec = `Record [| "columns", js_cols_map.spec;
                      "rows", js_rows_map.spec |];
    inject =
      (fun res ->
        let cols =
          res.vars
          |> List.sort (fun (_,i) (_,j) -> Stdlib.compare i j)
          |> List.map (fun (v,i) -> v) in
        let rows = res.bindings in              
        Inject.(obj [| "columns", js_cols_map.inject cols;
                       "rows", js_rows_map.inject rows |]));
    extract =
      (fun js ->
        let js = Extract.as_object js in
        let cols = js_cols_map.extract (Extract.get js "columns") in
        let rows = js_rows_map.extract (Extract.get js "rows") in
        { dim = List.length cols;
          vars = List.mapi (fun i c -> (c,i)) cols;
          length = List.length rows;
          bindings = rows }) }
  
let empty_results = { dim=0; vars=[]; length=0; bindings=[]; }
let unit_results = { dim=0; vars=[]; length=1; bindings=[ [||] ]; }

let results_vars (res : results) =
  List.map fst res.vars

let results_are_empty (res : results) : bool =
  res.length = 0
		     
let float_of_results (res: results) : float option =
(* useful for simple aggregations returning a single number cell *)
  match res.bindings with
  | [ [| Some (Rdf.Number (f,_,_)) |] ] -> Some f
  | _ -> None

let csv_of_results ?(limit : int option) (res : results) : string =
  let buf = Buffer.create 10103 in
  let ch = Csv.to_buffer buf in
  Csv.output_record ch (List.map fst res.vars);
  let _ =
    let valid_rank =
      match limit with
      | None -> (fun rank -> true)
      | Some n -> (fun rank -> rank < n)
    in
    List.fold_left
      (fun rank binding ->
        if valid_rank rank then
          Csv.output_record ch
            (List.map
               (fun (v,i) ->
                 match binding.(i) with
                 | None -> ""
                 | Some term -> Rdf.string_of_term term) (* TODO: refine? language/datatype lost *)
               res.vars);
        rank+1)
      0 res.bindings in
  Csv.close_out ch;
  Buffer.contents buf

       
module Xml = (* CAUTION: some specifics to SPARQL results *)
struct
  let lookup_prefix (elt : Dom.element t) (ns : string) : string =
    let prefix = ref "" in
    let node_map = elt##.attributes in
    for i = 0 to node_map##.length - 1 do
      Opt.iter (node_map##item i)
	(fun a ->
	  let value = to_string a##.value in
	  if value = sparql_ns
	  then
	    let name = to_string a##.name in
	    try
	      let pre = String.sub name 6 (String.length name - 6) in (* 6 = length "xmlns:" *)
	      prefix := pre ^ ":"
	    with _ -> ())
    done;
    !prefix

  let get (elt : Dom.element t) (tag : string) : Dom.element t =
    let nodelist = elt##getElementsByTagName (string tag) in
    Opt.get (nodelist##item 0)
      (fun () -> failwith ("Sparql_endpoint.Xml.get: missing tag " ^ tag))

  let find (elt : Dom.element t) (tag : string) : Dom.element t option =
    try Some (get elt tag)
    with _ -> None

  let find_all (elt : Dom.element t) (tag : string) : Dom.element t list =
    let nodelist = elt##getElementsByTagName (string tag) in
    let l = nodelist##.length in
    let res = ref [] in
    for i = l-1 downto 0 do
      Opt.iter (nodelist##item i)
	(fun e -> res := e::!res)
    done;
    !res

  let get_attribute (elt : Dom.element t) (attr : string) : string =
    Opt.case (elt##getAttribute (string attr))
      (fun () -> failwith ("Sparql_endpoint.Xml.get_attribute: missing attribute " ^ attr))
      (fun js -> to_string js)

  let find_attribute (elt : Dom.element t) (attr : string) : string option =
    try Some (get_attribute elt attr)
    with _ -> None

  let get_text (elt : Dom.element t) : string =
    Opt.case elt##.firstChild
      (fun () -> "")
      (fun node ->
	if node##.nodeType = Dom.TEXT
	then
	  Opt.case node##.nodeValue
	    (fun () -> "")
	    (fun s -> String.trim (to_string s))
	else "")
end

let results_of_xml (doc_xml : Dom.element Dom.document t) =
  try
    let elt_xml : Dom.element t = doc_xml##.documentElement in
    let prefix = Xml.lookup_prefix elt_xml sparql_ns in
    match Xml.find elt_xml (prefix ^ "boolean") with
    | Some elt_boolean ->
      ( match Xml.get_text elt_boolean with
      | "true" -> unit_results
      | _ -> empty_results )
    | None ->
      let elt_head : Dom.element t = Xml.get elt_xml (prefix ^ "head") in
      let elts_var = Xml.find_all elt_head (prefix ^ "variable") in
      let dim, rev_vars =
	List.fold_left
	  (fun (i, vars as res) elt_var ->
	    let v = Xml.get_attribute elt_var "name" in
	    if v = "_star_fake"
	    then res
	    else (i+1, (v,i)::vars))
	  (0,[]) elts_var in
      let vars = List.rev rev_vars in
      let elt_results = Xml.get elt_xml (prefix ^ "results") in
      let elts_result = Xml.find_all elt_results (prefix ^ "result") in
      let length, rev_bindings =
	List.fold_left
	  (fun (j,l) elt_result ->
	    let binding = Array.make dim None in
	    let elts_binding = Xml.find_all elt_result (prefix ^ "binding") in
	    List.iter
	      (fun elt_binding ->
		let v = Xml.get_attribute elt_binding "name" in
		let i = try List.assoc v vars
			with _ -> failwith "Unexpected variable name in XML Sparql results" in
		let term_opt =
		  match Xml.find elt_binding (prefix ^ "uri") with
		  | Some elt_uri ->
		    let uri = Xml.get_text elt_uri in
		    Some (Rdf.URI uri)
		  | None ->
		    match Xml.find elt_binding (prefix ^ "literal") with
		    | Some elt_lit ->
		      let s = Xml.get_text elt_lit in
		      ( match Xml.find_attribute elt_lit "xml:lang" with
		      | Some lang -> Some (Rdf.PlainLiteral (s, lang))
		      | None ->
			( match Xml.find_attribute elt_lit "datatype" with
			| Some dt ->
			  (try Some (Rdf.Number (float_of_string s, s, dt))
			   with _ -> Some (Rdf.TypedLiteral (s, dt)))
			| None ->
			  (try Some (Rdf.Number (float_of_string s, s, ""))
			   with _ -> Some (Rdf.PlainLiteral (s, "")))))
		    | None ->
		      match Xml.find elt_binding (prefix ^ "bnode") with
		      | Some elt_bnode ->
			let id = Xml.get_text elt_bnode in
			( match uri_of_id id with
			| Some uri -> Some (Rdf.URI uri)
			| None -> Some (Rdf.Bnode id) )
		      | None -> None in
		binding.(i) <- term_opt)
	      elts_binding;
	    (j+1, binding::l))
	  (0,[]) elts_result in
      let bindings = List.rev rev_bindings in
      { dim; vars; length; bindings; }
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
		  | "bnode" ->
		    let id = to_string v in
		    ( match uri_of_id id with Some uri -> Rdf.URI uri | None -> Rdf.Bnode id )
		  | "typed-literal" ->
		    let odatatype = Unsafe.get ocell (string "datatype") in
		    let s = to_string v in
		    let dt = to_string (decodeURI (Unsafe.get odatatype (string "fullBytes"))) in
		    (try Rdf.Number (float_of_string s, s, dt)
		     with _ -> Rdf.TypedLiteral (s, dt))
		  | "plain-literal" ->
		    let olang = Unsafe.get ocell (string "xml:lang") in
		    Rdf.PlainLiteral (to_string v, to_string (Unsafe.get olang (string "fullBytes")))
		  | "literal" -> (* TODO: handle plain literals as numbers *)
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

let start_progress elt =  (* setting progress cursor on 'elt' *)
  elt##.style##.cursor := string "progress";
  elt##.style##.opacity := def (string "0.7")
let end_progress elt = (* removing progress cursor on 'elt' *)
  elt##.style##.cursor := string "default";
  elt##.style##.opacity := def (string "1")

class ajax_pool =
object
  val mutable reqs : xmlHttpRequest t list = []
  method add_req req = reqs <- req::reqs
  method remove_req req = reqs <- List.filter ((!=) req) reqs

  val mutable elts : Dom_html.element t list = []
  method add_elt elt = elts <- elt::elts
  method remove_elt elt = elts <- List.filter ((!=) elt) elts

  val mutable raised_alerts : string list = []
  method alert (msg : string) : unit =
    if not (List.mem msg raised_alerts)
    then begin
      raised_alerts <- msg::raised_alerts;
      alert msg
    end
    
  method abort_all =
    List.iter
      (fun req ->
	req##.onreadystatechange := (Js.wrap_callback (fun _ -> ()));
	req##abort)
      reqs;
    reqs <- [];
    List.iter end_progress elts;
    elts <- [];
    raised_alerts <- []
end

let config_proxy = new Config.boolean_input ~key:"proxy" ~input_selector:"#input-proxy" ~default:false ()
let config_proxy_url = new Config.string_input ~key:"proxy_url" ~input_selector:"#input-proxy-url" ~default:"http://servolis.irisa.fr/dbpedia/sparql" ()

let config_method_get = new Config.boolean_input ~key:"method_get" ~input_selector:"#input-method-get" ~default:false ()

let config_withCredentials = new Config.boolean_input ~key:"withCredentials" ~input_selector:"#input-withCredentials" ~default:false ()

let config_caching = new Config.boolean_input ~key:"caching" ~input_selector:"#input-caching" ~default:true ()

(* hooks for Sparklis extension *)
   
let hook_sparql (sparql : string) : string =
  Config.apply_hook_data
    Config.sparklis_extension##.hookSparql
    Sparql.js_sparql_map
    sparql

let hook_results (res : results) : results =
  Config.apply_hook_data
    Config.sparklis_extension##.hookResults
    js_results_map
    res

let cache =
object
  val ht : (string * string, string * results) Hashtbl.t = Hashtbl.create 101
  method replace endpoint sparql responseText_results =
    if config_caching#value
    then Hashtbl.replace ht (endpoint,sparql) responseText_results
  method lookup endpoint sparql =
    if config_caching#value
    then try Some (Hashtbl.find ht (endpoint,sparql)) with _ -> None
    else None
  method clear = Hashtbl.clear ht
end

let resolve_endpoint_sparql endpoint sparql =
  let real_endpoint, real_sparql = (* use of proxy, if defined *)
    if config_proxy#value
    then config_proxy_url#value, "SELECT * WHERE { SERVICE <" ^ endpoint ^ "> { " ^ sparql ^ " }}"
    else endpoint, sparql in
  (*firebug real_sparql;*)
  let prologue_sparql = Sparql.prologue#add_declarations_to_query real_sparql in
  real_endpoint, prologue_sparql

(* tentative query evaluation through cache *)
let cache_eval (endpoint : string) (sparql : string) : results option =
  let real_endpoint, prologue_sparql = resolve_endpoint_sparql endpoint sparql in
  match cache#lookup real_endpoint prologue_sparql with
  | Some (_, results) -> Some results
  | None -> None

(* query evaluation, by AJAX call if required *)
let rec ajax_in ?(tentative = false) ?(main_query = false) (elts : Dom_html.element t list) (pool : ajax_pool)
    (endpoint : string) (sparql : string)
    (k1 : string (* hooked sparql *) -> results -> unit) (* SUCCESS continuation *)
    (k0 : int -> unit) (* FAILURE continuation *) =
 if sparql = "" (* to allow for dummy queries, especially in query lists [ajax_list_in] *)
 then k1 "" empty_results
 else
  let real_endpoint, prologue_sparql = resolve_endpoint_sparql endpoint sparql in
  let prologue_sparql =
    if main_query then (
      Jsutils.yasgui#set_query prologue_sparql;
      hook_sparql prologue_sparql)
    else prologue_sparql in
  match cache#lookup real_endpoint prologue_sparql with
    | Some (response_text, results) ->
       let results =
         if main_query then (
           Jsutils.yasgui#set_response response_text;
           hook_results results)
         else results in
       k1 prologue_sparql results
    | None ->
      let encode_fields l =
	String.concat "&"
	  (List.map
	     (function
             | name,`String s -> ((Url.urlencode name) ^ "=" ^ (Url.urlencode (to_string s)))
             | name,`File s -> ((Url.urlencode name) ^ "=" ^ (Url.urlencode (to_string s##.name))))
	     l) in
      let fields : (string * Form.form_elt) list =
	[("query", `String (string prologue_sparql))] in
      let req = create () in
      pool#add_req req;
      List.iter pool#add_elt elts;
      if config_method_get#value
      then begin
	let query_url = real_endpoint ^ "?" ^ encode_fields fields in
	req##_open (Js.string "GET") (Js.string query_url) Js._true;
	Unsafe.set req (string "withCredentials") (bool config_withCredentials#value);
	req##setRequestHeader (Js.string "Accept") (Js.string "application/sparql-results+xml")
      end
      else begin
	req##_open (Js.string "POST") (Js.string real_endpoint) Js._true;
	Unsafe.set req (string "withCredentials") (bool config_withCredentials#value);
	req##setRequestHeader (Js.string "Content-type") (Js.string "application/x-www-form-urlencoded");
	req##setRequestHeader (Js.string "Accept") (Js.string "application/sparql-results+xml")
      end;
  (*
    let headers s =
    Opt.case
    (req##getResponseHeader (Js.bytestring s))
    (fun () -> None)
    (fun v -> Some (Js.to_string v)) in  
  *)
      let do_check_headers () = () in
      req##.onreadystatechange := Js.wrap_callback
	(fun _ ->
	  (match req##.readyState with
        (* IE doesn't have the same semantics for HEADERS_RECEIVED.
           so we wait til LOADING to check headers. See:
           http://msdn.microsoft.com/en-us/library/ms534361(v=vs.85).aspx *)
            | HEADERS_RECEIVED when not Dom_html.onIE -> do_check_headers ()
            | LOADING when Dom_html.onIE -> do_check_headers ()
            | DONE ->
	      List.iter end_progress elts;
	      pool#remove_req req;
	      List.iter pool#remove_elt elts;
	      do_check_headers ();
	      let code = req##.status in
	  (* Firebug.console##log(string ("HTTP code: " ^ string_of_int code)); *)
	  (* Firebug.console##log(req##statusText); *)
	      ( match code / 100 with
		| 2 ->
		  (* Firebug.console##log(req##responseText); *)
	      (*	let results = results_of_json xhr.content in *)
		  let results_opt =
                    match Js.Opt.to_option req##.responseXML with
                      | None -> None
                      | Some doc ->
			if (Js.some doc##.documentElement) == Js.null
			then None
			else (
			  match Js.Opt.to_option req##.responseText with
			  | None -> None
			  | Some txt ->
			     let response_text = to_string txt in
                             let results = results_of_xml doc in
			     Some (response_text, results)
			) in
		  ( match results_opt with
		    | None ->
		      Firebug.console##log (string "No XML content");
		      k0 code
		    | Some (response_text, results) ->
		       cache#replace real_endpoint prologue_sparql (response_text, results);
                       let results =
                         if main_query then (
                           Jsutils.yasgui#set_response response_text;
                           hook_results results)
                         else results in
		       k1 prologue_sparql results)
		| 0 ->
		  if config_proxy#value (* proxy was used *)
		  then begin
		    pool#alert "The proxy SPARQL endpoint is not responsive. Check that the URL is correct, and that the server is running.";
		    k0 code end
		  else
		    if config_proxy_url#value = "" (* no proxy allowed *)
		    then begin
		      pool#alert "The SPARQL endpoint is not responsive. Check that the URL is correct, and that the server is running. Otherwise, a frequent cause for this error is that the SPARQL endpoint does not allow cross-origin HTTP requests. You can either specify a proxy SPARQL endpoint in configuration panel, or contact and ask the endpoint administrator to use the Cross-Origin Resource Sharing mechanism (CORS).";
		      k0 code end
		    else begin
		      config_proxy#set_value true;
		      ajax_in elts pool endpoint sparql k1 k0
		    end
		| 4 ->
		  if not tentative then
		    pool#alert "The query was not understood by the SPARQL endpoint (see browser's console to see the SPARQL query). The reason is probably that some SPARQL features used by Sparklis are not supported by the endpoint. The minimum required SPARQL features are: UNION, DISTINCT, LIMIT. Other features depend on the current query.";
		  firebug "The following query was not understood";
		  firebug sparql;
		  k0 code
		| 5 ->
		  pool#alert "There was an error at the SPARQL endpoint during the evaluation of the query.";
		  k0 code
		| _ ->
		  pool#alert ("Error " ^ string_of_int code);
		  k0 code )
            | _ -> ()));
      List.iter start_progress elts;
      if config_method_get#value
      then req##send Js.null
      else req##send (Js.some (string (encode_fields fields)))

let rec ajax_list_in ?tentative elts pool endpoint sparql_list k1 k0 =
  match sparql_list with
    | [] -> k1 []
    | s::ls ->
      ajax_in ?tentative elts pool endpoint s
	(fun _ r -> (* real SPARQL is ignored *)
	  ajax_list_in ?tentative elts pool endpoint ls
	    (fun rs1 ->
	      let rs = r::rs1 in
	      k1 rs)
	    (fun code -> k0 code))
	(fun code -> k0 code)

(* configuration for default graphs *)

class config_graphs ~key ~input_selector ~(default_froms : unit -> Rdf.uri list) =
object (self)
  inherit Config.string_input ~key ~input_selector ~default:"" () as super

  method froms : Rdf.uri list =
    match super#value with
    | "" -> default_froms ()
    | uri -> [uri]
  method sparql_froms : string =
    String.concat "" (List.map (fun from -> "FROM <" ^ from ^ "> ") self#froms)
end

let config_default_graphs = new config_graphs ~key:"default_graph" ~input_selector:"#input-default-graph" ~default_froms:(fun () -> [])
let config_schema_graphs = new config_graphs ~key:"schema_graph" ~input_selector:"#input-schema-graph" ~default_froms:(fun () -> config_default_graphs#froms)

