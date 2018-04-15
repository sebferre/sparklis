(*
  Copyright 2013-2017 Sébastien Ferré, IRISA, Université de Rennes 1

  This file is part of Sparklis.
*)

(* URI lexicon definitions *)

class virtual ['a] lexicon = [Rdf.uri,'a] Cache.cache
class ['a] pure_lexicon get_label = [Rdf.uri,'a] Cache.pure_cache ~get:get_label
class ['a] tabled_lexicon default_label bind_labels = [Rdf.uri,'a] Cache.tabled_cache ~default:default_label ~bind:bind_labels

type property_syntagm = [ `Noun | `InvNoun | `TransVerb | `TransAdj ]

type entity_lexicon = string lexicon
type class_lexicon = string lexicon
type property_lexicon = (property_syntagm * string) lexicon


(* default lexicon *)

let re_white = Regexp.regexp "_"

let name_of_uri uri =
  let uri = Js.to_string (Js.decodeURI (Js.string uri)) in
  match Regexp.search (Regexp.regexp "[^/#]+$") uri 0 with
    | Some (_,res) ->
      ( match Regexp.matched_string res with "" -> uri | name -> name )
    | None -> uri

let name_of_uri_entity =
  fun uri ->
    let name = name_of_uri uri in
    try Regexp.global_replace re_white name " "
    with _ -> name

let name_of_uri_concept =
  fun uri ->
  let name = name_of_uri uri in
  let name =
    try Common.uncamel name
    with _ -> Jsutils.firebug "Common.uncamel failed"; name in
  try Regexp.global_replace re_white name " "
  with _ -> name

let prepositions = ["by"; "for"; "with"; "on"; "from"; "to"; "off"; "in"; "about"; "after"; "at"; "down"; "up"; "into"; "over"; "until"; "upon"; "within"; "without"]

let syntagm_of_property_name (name : string) : property_syntagm * string =
  try
    if Common.has_suffix name " of" then
      let name = String.sub name 0 (String.length name - 3) in
      let name =
	if Common.has_prefix name "is "
	then String.sub name 3 (String.length name - 3)
	else name in
      `InvNoun, name
    else if Common.has_prefix name "has " || Common.has_prefix name "with " then
      `Noun, String.sub name 4 (String.length name - 4)
    else if Common.has_suffix name "ed" || List.exists (fun prep -> Common.has_suffix name ("s " ^ prep)) prepositions then
      `TransVerb, name
    else if Common.has_prefix name "is " || List.exists (fun prep -> Common.has_suffix name (" " ^ prep)) prepositions then
      let name =
	if Common.has_prefix name "is "
	then String.sub name 3 (String.length name - 3)
	else name in
      `TransAdj, name
    else `Noun, name
  with _ -> Jsutils.firebug ("Lexicon.syntagm_of_property_name: exception raised for:" ^ name); `Noun, name

let syntagm_name_of_uri_property =
  fun uri ->
    let name = name_of_uri_concept uri in
    syntagm_of_property_name name

let default_entity_lexicon = new pure_lexicon name_of_uri_entity
let default_class_lexicon = new pure_lexicon name_of_uri_concept
let default_property_lexicon = new pure_lexicon syntagm_name_of_uri_property


(* lexicon retrieving labels from a SPARQL endpoint *)

let wikidata_entity_of_predicate uri =
  let prefix_predicate = "http://www.wikidata.org/prop/" in
  if Common.has_prefix uri prefix_predicate
  then 
    (*let prefix_length = String.length prefix_predicate in
    let suffix_predicate = String.sub uri prefix_length (String.length uri - prefix_length) in
    let l_middle_predicate =
      ["direct/"; "novalue/";
       "statement/"; "statement/value/";
       "qualifier/"; "qualifier/value/";
       "reference/"; "reference/value/"] in
    let middle_predicate = try List.find (fun middle -> Common.has_prefix suffix_predicate middle) l_middle_predicate with _ -> "" in
    let middle_length = String.length middle_predicate in
      let property_id = String.sub suffix_predicate middle_length (String.length suffix_predicate middle_length) in*)
    "http://www.wikidata.org/entity/" ^ name_of_uri uri
  else uri
  
(* from label property and optional language *)
let sparql_lexicon
    ~(default_label : Rdf.uri -> 'a)
    ~(endpoint : string) ~(froms: Rdf.uri list) ~(property : string) ?(language : string option)
    (map : string -> 'a) : 'a lexicon =
  let ajax_pool = new Sparql_endpoint.ajax_pool in
  let bind_labels l_uri k =
    Jsutils.firebug ("Retrieving labels for " ^ string_of_int (List.length l_uri) ^ " URIs");
    let l_uri =
      if endpoint = Sparql_endpoint.wikidata_endpoint
      then List.map wikidata_entity_of_predicate l_uri (* converting Wikidata predicates to entities *)
      else l_uri in
    let l_l_uri =
      if Sparql_endpoint.config_method_get#value (* to avoid lengthy queries *)
      then Common.bin_list 20 l_uri (* creating bins of 20 uris max *)
      else [l_uri] in
    let u, l = "u", "l" in
    let l_sparql =
      let open Sparql in
      let v_u, v_l = Sparql.var u, Sparql.var l in
      List.map
	(fun l_uri ->
	  select ~projections:[(`Bare,u); (`Bare,l)] ~froms
	    (join
	       [ values v_u
		   (List.map (fun x_uri -> (uri x_uri :> term)) l_uri);
		 optional
		   (join
		      ( triple (v_u :> term) (uri property :> pred) (v_l :> term)
			:: ( match language with
			| None -> []
			| Some lang -> [filter (expr_comp "=" (expr_func "lang" [(v_l :> expr)]) (string lang :> expr))] ))) ]))
	l_l_uri in
    let add_uri_label uri label_opt lui =
      if Common.has_prefix uri "http://www.wikidata.org/entity/P"
      then
	let p_id = String.sub uri 31 (String.length uri - 31) in
	List.fold_left
	  (fun lui middle ->
	    let uri_pred = "http://www.wikidata.org/prop/" ^ middle ^ p_id in
	    let info_opt =
	      match label_opt with
	      | None -> None
	      | Some label ->
		let label_pred =
		  match middle with
		  | "direct/" -> label
		  | "novalue/" -> label ^ " (novalue)"
		  | "" -> label ^ " (statement)"
		  | "statement/" -> label ^ " (object)"
		  | "statement/value/" -> label ^ " (object value)"
		  | "qualifier/" -> label ^ " (qualifier)"
		  | "qualifier/value/" -> label ^ " (qualifier value)"
		  | "reference/" -> label ^ " (reference)"
		  | "reference/value/" -> label ^ " (reference value)"
		  | _ -> label in
		Some (map label_pred) in
	    (uri_pred,info_opt)::lui)
	  lui
	  ["direct/"; "novalue/"; "";
	   "statement/"; "statement/value/";
	   "qualifier/"; "qualifier/value/";
	   "reference/"; "reference/value/"]
      else
	let info_opt = match label_opt with None -> None | Some l -> Some (map l) in
	(uri,info_opt)::lui
    in
    Sparql_endpoint.ajax_list_in [] ajax_pool endpoint (l_sparql :> string list)
      (fun l_results ->
	let l_uri_info_opt =
	  List.fold_left
	    (fun lui results ->
	      let i = List.assoc u results.Sparql_endpoint.vars in
	      let j = List.assoc l results.Sparql_endpoint.vars in
	      List.fold_left
		(fun lui binding ->
		  match binding.(i), binding.(j) with
		  | Some (Rdf.URI uri), Some (Rdf.PlainLiteral (label,_) | Rdf.TypedLiteral (label,_)) -> add_uri_label uri (Some label) lui
		  | Some (Rdf.URI uri), None -> add_uri_label uri None lui
		  | _ -> lui)
		lui results.Sparql_endpoint.bindings)
	    [] l_results in
	k l_uri_info_opt)
      (fun code ->
	ajax_pool#alert ("The labels could not be retrieved for property <"
			 ^ property ^ (match language with None -> ">." | Some lang -> "> and for language tag @" ^ lang ^ ".")
			 ^ " This may be because the endpoint does not support the BIND operator.");
	k [])
  in
(*
  let bind_labels_wikidata l_uri k =
    let l_l_uri = Common.bin_list 20 l_uri in
    let l_l_var_uri_sparql =
      List.map
	(fun l_uri ->
	  let _, l_var_uri = List.fold_left (fun (i,l) uri -> i+1, ("l" ^ string_of_int i, uri)::l) (1,[]) l_uri in
	  let open Sparql in
	  let sparql =
	    select ~projections:(List.map (fun (v,u) -> (`Bare,v)) l_var_uri)
	      (service (qname "wikibase:label")
		 (join (triple (qname "bd:serviceParam") (qname "wikibase:language")
			  (string (match language with None -> "en" | Some lang -> lang))
			:: List.map (fun (v,u) -> triple (uri u) (uri property) (var v :> term)) l_var_uri))) in
	  Jsutils.firebug (sparql :> string);
	  (l_var_uri, sparql))
	l_l_uri in
    let l_l_var_uri, l_sparql = List.split l_l_var_uri_sparql in
    Sparql_endpoint.ajax_list_in [] ajax_pool endpoint (l_sparql :> string list)
      (fun l_results ->
	let l_uri_info_opt =
	  List.fold_left2
	    (fun l_uri_info_opt l_var_uri results ->
	      let l_uri_pos_opt =
		List.fold_left
		  (fun res (v,u) ->
		    try (u, Some (List.assoc v results.Sparql_endpoint.vars))::res
		    with _ -> (u,None)::res)
		  [] l_var_uri in
	      match results.Sparql_endpoint.bindings with
	      | [] -> []
	      | binding::_ -> (* should be a single binding *)
		List.fold_left
		  (fun l_uri_info_opt -> function
		  | (u, None) -> (u, None)::l_uri_info_opt
		  | (u, Some pos) ->
		    ( match binding.(pos) with
		    | Some (Rdf.PlainLiteral (label,_) | Rdf.TypedLiteral (label,_)) -> (u, Some (map label))::l_uri_info_opt
		    | _ -> (u, None)::l_uri_info_opt ))
		  l_uri_info_opt l_uri_pos_opt)
	    [] l_l_var_uri l_results in
	k l_uri_info_opt)
      (fun code ->
	ajax_pool#alert ("The Wikidata labels could not be retrieved for property <"
			 ^ property ^ (match language with None -> ">." | Some lang -> "> and for language tag @" ^ lang ^ "."));
	k [])
  in
*)
  new tabled_lexicon default_label bind_labels

let sparql_entity_lexicon ~endpoint ~froms ~property ?language () =
  sparql_lexicon ~default_label:name_of_uri_entity ~endpoint ~froms ~property ?language (fun l -> l)
let sparql_class_lexicon ~endpoint ~froms ~property ?language () =
  sparql_lexicon ~default_label:name_of_uri_concept ~endpoint ~froms ~property ?language (fun l -> l)
let sparql_property_lexicon ~endpoint ~froms ~property ?language () =
  sparql_lexicon ~default_label:syntagm_name_of_uri_property ~endpoint ~froms ~property ?language syntagm_of_property_name


(* configuration *)

open Js
open Jsutils

class ['lexicon] config_input ~(key : string)
  ~(select_selector : string) ~(input_selector : string) ~(lang_input_selector : string)
  ~(config_graphs : Sparql_endpoint.config_graphs)
  ~(default_lexicon : 'lexicon) ~(custom_lexicon : endpoint:string -> froms:(Rdf.uri list) -> property:Rdf.uri -> ?language:string -> unit -> 'lexicon) () =
  let other = "other" in
  let key_select = key ^ "_select" in
  let key_property = key ^ "_property" in
  let key_lang = key ^ "_lang" in
object (self)
  inherit Config.input as super
  val mutable init_select = ""
  val mutable init_property = ""
  val mutable init_lang = ""
  val mutable current_froms = []
  val mutable current_select = ""
  val mutable current_property = ""
  val mutable current_lang = ""
  val mutable current_lexicon = default_lexicon

  method private get_select_property_lang select input lang_input =
    let sel = to_string select##value in
    let property = if sel = other then to_string (input##value) else sel in
    let lang = to_string (lang_input##value) in
    sel, property, lang

  method private set_select_property_lang s p l =
    if current_property <> p || current_lang <> l then begin
      jquery_select select_selector (fun select -> Jsutils.selectpicker_set_value select s);
      jquery_input input_selector (fun input -> input##value <- string (if s = other then p else ""));
      jquery_input lang_input_selector (fun input -> input##value <- string l);
      current_select <- s;
      current_property <- p;
      current_lang <- l;
      self#define_lexicon;
      self#changed
    end

  method private define_lexicon : unit =
    current_lexicon <-
      if current_property = ""
      then default_lexicon
      else custom_lexicon ~endpoint
	~froms:config_graphs#froms
	~property:current_property
	?language:(if current_lang = "" then None else Some current_lang) ()

  method private change_lexicon select input lang_input : unit =
    let fr = config_graphs#froms in
    let s, p, l = self#get_select_property_lang select input lang_input in
    if fr <> current_froms || p <> current_property || l <> current_lang then begin
      current_froms <- fr;
      current_select <- s;
      current_property <- p;
      current_lang <- l;
      self#define_lexicon;
      self#changed
    end

  method set_endpoint url =
    super#set_endpoint url;
    self#define_lexicon

  method get_permalink =
    if current_property <> init_property || current_lang <> init_lang
    then
      let args = if current_lang = "" then [] else [(key_lang, current_lang)] in
      if current_select = other
      then (key_property, current_property) :: args
      else (key_select, current_select) :: args
    else []
  method set_permalink args =
    try
      let s = try List.assoc key_select args with _ -> other in
      let p = if s = other then List.assoc key_property args else s in
      let l = try List.assoc key_lang args with _ -> "" in
      self#set_select_property_lang s p l
    with _ -> ()

  method property_lang : string * string = current_property, current_lang
  method value : 'lexicon = current_lexicon

  method init =
    jquery_select select_selector (fun select ->
      jquery_input input_selector (fun input ->
	jquery_input lang_input_selector (fun lang_input ->
	  (* default values from HTML *)
	  let s, p, l = self#get_select_property_lang select input lang_input in
	  if s <> other then input##style##display <- string "none";
	  init_select <- s;
	  init_property <- p;
	  init_lang <- l;
	  (* definition of current values *)
	  current_froms <- config_graphs#froms;
	  current_select <- init_select;
	  current_property <- init_property;
	  current_lang <- init_lang;
	  self#define_lexicon;
	  (* callbacks on changes/inputs *)
	  config_graphs#on_change (fun () -> self#change_lexicon select input lang_input);
	  onchange
	    (fun _ ev ->
	      if to_string select##value <> other
	      then begin
		input##style##display <- string "none";
		self#change_lexicon select input lang_input end
	      else
		input##style##display <- string "inline")
	    select;
	  oninput (fun _ ev -> self#change_lexicon select input lang_input) input;
	  oninput (fun _ ev -> self#change_lexicon select input lang_input) lang_input)))
  method reset = self#set_select_property_lang init_select init_property init_lang
end

let config_entity_lexicon =
  new config_input
    ~key:"entity_lexicon"
    ~select_selector:"#config-label-entity-select"
    ~input_selector:"#config-label-entity-input"
    ~lang_input_selector:"#config-label-entity-input-lang"
    ~config_graphs:Sparql_endpoint.config_default_graphs
    ~default_lexicon:default_entity_lexicon
    ~custom_lexicon:sparql_entity_lexicon
    ()
let config_class_lexicon =
  new config_input
    ~key:"class_lexicon"
    ~select_selector:"#config-label-class-select"
    ~input_selector:"#config-label-class-input"
    ~lang_input_selector:"#config-label-class-input-lang"
    ~config_graphs:Sparql_endpoint.config_schema_graphs
    ~default_lexicon:default_class_lexicon
    ~custom_lexicon:sparql_class_lexicon
    ()
let config_property_lexicon =
  new config_input
    ~key:"property_lexicon"
    ~select_selector:"#config-label-property-select"
    ~input_selector:"#config-label-property-input"
    ~lang_input_selector:"#config-label-property-input-lang"
    ~config_graphs:Sparql_endpoint.config_schema_graphs
    ~default_lexicon:default_property_lexicon
    ~custom_lexicon:sparql_property_lexicon
    ()
