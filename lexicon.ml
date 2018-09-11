(*
  Copyright 2013-2017 Sébastien Ferré, IRISA, Université de Rennes 1

  This file is part of Sparklis.
*)

(* URI lexicon definitions *)

class virtual ['a] lexicon = [Rdf.uri,'a] Cache.cache
class ['a] pure_lexicon get_label = [Rdf.uri,'a] Cache.pure_cache ~get:get_label
class ['a] tabled_lexicon default_label bind_labels = [Rdf.uri,'a] Cache.tabled_cache ~default:default_label ~bind:bind_labels

type property_syntagm = [ `Noun | `InvNoun | `TransVerb | `TransAdj ]
type arg_syntagm = [ `Noun | `TransAdj ]

type entity_lexicon = string lexicon
type class_lexicon = string lexicon
type property_lexicon = (property_syntagm * string) lexicon
type arg_lexicon = (arg_syntagm * string) lexicon


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

let syntagm_of_arg_name (name : string) : arg_syntagm * string =
  try
    if Common.has_prefix name "is " || List.exists (fun prep -> Common.has_suffix name (" " ^ prep)) prepositions then
      let name =
	if Common.has_prefix name "is "
	then String.sub name 3 (String.length name - 3)
	else name in
      `TransAdj, name
    else `Noun, name
  with _ -> Jsutils.firebug ("Lexicon.syntagm_of_arg_name: exception raised for:" ^ name); `Noun, name

let syntagm_name_of_uri_arg =
  fun uri ->
    let name = name_of_uri_concept uri in
    syntagm_of_arg_name name

let default_entity_lexicon = new pure_lexicon name_of_uri_entity
let default_class_lexicon = new pure_lexicon name_of_uri_concept
let default_property_lexicon = new pure_lexicon syntagm_name_of_uri_property
let default_arg_lexicon = new pure_lexicon syntagm_name_of_uri_arg


(* lexicon retrieving labels from a SPARQL endpoint *)

let wikidata_entity_of_predicate uri =
  let prefix_predicate = "http://www.wikidata.org/prop/" in
  if Common.has_prefix uri prefix_predicate
  then "http://www.wikidata.org/entity/" ^ name_of_uri uri
  else uri
  
(* from label property and optional language *)
let sparql_lexicon
    ~(kind : string)
    ~(default_label : Rdf.uri -> 'a)
    ~(endpoint : string) ~(froms: Rdf.uri list)
    ?(pref_properties : string list = [Rdf.rdfs_label])
    ?(pref_languages : string list = [])
    (map : string -> 'a) : 'a lexicon =
  (* avoiding empty lists for well-foundness *)
  let pref_properties = if pref_properties = [] then [Rdf.rdfs_label] else pref_properties in
  (* defining preference hash tables *)
  let make_ht_prefs (prefs : string list) : (string,int) Hashtbl.t =
    let ht = Hashtbl.create 10 in
    let prio = ref (List.length prefs) in
    prefs |> List.iter (fun x -> Hashtbl.add ht x !prio; decr prio);
    ht in
  let ht_pref_properties = make_ht_prefs pref_properties in
  let ht_pref_languages = make_ht_prefs pref_languages in
  (* *)
  let ajax_pool = new Sparql_endpoint.ajax_pool in
  let bind_labels l_uri k =
    Jsutils.firebug ("Retrieving " ^ kind ^ " labels for " ^ string_of_int (List.length l_uri) ^ " URIs");
    let l_uri =
      if Rdf.config_wikidata_mode#value
      then List.map wikidata_entity_of_predicate l_uri (* converting Wikidata predicates to entities *)
      else l_uri in
    let l_l_uri =
      if Sparql_endpoint.config_method_get#value (* to avoid lengthy queries *)
      then Common.bin_list 20 l_uri (* creating bins of 20 uris max *)
      else [l_uri] in
    let u, l, p = "u", "l", "p" in
    let l_sparql =
      let open Sparql in
      let v_u, v_l, v_p = Sparql.var u, Sparql.var l, Sparql.var p in
      List.map
	(fun l_uri ->
	  select ~projections:[(`Bare,u); (`Bare,l); (`Bare,p)] ~froms
	    (join
	       [ values v_u
		   (List.map (fun x_uri -> (uri x_uri :> term)) l_uri);
		 optional
		   (join
		      ( union
			  (List.map
			     (fun property ->
			      join [ triple (v_u :> term) (uri property :> pred) (v_l :> term);
				     bind (uri property :> expr) v_p ])
			     pref_properties);
			:: (if pref_languages = []
			    then [] (* no language constraint *)
			    else [filter
				    (expr_in (expr_coalesce [expr_func "lang" [(v_l :> expr)]; (string "" :> expr)])
					     (List.map
						(fun language -> (string language :> expr))
						pref_languages))] )) ) ]))
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
		  | "" -> label (* ^ " (statement)"*)
		  | "statement/" -> label ^ " (object)"
		  | "statement/value/" -> label ^ " (object value)"
		  | "qualifier/" -> label (*^ " (qualifier)"*)
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
	let ht_labels : (Rdf.uri, ((int * int) * string) option) Hashtbl.t = Hashtbl.create 31 in
	List.iter
	  (fun results ->
	   try
	     let i_u = List.assoc u results.Sparql_endpoint.vars in
	     let i_l = List.assoc l results.Sparql_endpoint.vars in
	     let i_p = List.assoc p results.Sparql_endpoint.vars in
	     List.iter
	       (fun binding ->
		match binding.(i_u), binding.(i_l), binding.(i_p) with
		| Some (Rdf.URI uri),
		  Some (Rdf.PlainLiteral _ | Rdf.TypedLiteral _ as label_term),
		  Some (Rdf.URI prop) ->
		   let label, lang =
		     match label_term with
		     | Rdf.PlainLiteral (label, lang) -> label, lang
		     | Rdf.TypedLiteral (label, _) -> label, ""
		     | _ -> assert false in
		   let prio =
		     (try Hashtbl.find ht_pref_properties prop with _ -> 0),
		     (try Hashtbl.find ht_pref_languages lang with _ -> 0) in
		   let is_better_label =
		     try
		       match Hashtbl.find ht_labels uri with
		       | Some (current_prio, _) -> prio > current_prio
		       | None -> true
		     with _ -> true in
		   if is_better_label then
		     Hashtbl.replace ht_labels uri (Some (prio,label))
		| Some (Rdf.URI uri), None, _ ->
		   if not (Hashtbl.mem ht_labels uri) then
		     Hashtbl.add ht_labels uri None
		| _ -> ())
	       results.Sparql_endpoint.bindings
	   with _ -> ())
	  l_results;
	let l_uri_info_opt =
	  Hashtbl.fold
	    (fun uri prio_label_opt lui ->
	     match prio_label_opt with
	     | Some (prio,label) -> add_uri_label uri (Some label) lui
	     | None -> add_uri_label uri None lui)
	    ht_labels [] in
	k l_uri_info_opt)
       (fun code ->
	ajax_pool#alert ("The " ^ kind ^ " labels could not be retrieved."
			 ^ " This may be because the endpoint does not support the VALUES or BIND operators.");
	k [])
  in
  new tabled_lexicon default_label bind_labels

let sparql_entity_lexicon ~endpoint ~froms ?pref_properties ?pref_languages () =
  sparql_lexicon ~kind:"entity" ~default_label:name_of_uri_entity ~endpoint ~froms ?pref_properties ?pref_languages (fun l -> l)
let sparql_class_lexicon ~endpoint ~froms ?pref_properties ?pref_languages () =
  sparql_lexicon ~kind:"class" ~default_label:name_of_uri_concept ~endpoint ~froms ?pref_properties ?pref_languages (fun l -> l)
let sparql_property_lexicon ~endpoint ~froms ?pref_properties ?pref_languages () =
  sparql_lexicon ~kind:"property" ~default_label:syntagm_name_of_uri_property ~endpoint ~froms ?pref_properties ?pref_languages syntagm_of_property_name
let sparql_arg_lexicon ~endpoint ~froms ?pref_properties ?pref_languages () =
  sparql_lexicon ~kind:"argument" ~default_label:syntagm_name_of_uri_arg ~endpoint ~froms ?pref_properties ?pref_languages syntagm_of_arg_name


(* configuration *)

open Js
open Jsutils

let regexp_sep = Regexp.regexp "[,;][ ]*"
       
class ['lexicon] config_input ~(key : string)
  ~(select_selector : string) ~(input_selector : string) ~(lang_input_selector : string)
  ~(config_graphs : Sparql_endpoint.config_graphs)
  ~(default_lexicon : 'lexicon) ~(custom_lexicon : endpoint:string -> froms:(Rdf.uri list) -> ?pref_properties:(Rdf.uri list) -> ?pref_languages:(string list) -> unit -> 'lexicon) () =
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
    let pref_properties =
      let l = Regexp.split regexp_sep current_property in
      List.filter ((<>) "") l in
    current_lexicon <-
      if pref_properties = []
      then default_lexicon
      else
	let pref_languages =
	  if current_lang = ""
	  then []
	  else Regexp.split regexp_sep current_lang in
	custom_lexicon ~endpoint
		       ~froms:config_graphs#froms
		       ~pref_properties
		       ~pref_languages
		       ()

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
    if current_property <> "" || current_lang <> ""
    then
      let args = if current_lang = "" then [] else [(key_lang, current_lang)] in
      if current_select = other
      then (key_property, current_property) :: args
      else (key_select, current_select) :: args
    else []
  method set_permalink args =
    let s = try List.assoc key_select args with _ -> "" in
    let s, p =
      if s = ""
      then (try other, List.assoc key_property args with _ -> "", "")
      else s, s in
    let l = try List.assoc key_lang args with _ -> "" in
    self#set_select_property_lang s p l

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
let config_arg_lexicon =
  new config_input
    ~key:"arg_lexicon"
    ~select_selector:"#config-label-arg-select"
    ~input_selector:"#config-label-arg-input"
    ~lang_input_selector:"#config-label-arg-input-lang"
    ~config_graphs:Sparql_endpoint.config_schema_graphs
    ~default_lexicon:default_arg_lexicon
    ~custom_lexicon:sparql_arg_lexicon
    ()

(* utilities for enqueuing and syncing *)

let enqueue_entity uri = config_entity_lexicon#value#enqueue uri
let enqueue_class uri = config_class_lexicon#value#enqueue uri
let enqueue_property uri = config_property_lexicon#value#enqueue uri
let enqueue_arg uri = config_arg_lexicon#value#enqueue uri

let sync_entities k =
  config_entity_lexicon#value#sync
    (fun () ->
     config_class_lexicon#value#sync k) (* 'class' for datatypes *)
let sync_concepts k =
  config_class_lexicon#value#sync
    (fun () ->
     config_property_lexicon#value#sync
       (fun () ->
	config_arg_lexicon#value#sync k))
    
let sync k =
  config_entity_lexicon#value#sync
    (fun () ->
     config_class_lexicon#value#sync
       (fun () ->
	config_property_lexicon#value#sync
	  (fun () ->
	   config_arg_lexicon#value#sync k)))
