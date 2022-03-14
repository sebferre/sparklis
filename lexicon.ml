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

(* URI lexicon definitions *)

class virtual ['a] lexicon = [Rdf.uri,'a] Cache.cache
class ['a] pure_lexicon get_label = [Rdf.uri,'a] Cache.pure_cache ~get:get_label
class ['a] tabled_lexicon default_label bind_labels = [Rdf.uri,'a] Cache.tabled_cache ~default:default_label ~bind:bind_labels

type property_syntagm = [ `Noun | `InvNoun | `TransVerb | `TransAdj ]
type arg_syntagm = [ `Noun | `TransAdj ]

let js_property_syntagm_map =
  let open Jsutils in
  { spec = `Abstract;
    inject = (function
              | `Noun -> Inject.string "Noun"
              | `InvNoun -> Inject.string "InvNoun"
              | `TransVerb -> Inject.string "TransVerb"
              | `TransAdj -> Inject.string "TransAdj");
    extract = (fun js ->
      match Extract.as_string js with
      | "Noun" -> `Noun
      | "InvNoun" -> `InvNoun
      | "TransVerb" -> `TransVerb
      | "TransAdj" -> `TransAdj
      | _ -> assert false) }
let js_arg_syntagm_map =
  let open Jsutils in
  { spec = `Abstract;
    inject = (function
              | `Noun -> Inject.string "Noun"
              | `TransAdj -> Inject.string "TransAdj");
    extract = (fun js ->
      match Extract.as_string js with
      | "Noun" -> `Noun
      | "TransAdj" -> `TransAdj
      | _ -> assert false) }
                 
type entity_lexicon = string lexicon
type class_lexicon = string lexicon
type property_lexicon = (property_syntagm * string) lexicon
type arg_lexicon = (arg_syntagm * string) lexicon
type tooltip_lexicon = string lexicon

type concept_lexicon =
  { classes : class_lexicon;
    properties : property_lexicon;
    args : arg_lexicon }

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

let default_entity_lexicon s = new pure_lexicon name_of_uri_entity

let default_class_lexicon s = new pure_lexicon name_of_uri_concept
let default_property_lexicon s = new pure_lexicon syntagm_name_of_uri_property
let default_arg_lexicon s = new pure_lexicon syntagm_name_of_uri_arg

let default_concept_lexicon s =
  { classes = default_class_lexicon s;
    properties = default_property_lexicon s;
    args = default_arg_lexicon s }

let default_tooltip_lexicon = function
  | "void" -> new pure_lexicon (fun uri -> "")
  | _ -> new pure_lexicon (fun uri -> uri)

let default_open_links = function
  | "void" -> new pure_lexicon (fun uri -> "")
  | _ -> new pure_lexicon (fun uri -> uri)

       
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
		   (List.map (fun x_uri -> (term_uri x_uri :> term)) l_uri);
		 optional
		   (join
		      ( union
			  (List.map
			     (fun property ->
			      join [ triple (v_u :> term) (path_uri property :> pred) (v_l :> term);
				     bind (term_uri property :> expr) v_p ])
			     pref_properties)
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
		  Some (Rdf.PlainLiteral _ | Rdf.TypedLiteral _ | Rdf.URI _ as label_term),
		  Some (Rdf.URI prop) ->
		   let label, lang =
		     match label_term with
		     | Rdf.PlainLiteral (label, lang) -> label, lang
		     | Rdf.TypedLiteral (label, _) -> label, ""
                     | Rdf.URI uri -> uri, ""
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

let sparql_concept_lexicon ~endpoint ~froms ?pref_properties ?pref_languages () =
  { classes = sparql_class_lexicon ~endpoint ~froms ?pref_properties ?pref_languages ();
    properties = sparql_property_lexicon ~endpoint ~froms ?pref_properties ?pref_languages ();
    args = sparql_arg_lexicon ~endpoint ~froms ?pref_properties ?pref_languages () }

let sparql_tooltip_lexicon ~endpoint ~froms ?pref_properties ?pref_languages () =
  sparql_lexicon ~kind:"tooltip" ~default_label:(fun uri -> "") ~endpoint ~froms ?pref_properties ?pref_languages (fun tooltip -> tooltip)

let sparql_open_links ~endpoint ~froms ?pref_properties ?pref_languages () =
  sparql_lexicon ~kind:"open-link" ~default_label:(fun uri -> "") ~endpoint ~froms ?pref_properties ?pref_languages (fun link -> link) 

(* configuration *)

open Js
open Jsutils

let regexp_sep = Regexp.regexp "[,;][ ]*"
       
class ['lexicon] config_input ~(key : string)
  ~(select_selector : string) ~(input_selector : string) ~(lang_input_selector : string)
  ~(config_graphs : Sparql_endpoint.config_graphs)
  ~(default_lexicon : string -> 'lexicon) ~(custom_lexicon : endpoint:string -> froms:(Rdf.uri list) -> ?pref_properties:(Rdf.uri list) -> ?pref_languages:(string list) -> unit -> 'lexicon) () =
  let other = "other" in
  let key_select = key ^ "_select" in
  let key_property = key ^ "_property" in
  let key_lang = key ^ "_lang" in
  let void_lexicon = default_lexicon "void" in
  let uri_lexicon = default_lexicon "" in
object (self)
  inherit Config.input as super
  val mutable init_select = ""
  val mutable init_property = ""
  val mutable init_lang = ""
  val mutable current_froms = []
  val mutable current_select = ""
  val mutable current_property = ""
  val mutable current_lang = ""
  val mutable current_pref_properties = []
  val mutable current_pref_languages = []
  val mutable current_lexicon = uri_lexicon

  method private get_select_property_lang select input lang_input =
    let sel = to_string select##.value in
    let property = if sel = other then to_string input##.value else sel in
    let lang = to_string lang_input##.value in
    sel, property, lang

  method private set_select_property_lang s p l =
    if current_property <> p || current_lang <> l then begin
      jquery_select select_selector (fun select -> select##.value := string s);
      jquery_input input_selector (fun input -> input##.value := string (if s = other then p else ""));
      jquery_input lang_input_selector (fun input -> input##.value := string l);
      current_select <- s;
      current_property <- p;
      current_lang <- l;
      self#define_lexicon;
      self#changed
    end

  method private define_pref_lists : unit =
    current_pref_properties <-
      begin
	let l = Regexp.split regexp_sep current_property in
	List.filter ((<>) "") l
      end;
    current_pref_languages <-
      begin
	if current_lang = ""
	then []
	else Regexp.split regexp_sep current_lang
      end
							 
  method private define_lexicon : unit =
    self#define_pref_lists;
    current_lexicon <-
      if current_select = "" then uri_lexicon
      else if current_select = "void" then void_lexicon
      else custom_lexicon ~endpoint
			  ~froms:config_graphs#froms
			  ~pref_properties:current_pref_properties
			  ~pref_languages:current_pref_languages
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

  method properties_langs : string list * string list = current_pref_properties, current_pref_languages
  method value : 'lexicon = current_lexicon

  method init =
    jquery_select select_selector (fun select ->
      jquery_input input_selector (fun input ->
	jquery_input lang_input_selector (fun lang_input ->
	  (* default values from HTML *)
	  let s, p, l = self#get_select_property_lang select input lang_input in
	  if s <> other then input##.style##.display := string "none";
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
	      if to_string select##.value <> other
	      then begin
		input##.style##.display := string "none";
		self#change_lexicon select input lang_input end
	      else
		input##.style##.display := string "inline")
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
let config_concept_lexicon =
  new config_input
    ~key:"concept_lexicons"
    ~select_selector:"#config-label-concept-select"
    ~input_selector:"#config-label-concept-input"
    ~lang_input_selector:"#config-label-concept-input-lang"
    ~config_graphs:Sparql_endpoint.config_schema_graphs
    ~default_lexicon:default_concept_lexicon
    ~custom_lexicon:sparql_concept_lexicon
    ()

let config_entity_tooltips =
  new config_input
    ~key:"entity_tooltips"
    ~select_selector:"#config-entity-tooltips-select"
    ~input_selector:"#config-entity-tooltips-input"
    ~lang_input_selector:"#config-entity-tooltips-input-lang"
    ~config_graphs:Sparql_endpoint.config_default_graphs
    ~default_lexicon:default_tooltip_lexicon
    ~custom_lexicon:sparql_tooltip_lexicon
    ()
let config_concept_tooltips =
  new config_input
    ~key:"concept_tooltips"
    ~select_selector:"#config-concept-tooltips-select"
    ~input_selector:"#config-concept-tooltips-input"
    ~lang_input_selector:"#config-concept-tooltips-input-lang"
    ~config_graphs:Sparql_endpoint.config_schema_graphs
    ~default_lexicon:default_tooltip_lexicon
    ~custom_lexicon:sparql_tooltip_lexicon
    ()

let config_open_links =
  new config_input
    ~key:"open_links"
    ~select_selector:"#config-open-links-select"
    ~input_selector:"#config-open-links-input"
    ~lang_input_selector:"#config-open-links-input-lang" (* TODO: not needed *)
    ~config_graphs:Sparql_endpoint.config_default_graphs
    ~default_lexicon:default_open_links
    ~custom_lexicon:sparql_open_links
    ()

(* utilities for enqueuing, syncing, and accessing *)

let enqueue_entity uri =
  config_entity_lexicon#value#enqueue uri;
  config_entity_tooltips#value#enqueue uri;
  config_open_links#value#enqueue uri
let enqueue_class uri = config_concept_lexicon#value.classes#enqueue uri; config_concept_tooltips#value#enqueue uri
let enqueue_property uri = config_concept_lexicon#value.properties#enqueue uri; config_concept_tooltips#value#enqueue uri
let enqueue_arg uri = config_concept_lexicon#value.args#enqueue uri; config_concept_tooltips#value#enqueue uri

let ( let> ) sync k = sync k
                      
let sync_entities k =
  let> () = config_entity_lexicon#value#sync in
  let> () = config_concept_lexicon#value.classes#sync (* 'class' for datatypes *) in
  let> () = config_entity_tooltips#value#sync in
  let> () = config_open_links#value#sync in
  k ()
  
let sync_concepts k =
  let> () = config_concept_lexicon#value.classes#sync in
  let> () = config_concept_lexicon#value.properties#sync in
  let> () = config_concept_lexicon#value.args#sync in
  let> () = config_concept_tooltips#value#sync in
  k ()
    
let sync k =
  let> () = config_entity_lexicon#value#sync in
  let> () = config_concept_lexicon#value.classes#sync in
  let> () = config_concept_lexicon#value.properties#sync in
  let> () = config_concept_lexicon#value.args#sync in
  let> () = config_entity_tooltips#value#sync in
  let> () = config_concept_tooltips#value#sync in
  let> () = config_open_links#value#sync in
  k ()

let entity_label uri = config_entity_lexicon#value#info uri
let class_label uri = config_concept_lexicon#value.classes#info uri
let property_label uri = config_concept_lexicon#value.properties#info uri
let arg_label uri = config_concept_lexicon#value.args#info uri
let entity_tooltip uri = config_entity_tooltips#value#info uri
let concept_tooltip uri = config_concept_tooltips#value#info uri
let entity_open_link uri = config_open_links#value#info uri

