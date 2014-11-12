
(* URI lexicon definitions *)

class virtual ['a] lexicon =
object
  method virtual info : Rdf.uri -> 'a
  method virtual enqueue : Rdf.uri -> unit
  method virtual sync : (unit -> unit) -> unit
end

type property_syntagm = [ `Noun | `InvNoun | `TransVerb | `TransAdj ]

type entity_lexicon = string lexicon
type class_lexicon = string lexicon
type property_lexicon = (property_syntagm * string) lexicon

(* URI lexicon templates *)

class ['a] pure_lexicon (get_label : Rdf.uri -> 'a) =
object
  inherit ['a] lexicon
  method info uri = get_label uri
  method enqueue uri = ()
  method sync k = k ()
end

module UriSet = Set.Make(String)

class ['a] tabled_lexicon (default_label : Rdf.uri -> 'a) (bind_labels : Rdf.uri list -> ((Rdf.uri * 'a option) list -> unit) -> unit) =
object (self)
  val h : (Rdf.uri,'a option) Hashtbl.t = Hashtbl.create 1001
  method info (uri : Rdf.uri) : 'a =
    try Common.unsome (Hashtbl.find h uri)
    with _ -> self#enqueue uri; default_label uri

  val mutable todo : UriSet.t = UriSet.empty
  method enqueue (uri : Rdf.uri) : unit =
    if not (UriSet.mem uri todo || Hashtbl.mem h uri)
    then todo <- UriSet.add uri todo
  method sync (k : unit -> unit) : unit =
    if UriSet.is_empty todo
    then k ()
    else begin
      let l_uri = UriSet.elements todo in
      Firebug.console##log(Js.string ("Synchronizing " ^ string_of_int (List.length l_uri) ^ " URI labels"));
      bind_labels l_uri
	(fun l_uri_info_opt ->
	  List.iter (fun (uri,info_opt) -> Hashtbl.add h uri info_opt) l_uri_info_opt;
	  todo <- UriSet.empty;
	  k ())
    end
end

(* default lexicon *)

let name_of_uri uri =
  let uri = Js.to_string (Js.decodeURI (Js.string uri)) in
  match Regexp.search (Regexp.regexp "[^/#]+$") uri 0 with
    | Some (_,res) ->
      ( match Regexp.matched_string res with "" -> uri | name -> name )
    | None -> uri

let name_of_uri_entity =
  let re_white = Regexp.regexp "_" in
  fun uri ->
    let name = name_of_uri uri in
    try Regexp.global_replace re_white name " "
    with _ -> name

let name_of_uri_concept =
  fun uri ->
    let name = name_of_uri uri in
    try Common.uncamel name
    with _ -> name

let prepositions = ["by"; "for"; "with"; "on"; "from"; "to"; "off"; "in"; "about"; "after"; "at"; "down"; "up"; "into"; "over"; "until"; "upon"; "within"; "without"]

let syntagm_of_property_name (name : string) : property_syntagm * string =
  if Common.has_suffix name " of" then `InvNoun, String.sub name 0 (String.length name - 3)
  else if Common.has_prefix name "has " then `Noun, String.sub name 4 (String.length name - 4)
  else if Common.has_suffix name "ed" || List.exists (fun prep -> Common.has_suffix name ("s " ^ prep)) prepositions then `TransVerb, name
  else if List.exists (fun prep -> Common.has_suffix name (" " ^ prep)) prepositions then `TransAdj, name
  else `Noun, name

let syntagm_name_of_uri_property =
  fun uri ->
    let name = name_of_uri_concept uri in
    syntagm_of_property_name name

let default_entity_lexicon = new pure_lexicon name_of_uri_entity
let default_class_lexicon = new pure_lexicon name_of_uri_concept
let default_property_lexicon = new pure_lexicon syntagm_name_of_uri_property


(* lexicon retrieving labels from a SPARQL endpoint *)

(* from label property and optional language *)
let sparql_lexicon
    ~(default_label : Rdf.uri -> 'a)
    ~(endpoint : string) ~(property : string) ?(language : string option)
    (map : string -> 'a) : 'a lexicon =
  let bind_labels l_uri k =
    let u, l = "u", "l" in
    let sparql =
      Sparql.select ~dimensions:[u;l]
	(Sparql.join
	   [ Sparql.union
	       (List.map (fun uri -> Sparql.bind (Sparql.uri uri) u) l_uri);
	     Sparql.optional
	       (Sparql.join
		  ( Sparql.triple (Rdf.Var u) (Rdf.URI property) (Rdf.Var l)
		    :: ( match language with
		      | None -> []
		      | Some lang -> [Sparql.filter (Sparql.expr_comp "=" (Sparql.expr_func "lang" (Sparql.var l)) (Sparql.string lang))] ))) ]) in
    (*Firebug.console##log(Js.string sparql);*)
    let pool = new Sparql_endpoint.ajax_pool in
    Sparql_endpoint.ajax_in [] pool endpoint sparql
      (fun results ->
	let l_uri_info_opt =
	  let i = List.assoc u results.Sparql_endpoint.vars in
	  let j = List.assoc l results.Sparql_endpoint.vars in
	  List.fold_left
	    (fun lui binding ->
	      match binding.(i), binding.(j) with
		| Some (Rdf.URI uri), Some (Rdf.PlainLiteral (label,_) | Rdf.TypedLiteral (label,_)) -> (uri, Some (map label))::lui
		| Some (Rdf.URI uri), None -> (uri, None)::lui
		| _ -> lui)
	    [] results.Sparql_endpoint.bindings in
	k l_uri_info_opt)
      (fun code -> k [])
  in
  new tabled_lexicon default_label bind_labels

let sparql_entity_lexicon ~endpoint ~property ?language () =
  sparql_lexicon ~default_label:name_of_uri_entity ~endpoint ~property ?language (fun l -> l)
let sparql_class_lexicon ~endpoint ~property ?language () =
  sparql_lexicon ~default_label:name_of_uri_concept ~endpoint ~property ?language (fun l -> l)
let sparql_property_lexicon ~endpoint ~property ?language () =
  sparql_lexicon ~default_label:syntagm_name_of_uri_property ~endpoint ~property ?language syntagm_of_property_name
