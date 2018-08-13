(*
  Copyright 2013-2017 Sébastien Ferré, IRISA, Université de Rennes 1

  This file is part of Sparklis.
*)

(* ontological relations *)
class virtual ['a] relation = [Rdf.uri, 'a list] Cache.cache
class ['a] pure_relation get_images = [Rdf.uri, 'a list] Cache.pure_cache ~get:get_images
class ['a] tabled_relation default_images bind_images = [Rdf.uri, 'a list] Cache.tabled_cache ~default:default_images ~bind:bind_images

(* default void hierarchy *)
let no_relation = new pure_relation (fun uri -> [])


(* SPARQL-based relation, retrieving relation from endpoint *)
let sparql_relation
      ~(name : string)
      ~(endpoint : string)
      ~(froms : Rdf.uri list)
      ~(make_pattern : Sparql.var -> Sparql.var -> Sparql.pattern)
      ~(image_opt_of_term : Rdf.term -> 'a option)
    : 'a relation =
  let ajax_pool = new Sparql_endpoint.ajax_pool in
  let bind_images l_uri k =
    Jsutils.firebug ("Retrieving image URIs in " ^ name ^ ", for " ^ string_of_int (List.length l_uri) ^ " URIs");
    let l_l_uri =
      if Sparql_endpoint.config_method_get#value (* to avoid lengthy queries *)
      then Common.bin_list 50 l_uri (* creating bins of 50 uris max *)
      else [l_uri] in
    let source, image = "uri", "image" in (* SPARQL vars *)
    let l_sparql =
      let open Sparql in
      let v_source, v_image = var source, var image in
      List.map
	(fun l_uri ->
	  select ~projections:[(`Bare,source); (`Bare,image)] ~froms
	    (join
	       [ values v_source
		   (List.map (fun x_uri -> (uri x_uri :> term)) l_uri);
		 optional
		   (make_pattern v_source v_image) ]))
	l_l_uri in
    let add_source_image ht_images uri_source image =
      let images_ref =
	try Hashtbl.find ht_images uri_source
	with Not_found ->
	  let imgs_ref = ref [] in
	  Hashtbl.add ht_images uri_source imgs_ref;
	  imgs_ref in
      if not (List.mem image !images_ref)
      then images_ref := image :: !images_ref
      else ()
    in
    Sparql_endpoint.ajax_list_in [] ajax_pool endpoint (l_sparql :> string list)
      (fun l_results ->
	let ht_images : (Rdf.uri, 'a list ref) Hashtbl.t = Hashtbl.create 101 in
	List.iter
	  (fun results ->
	   try
	     let i = List.assoc source results.Sparql_endpoint.vars in
	     let j_opt = try Some (List.assoc image results.Sparql_endpoint.vars) with _ -> None in
	     (* some endpoints do not include ?image when no binding at all (in OPTIONAL) *)
	     List.iter
	       (fun binding ->
		match binding.(i), (match j_opt with None -> None | Some j -> match binding.(j) with None -> None | Some t -> image_opt_of_term t) with
		(*		| Some (Rdf.URI uri_source), Some (Rdf.URI uri_image) -> add_source_image ht_images uri_source uri_image*)
		| Some (Rdf.URI uri_source), Some image -> add_source_image ht_images uri_source image
		| Some (Rdf.URI uri_source), None -> Hashtbl.add ht_images uri_source (ref []) (* recording absence of parents *)
		| _ -> ())
	       results.Sparql_endpoint.bindings
	   with _ -> Jsutils.firebug ("Missing variable(s) in SPARQL results: ?uri"))
	  l_results;
	let l_uri_info_opt =
	  Hashtbl.fold
	    (fun uri_source images_ref res -> (uri_source, Some !images_ref)::res)
	    ht_images [] in
	k l_uri_info_opt)
      (fun code ->
	ajax_pool#alert ("The image URIs could not be retrieved in " ^ name ^ ".");
	k [])
  in
  new tabled_relation (fun uri -> []) bind_images

(* SPARQL-based relation, retrieving data from endpoint *)
let sparql_relation_property ~endpoint ~froms ~(property : Rdf.uri) ~(inverse : bool) ~(image_opt_of_term : Rdf.term -> 'a option) : 'a relation =
  let make_pattern v_source v_image : Sparql.pattern =
    let open Sparql in
    let uri_property = (uri property :> pred) in
    if inverse
    then triple (v_image :> term) uri_property (v_source :> term)
    else triple (v_source :> term) uri_property (v_image :> term)
  in
  sparql_relation
    ~name:("property <" ^ property ^ ">")
    ~endpoint
    ~froms
    ~make_pattern
    ~image_opt_of_term

(* SPARQL-based hierarchy, retrieving hierarchical relation from endpoint *)    
let sparql_relation_hierarchy ~endpoint ~froms ~(property : Rdf.uri) ~(inverse : bool) : Rdf.uri relation =
  let make_pattern v_child v_parent : Sparql.pattern =
    let open Sparql in
    let has_parent s o =
      let uri_property = (uri property :> pred) in
      if inverse
      then triple o uri_property s
      else triple s uri_property o
    in
    let v_middle = var "middle" in
    join
      [ has_parent (v_child :> term) (v_parent :> term);
	filter (expr_comp "!=" (v_child :> expr) (v_parent :> expr));
	filter (not_exists (has_parent (v_parent :> term) (v_child :> term)));
	filter (not_exists (join
			      [ has_parent (v_child :> term) (v_middle :> term);
				has_parent (v_middle :> term) (v_parent :> term);
				filter (log_and [ expr_comp "!=" (v_middle :> expr) (v_child :> expr);
						  expr_comp "!=" (v_middle :> expr) (v_parent :> expr) ])
			      ]))
      ]
  in
  sparql_relation
    ~name:("property <" ^ property ^ ">")
    ~endpoint
    ~froms
    ~make_pattern
    ~image_opt_of_term:(function Rdf.URI uri -> Some uri | _ -> None)
    
(* pool of hierarchies for an endpoint as a configuration *)

let sparql_relations =
  object (self)
    inherit Config.input as super

    method get_permalink = []
    method set_permalink _ = ()

    val ht_property_number : (Rdf.uri, float relation) Hashtbl.t = Hashtbl.create 7
    val ht_property_uri : (Rdf.uri * bool (* inverse *), Rdf.uri relation) Hashtbl.t = Hashtbl.create 7
    val ht_hierarchy : (Rdf.uri * bool (* inverse *), Rdf.uri relation) Hashtbl.t = Hashtbl.create 7
											     
    method init = ()
      
    method set_endpoint url =
      super#set_endpoint url;
      Hashtbl.clear ht_property_number;
      Hashtbl.clear ht_property_uri;
      Hashtbl.clear ht_hierarchy

    method reset = ()

    method get_property_number ~(froms : Rdf.uri list) ~(property : Rdf.uri) : float relation =
      try Hashtbl.find ht_property_number property
      with Not_found ->
	let rel = sparql_relation_property
		    ~endpoint ~froms ~property ~inverse:false
		    ~image_opt_of_term:(function Rdf.Number (f,_,_) -> Some f | _ -> None) in
	Hashtbl.add ht_property_number property rel;
	rel

    method get_property_uri ~(froms : Rdf.uri list) ~(property : Rdf.uri) ~(inverse : bool) : Rdf.uri relation =
      try Hashtbl.find ht_property_uri (property,inverse)
      with Not_found ->
	let rel = sparql_relation_property
		    ~endpoint ~froms ~property ~inverse
		    ~image_opt_of_term:(function Rdf.URI uri -> Some uri | _ -> None) in
	Hashtbl.add ht_property_uri (property,inverse) rel;
	rel

    method get_hierarchy ~(froms : Rdf.uri list) ~(property : Rdf.uri) ~(inverse : bool) : Rdf.uri relation =
      try Hashtbl.find ht_hierarchy (property,inverse)
      with Not_found ->
	let rel = sparql_relation_hierarchy ~endpoint ~froms ~property ~inverse in
	Hashtbl.add ht_hierarchy (property,inverse) rel;
	rel
	  
    method subclassof ~froms = self#get_hierarchy ~froms ~property:Rdf.rdfs_subClassOf ~inverse:false
    method subpropertyof ~froms = self#get_hierarchy ~froms ~property:Rdf.rdfs_subPropertyOf ~inverse:false
    method domain ~froms = self#get_property_uri ~froms ~property:Rdf.rdfs_domain ~inverse:false
    method range ~froms = self#get_property_uri ~froms ~property:Rdf.rdfs_range ~inverse:false
    method inheritsthrough ~froms = self#get_property_uri ~froms ~property:Rdf.rdfs_inheritsThrough ~inverse:false

    method position ~froms = self#get_property_number ~froms ~property:Rdf.schema_position
  end
							     
(* configuration *)

open Js
open Jsutils

class ['relation] config_relation ~(key : string)
  ~(input_selector : string)
  ~(config_graphs : Sparql_endpoint.config_graphs)
  ~(default_relation : 'relation) ~(custom_relation : froms:(Rdf.uri list) -> 'relation) () =
  let default = false in
object (self)
  inherit Config.input as super
  val mutable init_on = default
  val mutable current_froms = []
  val mutable current_on = default
  val mutable current_relation = default_relation

  method private get_on input =
    to_bool input##checked
  method private set_on on =
    if current_on <> on then begin
      jquery_input input_selector (fun input -> input##checked <- bool on);
      current_on <- on;
      self#define_relation;
      self#changed
    end

  method private define_relation : unit =
    current_relation <-
      if not current_on
      then begin
	Jsutils.firebug "Using default relation";
	default_relation end
      else begin
	Jsutils.firebug "Using custom relation";
	custom_relation ~froms:config_graphs#froms
      end

  method private change_relation input : unit =
    let fr = config_graphs#froms in
    let on = self#get_on input in
    if fr <> current_froms || on <> current_on then begin
      current_on <- on;
      self#define_relation;
      self#changed
    end
    
  method set_endpoint url =
    super#set_endpoint url;
    self#define_relation

  method get_permalink =
    if current_on <> default
    then [(key, string_of_bool current_on)]
    else []
  method set_permalink args =
    self#set_on (try bool_of_string (List.assoc key args) with _ -> default)

  method on : bool = current_on
  method value : 'relation = current_relation

  method init =
    jquery_input input_selector (fun input ->
      let on = self#get_on input in
      init_on <- on;
      current_froms <- config_graphs#froms;
      current_on <- init_on;
      self#define_relation;
      config_graphs#on_change (fun () -> self#change_relation input);
      onchange
	(fun _ ev -> self#change_relation input)
	input)
  method reset = self#set_on init_on
end

let config_class_hierarchy =
  new config_relation
    ~key:"class_hierarchy"
    ~input_selector:"#input-class-hierarchy"
    ~config_graphs:Sparql_endpoint.config_schema_graphs
    ~default_relation:no_relation
    ~custom_relation:sparql_relations#subclassof
    ()
let config_property_hierarchy =
  new config_relation
    ~key:"property_hierarchy"
    ~input_selector:"#input-property-hierarchy"
    ~config_graphs:Sparql_endpoint.config_schema_graphs
    ~default_relation:no_relation
    ~custom_relation:sparql_relations#subpropertyof
    ()
let config_hierarchy_inheritance =
  new config_relation
      ~key:"hierarchy_inheritance"
      ~input_selector:"#input-hierarchy-inheritance"
      ~config_graphs:Sparql_endpoint.config_schema_graphs
      ~default_relation:no_relation
      ~custom_relation:sparql_relations#inheritsthrough
      ()

let config_sort_by_position =
  new config_relation
      ~key:"sort-by-position"
      ~input_selector:"#input-sort-by-position"
      ~config_graphs:Sparql_endpoint.config_schema_graphs
      ~default_relation:no_relation
      ~custom_relation:sparql_relations#position
      ()
