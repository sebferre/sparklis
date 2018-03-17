(*
  Copyright 2013-2017 Sébastien Ferré, IRISA, Université de Rennes 1

  This file is part of Sparklis.
*)

(* ontological relations *)
class virtual relation = [Rdf.uri,Rdf.uri list] Cache.cache
class pure_relation get_images = [Rdf.uri,Rdf.uri list] Cache.pure_cache ~get:get_images
class tabled_relation default_images bind_images = [Rdf.uri,Rdf.uri list] Cache.tabled_cache ~default:default_images ~bind:bind_images

(* default void hierarchy *)
let no_relation = new pure_relation (fun uri -> [])


(* SPARQL-based relation, retrieving relation from endpoint *)
let sparql_relation
      ~(name : string)
      ~(endpoint : string)
      ~(froms : Rdf.uri list)
      ~(make_pattern : Sparql.var -> Sparql.var -> Sparql.pattern)
    : relation =
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
	       [ union
		   (List.map (fun x_uri -> bind (uri x_uri :> expr) v_source) l_uri);
		 optional
		   (make_pattern v_source v_image) ]))
	l_l_uri in
    let add_source_image ht_images uri_source uri_image =
      let images_ref =
	try Hashtbl.find ht_images uri_source
	with Not_found ->
	  let imgs_ref = ref [] in
	  Hashtbl.add ht_images uri_source imgs_ref;
	  imgs_ref in
      if not (List.mem uri_image !images_ref)
      then images_ref := uri_image :: !images_ref
      else ()
    in
    Sparql_endpoint.ajax_list_in [] ajax_pool endpoint (l_sparql :> string list)
      (fun l_results ->
	let ht_images : (Rdf.uri, Rdf.uri list ref) Hashtbl.t = Hashtbl.create 101 in
	List.iter
	  (fun results ->
	    let i = List.assoc source results.Sparql_endpoint.vars in
	    let j = List.assoc image results.Sparql_endpoint.vars in
	    List.iter
	      (fun binding ->
		match binding.(i), binding.(j) with
		| Some (Rdf.URI uri_source), Some (Rdf.URI uri_image) -> add_source_image ht_images uri_source uri_image
		| Some (Rdf.URI uri_source), None -> Hashtbl.add ht_images uri_source (ref []) (* recording absence of parents *)
		| _ -> ())
	      results.Sparql_endpoint.bindings)
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
let sparql_relation_property ~endpoint ~froms ~(property : Rdf.uri) ~(inverse : bool) : relation =
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

(* SPARQL-based hierarchy, retrieving hierarchical relation from endpoint *)    
let sparql_relation_hierarchy ~endpoint ~froms ~(property : Rdf.uri) ~(inverse : bool) : relation =
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

(*  
  let ajax_pool = new Sparql_endpoint.ajax_pool in
  let bind_parents l_uri k =
    Jsutils.firebug ("Retrieving parent URIs with property " ^ property ^ ", for " ^ string_of_int (List.length l_uri) ^ " URIs");
    let l_l_uri =
      if Sparql_endpoint.config_method_get#value (* to avoid lengthy queries *)
      then Common.bin_list 50 l_uri (* creating bins of 50 uris max *)
      else [l_uri] in
    let child, middle, parent = "child", "middle", "parent" in (* SPARQL vars *)
    let l_sparql =
      let open Sparql in
      let v_child, v_middle, v_parent = var child, var middle, var parent in
      let t_child, t_middle, t_parent = (v_child :> term), (v_middle :> term), (v_parent :> term) in
      let e_child, e_middle, e_parent = (v_child :> expr), (v_middle :> expr), (v_parent :> expr) in
      let has_parent s o =
	let uri_property = (uri property :> pred) in
	match orientation with
	| Lisql.Fwd -> triple s uri_property o
	| Lisql.Bwd -> triple o uri_property s
      in
      List.map
	(fun l_uri ->
	  select ~projections:[(`Bare,child); (`Bare,parent)] ~froms
	    (join
	       [ union
		   (List.map (fun x_uri -> bind (uri x_uri :> expr) v_child) l_uri);
		 optional
		   (join
		      [ has_parent t_child t_parent;
			filter (expr_comp "!=" e_child e_parent);
			filter (not_exists (has_parent t_parent t_child));
			filter (not_exists (join
					      [ has_parent t_child t_middle;
						has_parent t_middle t_parent;
						filter (log_and [ expr_comp "!=" e_middle e_child;
								  expr_comp "!=" e_middle e_parent ])
					      ]))
		      ])
	       ]))
	l_l_uri in
    let add_child_parent ht_parents uri_child uri_parent =
      let parents_ref =
	try Hashtbl.find ht_parents uri_child
	with Not_found ->
	  let p_ref = ref [] in
	  Hashtbl.add ht_parents uri_child p_ref;
	  p_ref in
      if not (List.mem uri_parent !parents_ref)
	     (* uri_parent <> uri_child
	 && not (List.mem uri_parent !parents_ref)
	 && not (List.mem uri_child (try !(Hashtbl.find ht_parents uri_parent) with _ -> [])) *)
      then parents_ref := uri_parent :: !parents_ref
      else ()
    in
    Sparql_endpoint.ajax_list_in [] ajax_pool endpoint (l_sparql :> string list)
      (fun l_results ->
	let ht_parents : (Rdf.uri, Rdf.uri list ref) Hashtbl.t = Hashtbl.create 101 in
	List.iter
	  (fun results ->
	    let i = List.assoc child results.Sparql_endpoint.vars in
	    let j = List.assoc parent results.Sparql_endpoint.vars in
	    List.iter
	      (fun binding ->
		match binding.(i), binding.(j) with
		| Some (Rdf.URI uri_child), Some (Rdf.URI uri_parent) -> add_child_parent ht_parents uri_child uri_parent
		| Some (Rdf.URI uri_child), None -> Hashtbl.add ht_parents uri_child (ref []) (* recording absence of parents *)
		| _ -> ())
	      results.Sparql_endpoint.bindings)
	  l_results;
	let l_uri_info_opt =
	  Hashtbl.fold
	    (fun uri parents_ref res -> (uri, Some !parents_ref)::res)
	    ht_parents [] in
	k l_uri_info_opt)
      (fun code ->
	ajax_pool#alert ("The parent URIs could not be retrieved for property <" ^ property ^ ">.");
	k [])
  in	 
  new tabled_hierarchy (fun uri -> []) bind_parents
 *)
    
(* pool of hierarchies for an endpoint as a configuration *)

type relation_spec =
  | Property of Rdf.uri * bool (* inverse *)
  | Hierarchy of Rdf.uri * bool (* inverse *)
    
let sparql_relations =
  object (self)
    inherit Config.input as super

    method get_permalink = []
    method set_permalink _ = ()

    val spec_relation : (relation_spec, relation) Hashtbl.t = Hashtbl.create 7
											     
    method init = ()
      
    method set_endpoint url =
      super#set_endpoint url;
      Hashtbl.clear spec_relation

    method reset = ()

    method get ~(froms : Rdf.uri list) (rel_spec : relation_spec) : relation =
      try Hashtbl.find spec_relation rel_spec
      with Not_found ->
	let rel =
	  match rel_spec with
	  | Property (property,inverse) -> sparql_relation_property ~endpoint ~froms ~property ~inverse
	  | Hierarchy (property,inverse) -> sparql_relation_hierarchy ~endpoint ~froms ~property ~inverse in
	Hashtbl.add spec_relation rel_spec rel;
	rel

    method subclassof ~froms = self#get ~froms (Hierarchy (Rdf.rdfs_subClassOf, false))
    method subpropertyof ~froms = self#get ~froms (Hierarchy (Rdf.rdfs_subPropertyOf, false))
    method domain ~froms = self#get ~froms (Property (Rdf.rdfs_domain, false))
    method range ~froms = self#get ~froms (Property (Rdf.rdfs_range, false))
    method inheritsthrough ~froms = self#get ~froms (Property (Rdf.rdfs_inheritsThrough, false))
													 
  end
							     
(* configuration *)

open Js
open Jsutils

class ['relation] config_relation ~(key : string)
  ~(input_selector : string)
  ~(config_graphs : Sparql_endpoint.config_graphs)
  ~(default_relation : 'relation) ~(custom_relation : froms:(Rdf.uri list) -> 'relation) () =
object (self)
  inherit Config.input as super
  val mutable init_on = false
  val mutable current_froms = []
  val mutable current_on = false
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
    if current_on <> init_on
    then [(key, string_of_bool current_on)]
    else []
  method set_permalink args =
    let on = try bool_of_string (List.assoc key args) with _ -> true in
    self#set_on on

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
