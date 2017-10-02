(*
  Copyright 2013-2017 Sébastien Ferré, IRISA, Université de Rennes 1

  This file is part of Sparklis.
*)

(* ontological hierarchies *)
class virtual hierarchy = [Rdf.uri,Rdf.uri list] Cache.cache
class pure_hierarchy get_parents = [Rdf.uri,Rdf.uri list] Cache.pure_cache ~get:get_parents
class tabled_hierarchy default_parents bind_parents = [Rdf.uri,Rdf.uri list] Cache.tabled_cache ~default:default_parents ~bind:bind_parents

(* default void hierarchy *)
let no_hierarchy = new pure_hierarchy (fun uri -> [])

let flat_hierarchy =
  new pure_hierarchy
    (fun uri -> if uri=Rdf.owl_Thing then [] else [Rdf.owl_Thing])

(* SPARQL-based hierarchy, retrieving hierarchy from endpoint *)    
let sparql_hierarchy ~(endpoint : string) ~(froms : Rdf.uri list) ~(property : string) ~(orientation : Lisql.orientation) : hierarchy =
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

(* pool of hierarchies for an endpoint as a configuration *)

let sparql_hierarchies =
  object (self)
    inherit Config.input as super

    method get_permalink = []
    method set_permalink _ = ()

    val prop_hierarchy : (Rdf.uri * Lisql.orientation, hierarchy) Hashtbl.t = Hashtbl.create 7
											     
    method init = ()
      
    method set_endpoint url =
      super#set_endpoint url;
      Hashtbl.clear prop_hierarchy

    method reset = ()

    method get ~(froms : Rdf.uri list) (property : Rdf.uri) (orientation : Lisql.orientation) =
      try Hashtbl.find prop_hierarchy (property,orientation)
      with Not_found ->
	let h = sparql_hierarchy ~endpoint ~froms ~property ~orientation in
	Hashtbl.add prop_hierarchy (property,orientation) h;
	h

    method subclassof ~froms = self#get ~froms Rdf.rdfs_subClassOf Lisql.Fwd
    method subpropertyof ~froms = self#get ~froms Rdf.rdfs_subPropertyOf Lisql.Fwd
  end
							     
(* configuration *)

open Js
open Jsutils

class ['hierarchy] config_hierarchy ~(key : string)
  ~(input_selector : string)
  ~(config_graphs : Sparql_endpoint.config_graphs)
  ~(default_hierarchy : 'hierarchy) ~(custom_hierarchy : froms:(Rdf.uri list) -> 'hierarchy) () =
object (self)
  inherit Config.input as super
  val mutable init_on = false
  val mutable current_froms = []
  val mutable current_on = false
  val mutable current_hierarchy = default_hierarchy

  method private get_on input =
    to_bool input##checked
  method private set_on on =
    if current_on <> on then begin
      jquery_input input_selector (fun input -> input##checked <- bool on);
      current_on <- on;
      self#define_hierarchy;
      self#changed
    end

  method private define_hierarchy : unit =
    current_hierarchy <-
      if not current_on
      then begin
	Jsutils.firebug "Using default hierarchy";
	default_hierarchy end
      else begin
	Jsutils.firebug "Using custom hierarchy";
	custom_hierarchy ~froms:config_graphs#froms
      end

  method private change_hierarchy input : unit =
    let fr = config_graphs#froms in
    let on = self#get_on input in
    if fr <> current_froms || on <> current_on then begin
      current_on <- on;
      self#define_hierarchy;
      self#changed
    end
    
  method set_endpoint url =
    super#set_endpoint url;
    self#define_hierarchy

  method get_permalink =
    if current_on <> init_on
    then [(key, string_of_bool current_on)]
    else []
  method set_permalink args =
    let on = try bool_of_string (List.assoc key args) with _ -> true in
    self#set_on on

  method on : bool = current_on
  method value : 'hierarchy = current_hierarchy

  method init =
    jquery_input input_selector (fun input ->
      let on = self#get_on input in
      init_on <- on;
      current_froms <- config_graphs#froms;
      current_on <- init_on;
      self#define_hierarchy;
      config_graphs#on_change (fun () -> self#change_hierarchy input);
      onchange
	(fun _ ev -> self#change_hierarchy input)
	input)
  method reset = self#set_on init_on
end

let config_class_hierarchy =
  new config_hierarchy
    ~key:"class_hierarchy"
    ~input_selector:"#input-class-hierarchy"
    ~config_graphs:Sparql_endpoint.config_schema_graphs
    ~default_hierarchy:no_hierarchy
    ~custom_hierarchy:sparql_hierarchies#subclassof
    ()
let config_property_hierarchy =
  new config_hierarchy
    ~key:"property_hierarchy"
    ~input_selector:"#input-property-hierarchy"
    ~config_graphs:Sparql_endpoint.config_schema_graphs
    ~default_hierarchy:no_hierarchy
    ~custom_hierarchy:sparql_hierarchies#subpropertyof
    ()
 
