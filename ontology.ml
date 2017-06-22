(*
  Copyright 2013-2017 Sébastien Ferré, IRISA, Université de Rennes 1

  This file is part of Sparklis.

  Sparklis is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Sparklis is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with Sparklis.  If not, see <http://www.gnu.org/licenses/>.
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
let sparql_hierarchy ~(endpoint : string) ~(froms : Rdf.uri list) ~(property : string) : hierarchy =
  let ajax_pool = new Sparql_endpoint.ajax_pool in
  let bind_parents l_uri k =
    Jsutils.firebug ("Retrieving parent URIs for " ^ string_of_int (List.length l_uri) ^ " URIs");
    let l_l_uri =
      if Sparql_endpoint.config_method_get#value (* to avoid lengthy queries *)
      then Common.bin_list 50 l_uri (* creating bins of 50 uris max *)
      else [l_uri] in
    let child, parent = "child", "parent" in (* SPARQL vars *)
    let l_sparql =
      let open Sparql in
      let v_child, v_parent = Sparql.var child, Sparql.var parent in
      List.map
	(fun l_uri ->
	  select ~projections:[(`Bare,child); (`Bare,parent)] ~froms
	    (join
	       [ union
		   (List.map (fun x_uri -> bind (uri x_uri :> expr) v_child) l_uri);
		 optional
		   (triple (v_child :> term) (uri property) (v_parent :> term)) ]))
	l_l_uri in
    let add_child_parent ht_parents uri_child uri_parent =
      let parents_ref =
	try Hashtbl.find ht_parents uri_child
	with Not_found ->
	  let p_ref = ref [] in
	  Hashtbl.add ht_parents uri_child p_ref;
	  p_ref in
      if uri_parent <> uri_child
	 && not (List.mem uri_parent !parents_ref)
	 && not (List.mem uri_child (try !(Hashtbl.find ht_parents uri_parent) with _ -> []))
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

let sparql_class_hierarchy ~endpoint ~froms () = sparql_hierarchy ~endpoint ~froms ~property:Rdf.rdfs_subClassOf
let sparql_property_hierarchy ~endpoint ~froms () = sparql_hierarchy ~endpoint ~froms ~property:Rdf.rdfs_subPropertyOf
    
(* configuration *)

open Js
open Jsutils

class ['hierarchy] config_hierarchy ~(key : string)
  ~(input_selector : string)
  ~(config_graphs : Sparql_endpoint.config_graphs)
  ~(default_hierarchy : 'hierarchy) ~(custom_hierarchy : endpoint:string -> froms:(Rdf.uri list) -> unit -> 'hierarchy) () =
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
	custom_hierarchy ~endpoint ~froms:config_graphs#froms ()
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
    ~custom_hierarchy:sparql_class_hierarchy
    ()
let config_property_hierarchy =
  new config_hierarchy
    ~key:"property_hierarchy"
    ~input_selector:"#input-property-hierarchy"
    ~config_graphs:Sparql_endpoint.config_schema_graphs
    ~default_hierarchy:no_hierarchy
    ~custom_hierarchy:sparql_property_hierarchy
    ()
 
