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

(* ontological relations *)
class virtual ['a] relation = [Rdf.uri, 'a list] Cache.cache
class ['a] pure_relation get = [Rdf.uri, 'a list] Cache.pure_cache ~get
class ['a] init_relation default bind = [Rdf.uri, 'a list] Cache.init_cache ~default ~bind
class ['a] tabled_relation default bind = [Rdf.uri, 'a list] Cache.tabled_cache ~default ~bind

(* default void hierarchy *)
let no_relation = new pure_relation (fun uri -> [])

(* SPARQL-based relations *)

class ['a] source_images =
object
  val ht_images : (Rdf.uri, 'a list ref) Hashtbl.t = Hashtbl.create 101

  method add uri_source image =
    let images_ref =
      try Hashtbl.find ht_images uri_source
      with Not_found ->
	let imgs_ref = ref [] in
	Hashtbl.add ht_images uri_source imgs_ref;
	imgs_ref in
    if not (List.mem image !images_ref)
    then images_ref := image :: !images_ref
    else ()

  method add_no_image uri_source =
    Hashtbl.add ht_images uri_source (ref [])

  method list =
    Hashtbl.fold
      (fun uri_source images_ref res -> (uri_source, Some !images_ref)::res)
      ht_images []
end

let sparql_relation_process_results ~image_opt_of_term source image src_imgs results =
  try
    let i = List.assoc source results.Sparql_endpoint.vars in
    let j_opt = try Some (List.assoc image results.Sparql_endpoint.vars) with _ -> None in
    (* some endpoints do not include ?image when no binding at all (in OPTIONAL) *)
    List.iter
      (fun binding ->
	match binding.(i),
              (match j_opt with
               | None -> None
               | Some j -> match binding.(j) with
                           | None -> None
                           | Some t -> image_opt_of_term t)
        with
	| Some (Rdf.URI uri_source), Some image -> src_imgs#add uri_source image
	| Some (Rdf.URI uri_source), None -> src_imgs#add_no_image uri_source (* recording absence of image *)
	| _ -> ())
      results.Sparql_endpoint.bindings
  with _ -> Jsutils.firebug ("Missing variable(s) in SPARQL results: ?uri")

  
(* SPARQL-based relation, computed at once *)
let sparql_init_relation
      ~(name : string)
      ~(endpoint : string)
      ~(froms : Rdf.uri list)
      ~(make_pattern : Sparql.var -> Sparql.var -> Sparql.pattern)
      ~(image_opt_of_term : Rdf.term -> 'a option)
    : 'a relation =
  let ajax_pool = new Sparql_endpoint.ajax_pool in
  let bind k =
    Jsutils.firebug ("Retrieving relation " ^ name);
    let source, image = "uri", "image" in (* SPARQL vars *)
    let sparql =
      let open Sparql in
      let v_source, v_image = var source, var image in
      select ~projections:[(`Bare,source); (`Bare,image)] ~froms
        (make_pattern v_source v_image) in
    Sparql_endpoint.ajax_in [] ajax_pool endpoint (sparql :> string)
      (fun sparql results ->
        let src_imgs = new source_images in
        sparql_relation_process_results ~image_opt_of_term source image src_imgs results;
        k src_imgs#list)
      (fun code ->
        ajax_pool#alert ("Relation " ^ name ^ " could not be retrieved.");
        k [])
  in
  new init_relation (fun uri -> []) bind
                
(* SPARQL-based relation, computed by chunks of source URIS *)
let sparql_tabled_relation
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
		   (List.map (fun x_uri -> (term_uri x_uri :> term)) l_uri);
		 optional
		   (make_pattern v_source v_image) ]))
	l_l_uri in
    Sparql_endpoint.ajax_list_in [] ajax_pool endpoint (l_sparql :> string list)
      (fun l_results ->
        let src_imgs = new source_images in
	List.iter
	  (fun results ->
            sparql_relation_process_results ~image_opt_of_term source image src_imgs results)
	  l_results;
	k src_imgs#list)
      (fun code ->
	ajax_pool#alert ("The image URIs could not be retrieved in " ^ name ^ ".");
	k [])
  in
  new tabled_relation (fun uri -> []) bind_images

(* SPARQL-based relation, retrieving data from endpoint *)
let sparql_relation_property ~(mode : [`Init | `Tabled]) ~endpoint ~froms ~(property : Rdf.uri) ~(inverse : bool) ~(image_opt_of_term : Rdf.term -> 'a option) : 'a relation =
  let make_pattern v_source v_image : Sparql.pattern =
    let open Sparql in
    let uri_property = (path_uri property :> pred) in
    if inverse
    then triple (v_image :> term) uri_property (v_source :> term)
    else triple (v_source :> term) uri_property (v_image :> term)
  in
  let sparql_relation =
    match mode with
    | `Init -> sparql_init_relation
    | `Tabled -> sparql_tabled_relation in
  sparql_relation
    ~name:("property <" ^ property ^ ">")
    ~endpoint
    ~froms
    ~make_pattern
    ~image_opt_of_term

(* SPARQL-based hierarchy, retrieving hierarchical relation from endpoint *)    
let sparql_relation_hierarchy ~(mode : [`Init | `Tabled]) ~endpoint ~froms ~(property_path : Sparql.pred) : Rdf.uri relation =
  let make_pattern v_child v_parent : Sparql.pattern =
    let open Sparql in
    let has_parent s o = triple s property_path o in
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
  let sparql_relation =
    match mode with
    | `Init -> sparql_init_relation
    | `Tabled -> sparql_tabled_relation in
  sparql_relation
    ~name:("property path: " ^ (property_path :> string))
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
    val ht_hierarchy : (Sparql.pred, Rdf.uri relation) Hashtbl.t = Hashtbl.create 7
											     
    method init = ()
      
    method set_endpoint url =
      super#set_endpoint url;
      Hashtbl.clear ht_property_number;
      Hashtbl.clear ht_property_uri;
      Hashtbl.clear ht_hierarchy

    method reset = ()

    method get_property_number ~mode ~(froms : Rdf.uri list) ~(property : Rdf.uri) : float relation =
      try Hashtbl.find ht_property_number property
      with Not_found ->
	let rel = sparql_relation_property ~mode
		    ~endpoint ~froms ~property ~inverse:false
		    ~image_opt_of_term:(function Rdf.Number (f,_,_) -> Some f | _ -> None) in
	Hashtbl.add ht_property_number property rel;
	rel

    method get_property_uri ~mode ~(froms : Rdf.uri list) ~(property : Rdf.uri) ~(inverse : bool) : Rdf.uri relation =
      try Hashtbl.find ht_property_uri (property,inverse)
      with Not_found ->
	let rel = sparql_relation_property ~mode
		    ~endpoint ~froms ~property ~inverse
		    ~image_opt_of_term:(function Rdf.URI uri -> Some uri | _ -> None) in
	Hashtbl.add ht_property_uri (property,inverse) rel;
	rel

    method get_hierarchy ~mode ~(froms : Rdf.uri list) ~(property_path : Sparql.pred) : Rdf.uri relation =
      try Hashtbl.find ht_hierarchy property_path
      with Not_found ->
	let rel = sparql_relation_hierarchy ~mode ~endpoint ~froms ~property_path in
	Hashtbl.add ht_hierarchy property_path rel;
	rel
	  
    method subclassof ~froms = self#get_hierarchy ~mode:`Tabled ~froms ~property_path:(Sparql.path_uri Rdf.rdfs_subClassOf :> Sparql.pred)
    method subpropertyof ~froms = self#get_hierarchy ~mode:`Tabled ~froms ~property_path:(Sparql.path_uri Rdf.rdfs_subPropertyOf :> Sparql.pred)
    method domain ~froms = self#get_property_uri ~mode:`Init ~froms ~property:Rdf.rdfs_domain ~inverse:false
    method range ~froms = self#get_property_uri ~mode:`Init ~froms ~property:Rdf.rdfs_range ~inverse:false
    method inheritsthrough ~froms = self#get_property_uri ~mode:`Init ~froms ~property:Rdf.rdfs_inheritsThrough ~inverse:false
    method transitiveclosure ~froms = self#get_property_uri ~mode:`Init ~froms ~property:Rdf.owl_transitiveOf ~inverse:true

    method position ~froms = self#get_property_number ~mode:`Tabled ~froms ~property:Rdf.schema_position
    method logo ~froms = self#get_property_uri ~mode:`Tabled ~froms ~property:Rdf.schema_logo ~inverse:false
  end
							     
(* configuration *)

open Js_of_ocaml
       
open Js
open Jsutils

class ['relation] config_relation ~(key : string)
  ~(input_selector : string)
  ~(config_graphs : Sparql_endpoint.config_graphs)
  ~(inactive_relation : 'relation)
  ~(active_relation : froms:(Rdf.uri list) -> 'relation)
  ~(default : bool) () =
object (self)
  inherit Config.input as super
  val mutable init_on = default
  val mutable current_froms = []
  val mutable current_on = default
  val mutable current_relation = inactive_relation

  method private get_on input =
    to_bool input##.checked
  method private set_on on =
    if current_on <> on then begin
      jquery_input input_selector (fun input -> input##.checked := bool on);
      current_on <- on;
      self#define_relation;
      self#changed
    end

  method private define_relation : unit =
    current_relation <-
      if not current_on
      then begin
	Jsutils.firebug "Using default relation";
	inactive_relation end
      else begin
	Jsutils.firebug "Using custom relation";
	active_relation ~froms:config_graphs#froms
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
    ~inactive_relation:no_relation
    ~active_relation:sparql_relations#subclassof
    ~default:true
    ()
let config_property_hierarchy =
  new config_relation
    ~key:"property_hierarchy"
    ~input_selector:"#input-property-hierarchy"
    ~config_graphs:Sparql_endpoint.config_schema_graphs
    ~inactive_relation:no_relation
    ~active_relation:sparql_relations#subpropertyof
    ~default:true
    ()
  
let config_hierarchy_inheritance =
  new config_relation
      ~key:"hierarchy_inheritance"
      ~input_selector:"#input-hierarchy-inheritance"
      ~config_graphs:Sparql_endpoint.config_schema_graphs
      ~inactive_relation:no_relation
      ~active_relation:sparql_relations#inheritsthrough
      ~default:false
      ()
let config_transitive_closure =
  new config_relation
    ~key:"transitive_closure"
    ~input_selector:"#input-transitive-closure"
    ~config_graphs:Sparql_endpoint.config_schema_graphs
    ~inactive_relation:no_relation
    ~active_relation:sparql_relations#transitiveclosure
    ~default:false
    ()
  
let config_sort_by_position =
  new config_relation
      ~key:"sort_by_position"
      ~input_selector:"#input-sort-by-position"
      ~config_graphs:Sparql_endpoint.config_schema_graphs
      ~inactive_relation:no_relation
      ~active_relation:sparql_relations#position
      ~default:false
      ()
let config_show_logo =
  new config_relation
      ~key:"show_logo"
      ~input_selector:"#input-show-logo"
      ~config_graphs:Sparql_endpoint.config_schema_graphs
      ~inactive_relation:no_relation
      ~active_relation:sparql_relations#logo
      ~default:false
      ()

(* utilities for enqueuing and syncing *)

let enqueue_entity uri =
  config_sort_by_position#value#enqueue uri;
  config_show_logo#value#enqueue uri
let enqueue_class uri =
  config_class_hierarchy#value#enqueue uri;
  config_hierarchy_inheritance#value#enqueue uri;
  enqueue_entity uri
let enqueue_property uri =
  config_property_hierarchy#value#enqueue uri;
  config_hierarchy_inheritance#value#enqueue uri;
  config_transitive_closure#value#enqueue uri;
  enqueue_entity uri
let enqueue_pred uri =
  enqueue_entity uri
let enqueue_arg uri =
  enqueue_entity uri

let sync_entities k =
  config_sort_by_position#value#sync
    (fun () ->
      config_show_logo#value#sync k)
let sync_concepts k =
  config_class_hierarchy#value#sync
    (fun () ->
     config_property_hierarchy#value#sync
       (fun () ->
	 sync_entities k))
let sync_endpoint k =
  config_hierarchy_inheritance#value#sync
    (fun () ->
      config_transitive_closure#value#sync k)
