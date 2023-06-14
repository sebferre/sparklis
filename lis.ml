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
open Js

(* indices *)

type 'a forest = 'a tree list
and 'a tree = Node of 'a * 'a forest
let js_forest_map (m : 'a Jsutils.js_map) : 'a forest Jsutils.js_map =
  Jsutils.js_map
    (`List (`Record [| "item", Jsutils.js_custom_spec m; (* singleton sum is like a record *)
                       "children", `Rec "self" |]))

let rec forest_filter_map (f : 'a -> 'b option) : 'a forest -> 'b forest =
  function
  | [] -> []
  | tree::forest1 -> tree_filter_map f tree @ forest_filter_map f forest1
and tree_filter_map f : 'a tree -> 'b forest =
  function
  | Node (item, children) ->
     match f item with
     | None -> forest_filter_map f children
     | Some item' -> [Node (item', forest_filter_map f children)]

                   
class ['a,'b] index ?(parents : ('a -> 'a list) option) () =
object (self)
  val mutable organized : bool = false
  val mutable h : ('a, 'b * 'a list ref (* children *) * 'a list ref (* parents *)) Hashtbl.t = Hashtbl.create 101
  val mutable roots : 'a list = []
  val mutable leaves : 'a list = []

  method mem (elt : 'a) : bool =
    Hashtbl.mem h elt
  method get (elt : 'a) : 'b option =
    try
      let v, _, _ = Hashtbl.find h elt in
      Some v
    with Not_found -> None
  method add (elt, info : 'a * 'b) : unit =
    assert (not organized);
    Hashtbl.add h elt (info, ref [], ref [])
  method remove (elt : 'a) : unit =
    assert (not organized);
    Hashtbl.remove h elt
    
  method private organize : unit = (* WARNING: must be called after all additions *)
    match organized, parents with
    | _, None -> ()
    | true, _ -> ()
    | false, Some parents ->
      let add_child k_parent k_child : bool = (* returns true if parent exists *)
	try
	  let _v, ref_children, _ref_parents = Hashtbl.find h k_parent in
	  ref_children := k_child::!ref_children;
	  true
	with Not_found -> false (* absent parents are ignored *)
      in
      Hashtbl.iter
	(fun k_child (_,_,ref_parents) ->
	  let l_parents = parents k_child in
	  let present_parents =
	    List.filter
	      (fun k_parent ->
	        let present = add_child k_parent k_child in
		present)
	      l_parents in
	  ref_parents := present_parents)
	h;
      Hashtbl.iter
	(fun k (_, ref_children, ref_parents) ->
	  if !ref_children = [] then leaves <- k::leaves;
	  if !ref_parents = [] then roots <- k::roots)
	h;
      organized <- true

  method is_empty : bool = (Hashtbl.length h = 0)
  method length : int = Hashtbl.length h
  method fold : 'c. ('c -> 'a * 'b -> 'c) -> 'c -> 'c =
    fun f init -> Hashtbl.fold (fun k (v,_,_) res -> f res (k,v)) h init
  method iter : ('a * 'b -> unit) -> unit =
    fun f -> Hashtbl.iter (fun k (v,_,_) -> f (k,v)) h
  method filter_map_list : 'c. ('a * 'b -> 'c option) -> 'c list =
    fun f ->
    Hashtbl.fold
      (fun k (v,_,_) res ->
       match f (k,v) with
       | Some x -> x::res
       | None -> res)
      h []
  method filter_map_forest : 'c. inverse:bool -> ('a * 'b -> 'c option) -> 'c forest =
    fun ~inverse f ->
      self#organize;
      if organized then
	let rec aux ancestors (keys : 'a list) =
	  Common.mapfilter
	    (fun k ->
	     if List.mem k ancestors (* there is a loop through k *)
	     then None
	     else
	       let k, (v, ref_children, ref_parents) =
		 try k, Hashtbl.find h k
		 with Not_found -> assert false in
	       match f (k,v) with
	       | Some x ->
		  let node_children =
		    if inverse
		    then aux (k::ancestors) !ref_parents
		    else aux (k::ancestors) !ref_children in
		  Some (Node (x, node_children))
	       | None -> None)
	    keys
	in
	aux [] (if inverse then leaves else roots)
      else (* no tree organization *)
	Hashtbl.fold
	  (fun k (v,_,_) res ->
	   match f (k,v) with
	   | Some x -> Node (x, []) :: res
	   | None -> res)
	  h []
  method sample_list : 'c. int -> ('a * 'b -> 'c) -> int * 'c list =
    fun max f ->
    let _, n, res =
      Hashtbl.fold
	(fun k (v,_,_) (max,n,res as acc) ->
	 if max <= 0 then acc else (max-1, n+1, f (k,v) :: res))
	h (max,0,[]) in
    n, res
end
  
let empty_index () = new index ()
let singleton_index elt_info =
  let index = new index () in
  index#add elt_info;
  index
							  
class ['a] int_index = ['a,int] index ()
class ['a,'b] nested_int_index = ['a, int * 'b int_index] index ()

type freq_unit = Results | Entities | Concepts | Modifiers
let js_freq_unit_map : freq_unit Jsutils.js_map =
  Jsutils.js_map
    (`Enum [| "Results"; "Entities"; "Concepts"; "Modifiers"|])
  
type freq = { value : int; max_value : int option; partial : bool; unit : freq_unit }
let js_freq_map : freq Jsutils.js_map =
  let open Jsutils in
  js_map
    (`Record [| "value", `Int;
                "maximum", `Option `Int;
                "partialCount", `Bool;
                "unit", js_custom_spec js_freq_unit_map |])

class incr_freq_index = [Lisql.increment, freq option] index ()

type incr_freq_forest = (Lisql.increment * freq option) forest
let js_incr_freq_forest_map : incr_freq_forest Jsutils.js_map =
  let open Jsutils in
  js_forest_map
    (js_map (`Record [| "suggestion", js_custom_spec Lisql.js_increment_map; (* Tuple and Record have same internal repr *)
                        "frequency", `Option (js_custom_spec js_freq_map) |]))

type suggestions =
  { partial : bool;
    forest : incr_freq_forest }
let js_suggestions_map : suggestions Jsutils.js_map =
  let open Jsutils in
  js_map
    (`Record [| "partial", `Bool;
                "forest", js_custom_spec js_incr_freq_forest_map |])
  
(* increment hierarchies*)
  
let term_hierarchy_of_focus focus =
  match Lisql.hierarchy_of_focus focus with
  | None -> Ontology.no_relation
  | Some (id,pred,args,argo) ->
     Ontology.sparql_relations#get_hierarchy
       ~mode:`Tabled
       ~froms:Sparql_endpoint.config_default_graphs#froms
       ~property_path:(Lisql2sparql.path_pred_args_argo pred args argo)
						       
let increment_parents (term_hierarchy : Rdf.uri Ontology.relation) = function
  | Lisql.IncrTerm (Rdf.URI uri) -> List.map (fun u -> Lisql.IncrTerm (Rdf.URI u)) (term_hierarchy#info uri)
  | Lisql.IncrType uri -> List.map (fun u -> Lisql.IncrType u) (Ontology.config_class_hierarchy#value#info uri)
  | Lisql.IncrRel (uri,xwd) -> List.map (fun u -> Lisql.IncrRel (u,xwd)) (Ontology.config_property_hierarchy#value#info uri)
  | _ -> []
class incr_freq_tree_index th = [Lisql.increment, freq option] index ~parents:(increment_parents th) ()


(* configuration *)

let config_intentional_init_concepts = new Config.boolean_input ~key:"intentional_init_concepts" ~input_selector:"#input-intentional-init-concepts" ~default:true ()
let config_nary_relations = new Config.boolean_input ~key:"nary_relations" ~input_selector:"#input-nary-relations" ~default:false ()
let config_incr_sim = new Config.boolean_input ~key:"incr_sim" ~input_selector:"#input-incr-sim" ~default:false ()
let config_concept_profile = new Config.string_input ~key:"concept_profile" ~input_selector:"#input-concept-profile" ~default:"" ()
let config_regexp_hidden_URIs = new Config.string_input ~key:"regexp_hidden_URIs" ~input_selector:"#input-regexp-hidden-uris" ~default:"" ()
let config_max_results = new Config.integer_input ~key:"max_results" ~input_selector:"#input-max-results" ~min:1 ~default:200 ()
let config_max_increment_samples = new Config.integer_input ~key:"max_increment_samples" ~input_selector:"#input-max-increment-samples" ~min:1 ~default:200 ()
let config_max_classes = new Config.integer_input ~key:"max_classes" ~input_selector:"#input-max-classes" ~min:0 ~default:200 ()
let config_max_properties = new Config.integer_input ~key:"max_properties" ~input_selector:"#input-max-properties" ~min:0 ~default:200 ()
let config_avoid_lengthy_queries = new Config.boolean_input ~key:"avoid_lengthy_queries" ~input_selector:"#input-avoid-lengthy-queries" ~default:false ()

let regexp_sep = Regexp.regexp "[,;][ ]*"

let formula_concept_profile_term (tx : _ Sparql.any_term) : Sparql.formula =
  let profile = config_concept_profile#value in
  if profile = ""
  then Sparql.True
  else
    let uris = List.filter ((<>) "") (Regexp.split regexp_sep profile) in
    if uris = []
    then Sparql.True
    else Sparql.(Pattern
		   (union
		      (List.map
			 (fun u -> rdf_type tx (term_uri u))
			 uris)))
let formula_concept_profile (v : string) : Sparql.formula =
  formula_concept_profile_term (Sparql.var v)

			       
let formula_hidden_URIs_term (tx : _ Sparql.any_term) : Sparql.formula =
  match config_regexp_hidden_URIs#value with
  | "" -> Sparql.True
  | re -> Sparql.(Filter (log_not (log_and [expr_func "BOUND" [tx]; expr_regex (expr_func "str" [tx]) re])))
let formula_hidden_URIs (v : string) : Sparql.formula =
  formula_hidden_URIs_term (Sparql.var v)
let pattern_hidden_URIs (v : string) : Sparql.pattern =
  Sparql.pattern_of_formula (formula_hidden_URIs v)
    
(* private intermediate functions, used to produce index *)
let nested_hashtbl_of_results_varterm_list
      (keys_vt : Rdf.term list) (nested_vt_opt : Rdf.term option)
      results : (Rdf.term option list, int ref * (Rdf.term option, int ref) Hashtbl.t) Hashtbl.t =
  let open Sparql_endpoint in
  let get vt : binding -> Rdf.term option =
    match vt with
    | Rdf.Var v ->
       if List.mem_assoc v results.vars
       then
	 let i = List.assoc v results.vars in
	 (fun binding -> binding.(i))
       else (fun binding -> None)
    | t ->
       (fun binding -> Some t) in
  let get_keys =
    let l_get_key = List.map get keys_vt in
    (fun binding -> List.map ((|>) binding) l_get_key) in
  let get_nested =
    match nested_vt_opt with
    | None -> (fun binding -> None)
    | Some nested_vt ->
       let get_nested = get nested_vt in
       (fun binding -> get_nested binding)
  in
  let ht = Hashtbl.create 1000 in
  List.iter
    (fun binding ->
     let keys = get_keys binding in
     let cpt1, nested_ht =
       try Hashtbl.find ht keys
       with Not_found ->
	 let data = ref 0, Hashtbl.create 3 in
	 Hashtbl.add ht keys data;
	 data in
     incr cpt1;
     let nested = get_nested binding in
     let cpt2 =
       try Hashtbl.find nested_ht nested
       with Not_found ->
	 let cpt2 = ref 0 in
	 Hashtbl.add nested_ht nested cpt2;
	 cpt2 in
     incr cpt2)
    results.bindings;
  ht

let int_index_of_nested_hashtbl ~mapfilter ht =
  let index = new int_index in
  Hashtbl.iter
    (fun k cpt ->
     match mapfilter k with
     | None -> ()
     | Some k -> index#add (k, !cpt))
    ht;
  index
let nested_int_index_of_hashtbl ~mapfilter ~nested_mapfilter ht =
  let index = new nested_int_index in
  Hashtbl.iter
    (fun k (cpt1,nested_ht) ->
     match mapfilter k with
     | None -> ()
     | Some k -> index#add (k, (!cpt1, int_index_of_nested_hashtbl ~mapfilter:nested_mapfilter nested_ht)))
    ht;
  index
let int_index_of_hashtbl ~mapfilter ht =
  let index = new int_index in
  Hashtbl.iter
    (fun k (cpt,_) ->
     match mapfilter k with
     | None -> ()
     | Some k -> index#add (k, !cpt))
    ht;
  index

    
let index_of_results_varterm ?(filter = fun (_ : Rdf.term) -> true) vt results : Rdf.term int_index =
  match vt with
  | Rdf.Var _ ->
     let ht = nested_hashtbl_of_results_varterm_list [vt] None results in
     int_index_of_hashtbl
       ~mapfilter:(function [Some key] when filter key -> Some key | _ -> None)
       ht
  | t -> singleton_index (t,1)

(* distinct count of values for some results column *)
let count_of_results_varterm vt results : int =
  match vt with
  | Rdf.Var _ ->
     let ht = nested_hashtbl_of_results_varterm_list [vt] None results in
     Hashtbl.length ht
  | t -> 1
			 
let index_of_results_varterm_list ?(filter = fun (_ : Rdf.term) -> true) keys_vt results : Rdf.term option list int_index =
  if List.exists Rdf.term_is_var keys_vt
  then
    let ht = nested_hashtbl_of_results_varterm_list keys_vt None results in
    int_index_of_hashtbl
      ~mapfilter:(fun keys -> if List.for_all (function None -> true | Some key -> filter key) keys then Some keys else None)
      ht
  else singleton_index (List.map (fun t -> Some t) keys_vt, 1)

let nested_index_of_results_varterm ?(filter = fun _ -> true) key_vt nested_vt_opt results : (Rdf.term, Rdf.term) nested_int_index =
  match key_vt, nested_vt_opt with
  | Rdf.Var _, _
  | _, Some (Rdf.Var _) ->
     let ht = nested_hashtbl_of_results_varterm_list [key_vt] nested_vt_opt results in
     nested_int_index_of_hashtbl
       ~mapfilter:(function [Some key] when filter key -> Some key | _ -> None)
       ~nested_mapfilter:(function Some nested when filter nested -> Some nested | _ -> None)
       ht
  | t, None -> singleton_index (t, (1,empty_index ()))
  | t, Some nested_t -> singleton_index (t, (1,singleton_index (nested_t,1)))
					
let nested_index_of_results_varterm_list ~(mapfilter : Rdf.term option -> 'a option) keys_vt nested_vt_opt results : ('a list, 'a) nested_int_index =
  if List.exists Rdf.term_is_var keys_vt
  then begin
    let ht = nested_hashtbl_of_results_varterm_list keys_vt nested_vt_opt results in
    nested_int_index_of_hashtbl
      ~mapfilter:(fun keys -> Common.mapforall mapfilter keys)
      ~nested_mapfilter:(fun nested_opt -> mapfilter nested_opt)
      ht end
  else begin
    let nested_index =
      match nested_vt_opt with
      | None -> empty_index ()
      | Some nested_vt ->
	 ( match nested_vt with
	   | Rdf.Var _ -> index_of_results_varterm ~filter:(fun t -> mapfilter (Some t) <> None) nested_vt results
	   | nested_t -> singleton_index (nested_t,1) ) in
    match Common.mapforall (fun key_vt -> mapfilter (Some key_vt)) keys_vt with
    | Some keys -> singleton_index (keys, (1, nested_index))
    | None -> empty_index ()
    end		      

let index_of_results_varterm_list_count (keys_vt : Rdf.term list) (var_count : Rdf.var) results : Rdf.term option list int_index =
  let open Sparql_endpoint in
  let get vt : binding -> Rdf.term option =
    match vt with
    | Rdf.Var v ->
       if List.mem_assoc v results.vars
       then
	 let i = List.assoc v results.vars in
	 (fun binding -> try binding.(i) with _ -> assert false)
       else (fun binding -> None)
    | t ->
       (fun binding -> Some t) in
  let get_keys =
    let l_get_key = List.map get keys_vt in
    (fun binding -> List.map ((|>) binding) l_get_key) in
  let index = new int_index in
  try
    let i_count = try List.assoc var_count results.vars with _ -> -1 in
    List.iter
      (fun binding ->
       let keys = get_keys binding in
       let count =
	 if i_count < 0
	 then 1
	 else
	   match binding.(i_count) with
	   | Some (Rdf.Number (f,s,dt)) -> (try int_of_string s with _ -> 1)
	   | Some (Rdf.TypedLiteral (s,dt)) -> (try int_of_string s with _ -> 1)
	   | _ -> 1 in
       index#add (keys, count))
      results.bindings;
    index
  with Not_found ->
    Jsutils.firebug "index_of_results_varterm_list_count: missing variables";
    index

(* extraction of the extension and indexes *)

let enqueue_term = function
  | Rdf.URI uri ->
     Ontology.enqueue_entity uri;
     Lexicon.enqueue_entity uri
  | Rdf.TypedLiteral (_,dt) ->
     Lexicon.enqueue_class dt
  | _ -> ()

let enqueue_term_opt = function
  | None -> ()
  | Some t -> enqueue_term t

let enqueue_binding_terms binding =
  Array.iter
    (function
      | Some t -> enqueue_term t
      | None -> ())
    binding
	   
let sync_terms k =
  Lexicon.sync_entities
    (fun () ->
      Ontology.sync_entities
	(fun () -> k ()))
	   
let sync_concepts k =
  Ontology.sync_concepts
    (fun () ->
      Lexicon.sync_concepts
	(fun () -> k ()))
	   
let page_of_results
      (offset : int) (limit : int)
      (geolocs : (Sparql.term * (Rdf.var * Rdf.var)) list)
      (results : Sparql_endpoint.results)
      (k : Sparql_endpoint.results (* subset of results *) -> unit) : unit =
  let open Sparql_endpoint in
  let rec aux offset limit acc = function
    | [] -> acc
    | binding::l ->
      if offset > 0 then aux (offset-1) limit acc l
      else if limit > 0 then begin
	enqueue_binding_terms binding;
	aux offset (limit-1) (binding :: acc) l end
      else acc
  in
  let partial_vars =
    List.filter
      (fun (v,i) -> not (List.exists (fun (_,(vlat,vlong)) -> v=vlat || v=vlong) geolocs))
      results.vars in
  let partial_bindings = List.rev (aux offset limit [] results.bindings) in
  let partial_results = { results with vars = partial_vars; bindings = partial_bindings } in
  sync_terms (* datatypes and entities *)
    (fun () -> k partial_results)

let list_of_results_column (var : Rdf.var) results : Rdf.term list =
  let open Sparql_endpoint in
  try
    let i = List.assoc var results.vars in
    List.fold_left
      (fun res binding ->
	match binding.(i) with
	  | None -> res
	  | Some t -> t::res)
      [] results.bindings
  with Not_found ->
    Jsutils.firebug ("list_of_results_column: missing variable " ^ var);
    []


(* use of dependencies between vars to structure query results *)
    
type results_shape =
  | Unit
  | Concat of results_shape list (* INV: at least 2 elements *)
  | Map of Rdf.var * results_shape
  | Descr of Rdf.term * results_shape

let rec string_of_results_shape = function
  | Unit -> "[]"
  | Concat lsh ->
     String.concat " " (List.map (fun sh -> "< " ^ string_of_results_shape sh ^ " >") lsh)
  | Map (x,Unit) -> "?" ^ x
  | Map (x,sh) -> "?" ^ x ^ ", " ^ string_of_results_shape sh
  | Descr (t,sh) -> Rdf.string_of_term t ^ ", " ^ string_of_results_shape sh
      
module FMDeps =
  Find_merge.Set
    (struct type t = Rdf.term let compare = Stdlib.compare end)
	     
let results_shape_of_deps
      (deps : Lisql2sparql.deps)
      (geolocs : (Sparql.term * (Rdf.var * Rdf.var)) list)
      (lx : Rdf.var list) : results_shape =
  let deps =
    let rec transform_dep = function
      (* return dep made of variables only, and in-order term-var dependencies *)
      (* term-var deps allow to insert Desc (term, ...) above the var *)
      | [] -> [], []
      | [t] ->
	 if Rdf.term_is_var t
	 then [t], []
	 else [], []
      | t1::(t2::r2 as r1) ->
	 let dep_xs1, deps_tx1 = transform_dep r1 in
	 if Rdf.term_is_var t1
	 then t1::dep_xs1, deps_tx1
	 else (* t1 is not a var *)
	   if Rdf.term_is_var t2
	   then dep_xs1, [t1;t2]::deps_tx1 (* adding [term;var] dep *)
	   else dep_xs1, deps_tx1
    in
    List.fold_left
      (fun deps dep ->
       let dep_xs, deps_tx = transform_dep dep in
       if dep_xs = []
       then deps
       else dep_xs :: deps_tx @ deps)
      [] deps in
  let lx = (* excluding geolocation variables *)
    List.filter
      (fun x -> not (List.exists (fun (_,(vlat,vlong)) -> x=vlat || x=vlong) geolocs))
      lx in
  let rec shape_of_deps deps lx : results_shape =
    let fm_of_deps deps =
      List.fold_left
	(fun fm dep ->
	 match dep with
	 | [] -> fm
	 | _ -> snd (FMDeps.merge dep fm))
	FMDeps.empty deps
    in
    match lx with
    | [] -> Unit
    | x1::lxr ->
       let fm = fm_of_deps deps in
       match list_shape_of_fm fm x1 lxr deps with
       | [] -> Unit
       | [sh] -> sh
       | lsh -> Concat lsh
  and list_shape_of_fm fm x1 lxr deps =
    let tx1 = Rdf.Var x1 in
    let terms_with_t1 = FMDeps.merged_with tx1 fm in
    let t1 = (* looking for an adjacent non-var term of tx1, if any *)
      List.fold_left
	(fun res dep ->
	 if List.mem tx1 dep
	 then
	   List.fold_right
	     (fun t res2 ->
	      if t = tx1 then res (* ignoring terms after tx1 in dep *)
	      else if Rdf.term_is_var t then res2 (* ignoring other terms *)
	      else t)
	     dep res
	 else res)
	tx1 deps in
    let lxr = if t1 = tx1 then lxr else x1::lxr in
    let lx1, lxr =
      List.partition
	(fun x -> List.mem (Rdf.Var x) terms_with_t1)
	lxr in
    let deps1, depsr =
      List.partition
	(function
	  | [] -> false
	  | t::_ -> List.mem t terms_with_t1)
	deps in
    let deps1 = (* removing t1 from dependencies *)
      List.map
	(fun dep1 ->
	 List.filter
	   (fun t -> t <> t1)
	   dep1)
	deps1 in
    let shape1 =
      match t1 with
      | Rdf.Var x1 -> Map (x1, shape_of_deps deps1 lx1)
      | _ -> Descr (t1, shape_of_deps deps1 lx1) in
    let lshaper =
      match lxr with
      | [] -> []
      | x2::lxr -> list_shape_of_fm fm x2 lxr depsr in
    shape1::lshaper
  in
  shape_of_deps deps lx

type shape_data =
  [ `Unit
  | `Concat of shape_data list
  | `MapN of [`KeyVar | `KeyTerm] * Rdf.var option list * (Rdf.term option list * shape_data) list ]
    
let shape_data_of_results
      (shape : results_shape)
      (results : Sparql_endpoint.results)
      (k : Rdf.var option list -> shape_data -> unit) : unit =
  (* [f] stands for 'functional depth' *)
  let open Sparql_endpoint in
  let var_index = results.vars in (* assoc var -> binding index *)
  let make_concat = function
    | [] -> `Unit
    | [d] -> d
    | ld -> `Concat ld in
  let rec aux shape bindings =
    (* result: var list, solution count, functional depth, shape_data *)
    match shape with
    | Unit -> [], 1, 0, `Unit
    | Concat lsh ->
       let lv, c, f, ld =
	 List.fold_right
	   (fun sh (lv,c,f,ld) ->
	    let lvi, ci, fi, di = aux sh bindings in
	    let f = if fi = List.length lvi then fi+f else fi in
	    lvi@lv, ci*c, f, di::ld)
	   lsh ([],1,0,[]) in
       lv, c, f, `Concat ld
    | Map (v,sh) ->
       let i =
	 try List.assoc v var_index
	 with Not_found -> assert false in
       let rank = ref 0 in
       let ht = Hashtbl.create 201 in
       bindings
       |> List.iter
	    (fun binding ->
	     incr rank;
	     let t_opt = binding.(i) in
	     try
	       let first_rank, ref_t_bindings = Hashtbl.find ht t_opt in
	       ref_t_bindings := binding::!ref_t_bindings
	     with Not_found ->
	       Hashtbl.add ht t_opt (!rank, ref [binding]));
       let lv1, c, f1, rank_rows =
	 Hashtbl.fold
	   (fun t_opt (first_rank,ref_t_bindings) (lv,c,f1,rank_rows) ->
	    let lvi, ci, fi, di = aux sh (List.rev !ref_t_bindings) in (* all [lvi] are the same *)
	    enqueue_term_opt t_opt;
	    lvi, c+ci, min fi f1, (first_rank,t_opt,di)::rank_rows)
	   ht ([],0,max_int,[]) in
       let lv = Some v::lv1 in
       let f = if List.length rank_rows = 1 then 1+f1 else 0 in
       let ranked_rows = List.sort Stdlib.compare rank_rows in
       (* TODO : optimize when f=0 and f=1 *)
       let d = mapn_of_rows `KeyVar lv f1 ranked_rows in
       lv, c, f, d
    | Descr (t,sh) ->
       let lv1, c1, f1, d1 = aux sh bindings in
       enqueue_term t;
       let lv, c, f, ranked_rows = None::lv1, c1, 0 (*1+f1*), [(1, Some t, d1)] in
       let d = mapn_of_rows `KeyTerm lv f1 ranked_rows in
       lv, c, f, d
  and mapn_of_rows key lv f1 ranked_rows : shape_data =
    let lv_a, _ = Common.split_list_at lv (1+f1) in
    let rows =
      List.map
	(fun (_,t_opt,di) ->
	 let lt_a, fd_b = row_of_data f1 di in
	 match fd_b with
	 | `D d_b -> t_opt :: lt_a, d_b
	 | `F _ -> assert false)
	ranked_rows in
    `MapN (key, lv_a, rows)
  and row_of_data (f : int) (d : shape_data) : Rdf.term option list * [`F of int | `D of shape_data] =
    if f = 0
    then [], `D d
    else
      match d with
      | `Unit -> [], `F f
      | `Concat [] -> [], `F f
      | `Concat (di::ldi) ->
	 let lt1, fd1 = row_of_data f di in
	 ( match fd1 with
	   | `D d1 -> lt1, `D (make_concat (d1::ldi))
	   | `F f1 ->
	      let lt2, fd2 = row_of_data f1 (make_concat ldi) in
	      lt1 @ lt2, fd2 )
      | `MapN (key,lv,[lt1,d1]) ->
	 let n = List.length lv in
	 if f < n
	 then
	   let lv_a, lv_b = Common.split_list_at lv f in
	   let lt1_a, lt1_b = Common.split_list_at lt1 f in
	   lt1_a, `D (`MapN (`KeyVar, lv_b, [lt1_b,d1]))
	 else (* f >= n *)
	   let lt2, fd2 = row_of_data (f-n) d1 in
	   lt1 @ lt2, fd2
      | `MapN _ -> assert false
  in
  let lv, _c, _f, data = aux shape results.bindings in
  sync_terms
    (fun () -> k lv data)

		 
(* slidewhow *)
      
type slide_data = { media_uri : Rdf.uri;
		    binding_fields : (string (* var name *) * Rdf.term option) list }
      
let slides_of_results results (k : slide_data list -> unit) : unit =
  let open Sparql_endpoint in
  let rev_l =
    List.fold_left
      (fun rev_l binding ->
       Array.fold_left
	 (fun rev_l term_opt ->
	  match term_opt with
	  | Some (Rdf.URI uri)
	       when Rdf.uri_is_image uri || Rdf.uri_is_video uri ->
	     enqueue_binding_terms binding;
	     let data = { media_uri = uri;
			  binding_fields =
			    List.map
			      (fun (v,i) -> (v, binding.(i)))
			      results.vars;
			} in
	     data::rev_l
	  | _ -> rev_l)
	 rev_l binding)
      [] results.bindings
  in
  sync_terms
    (fun () -> k (List.rev rev_l))

(* geolocations *)
    
let geolocations_of_results (geolocs : (Sparql.term * (Rdf.var * Rdf.var)) list) results (k : (float * float * Rdf.term) list -> unit) : unit =
  let open Sparql_endpoint in
  let l =
    List.fold_left
      (fun data ((t : Sparql.term), (v_lat,v_long)) ->
	try
	  let i_lat = List.assoc v_lat results.vars in
	  let i_long = List.assoc v_long results.vars in
	  let get_term_opt =
	    let s = (t :> string) in
	    assert (s <> "");
	    if s.[0] = '?' then
	      let v = String.sub s 1 (String.length s - 1) in
	      let i_name = List.assoc v results.vars in
	      (fun binding -> binding.(i_name))
	    else
	      (fun binding -> None) in (* TODO *)
	  List.fold_left
	    (fun data binding ->
	      match binding.(i_lat), binding.(i_long), get_term_opt binding with
	      | Some (Rdf.Number (lat,_,_)), Some (Rdf.Number (long,_,_)), Some term ->
		 enqueue_term term;
		 (lat,long,term)::data
	      | _ -> data)
	    data results.bindings
	with Not_found ->
	  Jsutils.firebug ("Missing geoloc vars in results: " ^ v_lat ^ ", " ^ v_long);
	  data)
      [] geolocs in
  sync_terms
    (fun () -> k l)

(* external search *)

let ajax_external_search_constr ~endpoint (search : Lisql.search) (k : (Lisql.constr, exn) Result.t -> unit) : unit =
  match search with
  | WikidataSearch [] -> k (Result.Ok Lisql.True)
  | WikidataSearch kwds ->
     let query = String.concat "+" kwds in
     let limit = 30 in
     Jsutils.Wikidata.ajax_entity_search
       query limit
       (function
        | Result.Ok le ->
           let lt =
             List.map
	       (fun e ->
                 match e.[0] with
                 | 'P' ->
                    if config_nary_relations#value (* see Lisq2sparql.WhichProp/Pred *)
                    then Rdf.URI (Rdf.wikidata_prop e)
                    else Rdf.URI (Rdf.wikidata_prop_direct e)
                 | _ (* 'Q' *) -> Rdf.URI (Rdf.wikidata_entity e))
	       le in
           k (Result.Ok (Lisql.ExternalSearch (search, Some lt)))
        | (Result.Error _ as err) -> k err)
  | TextQuery [] -> k (Result.Ok Lisql.True)
  | TextQuery kwds ->
     let lucene = Jsutils.lucene_query_of_kwds kwds in
     if lucene = ""
     then k (Result.Error (Failure "The Lucene query derived from keywords is empty"))
     else (
       let sparql =
	 let x = "x" in
	 Sparql.(select
		   ~distinct:true
		   ~projections:[`Bare, x]
		   ~limit:config_max_increment_samples#value
		   (text_query (var x) lucene)) in
       Sparql_endpoint.(ajax_in (* TODO: change this function for promises *)
			  [] (new ajax_pool)
			  endpoint (sparql :> string)
			  (fun sparql results ->
			    let lt =
			      List.fold_left
				(fun lt binding ->
				  match binding with
				  | [| Some t |] -> t::lt
				  | _ -> lt)
				[] results.bindings in
			    k (Result.Ok (Lisql.ExternalSearch (search, Some lt))))
	                  (fun code ->
                            k (Result.Error (Failure ("The SPARQL query for retrieving entities matching a Lucene query failed with code " ^ string_of_int code))))))


(* hooks for Sparklis extension *)

let hook_suggestions : (freq_unit * suggestions) -> (freq_unit * suggestions) =
  let open Jsutils in
  let js_unit_suggestions_map =
    js_map
      (`Record [| "type", js_custom_spec js_freq_unit_map;
                  "suggestions", js_custom_spec js_suggestions_map |]) in
  (fun unit_suggestions ->
    Jsutils.firebug "applying hook on suggestions";
    Config.apply_hook_data
      Config.sparklis_extension##.hookSuggestions
      js_unit_suggestions_map
      unit_suggestions)

(* LIS navigation places *)
  
class place (endpoint : string) (focus : Lisql.focus) =
  let ids, focus_descr, s_annot = Lisql_annot.annot_focus focus in
  let query, path = Lisql.elt_s_path_of_focus focus in
object (self)
  (* essential state *)

  val endpoint = endpoint
  method endpoint = endpoint

  method focus : Lisql.focus = focus (* focus-centric query representation *)
  method query_annot : Lisql_annot.annot Lisql.elt_s = s_annot (* annotated query *)
  method query : unit Lisql.elt_s = query (* query *)
  method path : Lisql.path = path (* focus path *)
  method query_ids : Lisql_annot.Ids.t = ids (* defined entity ids in query *)
  method focus_entity : Lisql_annot.focus_term = focus_descr#term (* entity at focus, if any *)

  (* derived state *)

  val mutable term_hierarchy : Rdf.uri Ontology.relation = Ontology.no_relation
		   
  val mutable id_labelling = new Lisql2nl.id_labelling []
  method id_labelling = id_labelling

  val mutable s_sparql : Lisql2sparql.s_sparql =
    Lisql2sparql.({
      state = new Lisql2sparql.state (new Lisql2nl.id_labelling []);
      focus_term_opt = None;
      focus_graph_opt = None;
      focus_pred_args_opt = None;
      deps = [];
      query_opt = None;
      query_count_opt = None;
      query_class_opt = None;
      query_prop_opt = None;
      query_pred_opt = None;
      query_arg_opt = None;
      seq_view = 0, Lisql_annot.Unit })
    
  method focus_term_opt = s_sparql.Lisql2sparql.focus_term_opt
  method focus_graph_opt = s_sparql.Lisql2sparql.focus_graph_opt
  method focus_pred_args_opt = s_sparql.Lisql2sparql.focus_pred_args_opt
    
  method private init =
    begin
      term_hierarchy <- term_hierarchy_of_focus focus;
      id_labelling <- Lisql2nl.id_labelling_of_s_annot Lisql2nl.config_lang#grammar s_annot;
      s_sparql <- Lisql2sparql.s_annot id_labelling focus_descr s_annot
(*
      Jsutils.firebug ("focus_term_opt = " ^ match s_sparql.Lisql2sparql.focus_term_opt with None -> "(none)" | Some t -> Rdf.string_of_term t);
      Jsutils.firebug ("focus_graph_opt = " ^ match s_sparql.Lisql2sparql.focus_graph_opt with None -> "(none)" | Some t -> Rdf.string_of_term t);
      Jsutils.firebug ("unconstrained focus = " ^ if focus_descr#unconstrained then "yes" else "no")
*)
    end

  initializer self#init

  (* utilities *)
(*
  method private is_qualifier_property pq =
    match s_sparql.Lisql2sparql.focus_pred_args_opt with
    | None -> false
    | Some (pred,args) ->
       let open Lisql in
       match pred with
       | Class _ -> false
       | Prop _ -> false
       | SO (ps,po) -> pq <> Rdf.rdf_type && pq <> ps && pq <> po
       | EO (pe,po) -> pq <> Rdf.rdf_type && pq <> po
 *)	       

  val ajax_pool = new Sparql_endpoint.ajax_pool
  method abort_all_ajax = ajax_pool#abort_all

  (* place state *)
  val mutable current_term_constr = Lisql.True
  val mutable current_limit = config_max_results#value
                        
  (* SPARQL derived state: query and results *)
  val mutable results_ok = false (* to know whether mutable vars below are defined *)
  val mutable sparql_opt : string option = None
  val mutable results = Sparql_endpoint.empty_results
  val mutable results_shape = Unit
  val mutable results_typing : Lisql_type.datatype list array = [||]
  val mutable focus_type_constraints : Lisql_type.focus_type_constraints = Lisql_type.default_focus_type_constraints
  val mutable focus_term_index : (Rdf.term, Rdf.term) nested_int_index = new nested_int_index (* used when some focus term *)
  val mutable focus_graph_index : Rdf.term int_index = new int_index (* used when no focus_term but some focus graph *)
  val mutable focus_pred_args_index : (Rdf.term list, Rdf.term) nested_int_index = new nested_int_index (* used when some focus-pred-args *)
  val mutable some_focus_term_is_not_queryable : bool = false

                                                      
  method filter_type : Lisql.filter_type =
    let has_IRI =
      Lisql_type.(check_input_constraint focus_type_constraints.input_constr `IRI) in
    let has_Literal =
      Lisql_type.(check_input_constraint focus_type_constraints.input_constr `String) in
    match has_IRI, has_Literal with
    | true, true -> Mixed
    | true, false -> OnlyIRIs
    | false, true -> OnlyLiterals
    | false, false -> OnlyIRIs

  method ajax_sparql_results ?limit term_constr elts (k : unit -> unit) : unit =
    (* define the new SPARQL query *)
      let limit =
        match limit with
        | None -> config_max_results#value
        | Some n -> n in
      let new_sparql_opt =
        match s_sparql.Lisql2sparql.query_opt with
        | None -> None
        | Some query ->
           let ft = self#filter_type in
           let sparql_genvar = s_sparql.Lisql2sparql.state#genvar in
           let froms = Sparql_endpoint.config_default_graphs#froms in
           let sparql = query
		          ~hook:(fun tx form ->
			    let form_constr = Lisql2sparql.filter_constr_entity sparql_genvar tx term_constr ft in
			    if Lisql.hierarchy_of_focus focus = None (* TODO: improve this rough hack *)
			    then Sparql.formula_and form_constr form
			    else Sparql.formula_and form form_constr)
		          ~froms ~limit () in
           Some sparql in
      (* define the query results, and continue when ready *)
      match new_sparql_opt with
      | None ->
         results_ok <- true;
         sparql_opt <- None;
         results <- Sparql_endpoint.empty_results;
         self#define_results_views;
         k ()
      | Some sparql ->
	 Sparql_endpoint.ajax_in
           ~main_query:true (* updating YASGUI, and hooking the query and results *)
           elts ajax_pool endpoint sparql
	   (fun sparql res ->
             results_ok <- true;
             sparql_opt <- Some sparql;
	     results <- res;
             self#define_results_views;
             k ())
           (fun code ->
             (* no state update *)
             k ())


  method id_typing (id : Lisql.id) : Lisql_type.datatype list =
    try
      let v = id_labelling#get_id_var id in
      let i = List.assoc v results.Sparql_endpoint.vars in
      results_typing.(i)
    with Not_found -> (* no results *)
      Jsutils.firebug ("No datatype for id #" ^ string_of_int id);
      []

  method private define_results_views =
    (* requires results_ok = true *)
    (* update state derived from sparql and results, if not up to date *) 
    let filter_term =
      function
      | Rdf.URI uri when String.contains uri ' ' ->
         (* URIs with spaces inside are not allowed in SPARQL queries *)
         some_focus_term_is_not_queryable <- true; false
      | Rdf.Bnode _ ->
         (* blank nodes are not allowed in SPARQL queries *)
         some_focus_term_is_not_queryable <- true; false
      | (Rdf.TypedLiteral (s,_) | Rdf.PlainLiteral (s,_)) when String.length s > 100 ->
         (* long literals can clutter term suggestions and queries retrieving concept suggestions *)
         some_focus_term_is_not_queryable <- true; false
      | _ -> true in
    let mapfilter_term_opt =
      function
      | Some t -> if filter_term t then Some t else None
      | None -> None
    in
    results_shape <- Unit;
    results_typing <- [||];
    focus_term_index <- new nested_int_index;
    focus_graph_index <- new int_index;
    focus_pred_args_index <- new nested_int_index;
    some_focus_term_is_not_queryable <- false;
    (* computing derived attributes from results *)
    match sparql_opt with
    | None ->
       focus_type_constraints <-
	 Lisql_type.of_focus
	   (fun id -> Some [`IRI])
	   focus focus_descr;
       ( match s_sparql.Lisql2sparql.focus_term_opt with
	 | None -> ()
	 | Some vt -> focus_term_index <- nested_index_of_results_varterm ~filter:filter_term vt None results )
(*	| Some (Rdf.Var _) -> ()
	| Some term -> focus_term_index#add (term, (1, new int_index))
	| None -> () ); *)
    | Some sparql ->
       results_shape <- results_shape_of_deps
			  s_sparql.Lisql2sparql.deps
			  s_sparql.Lisql2sparql.state#geolocs
			  (Sparql_endpoint.results_vars results);
       Jsutils.firebug ("DEPS: " ^ Lisql2sparql.string_of_deps s_sparql.Lisql2sparql.deps);
       Jsutils.firebug ("SHAPE: " ^ string_of_results_shape results_shape);
       results_typing <- Lisql_type.of_sparql_results results;
       focus_type_constraints <-
	 Lisql_type.union_focus_type_constraints
	   focus_type_constraints
	   (Lisql_type.of_focus
	      (fun id -> Some (self#id_typing id))
	      focus focus_descr);
       (* defining focus_term_index and focus_graph_index *)
       ( match
	   (if focus_descr#unconstrained then None else s_sparql.Lisql2sparql.focus_term_opt),
	   s_sparql.Lisql2sparql.focus_graph_opt
	 with
	 | None, None -> ()
	 | None, Some vtg ->
	    focus_graph_index <- index_of_results_varterm ~filter:filter_term vtg results
	 | Some vt, vtg_opt ->
	    focus_term_index <- nested_index_of_results_varterm ~filter:filter_term vt vtg_opt results
       );
       ( match s_sparql.Lisql2sparql.focus_pred_args_opt with
	 | None -> ()
	 | Some (pred,args) ->
	    let keys_vt = List.map snd args in
	    (*		 let _ = Jsutils.firebug ("pred_args_vt: " ^ String.concat ", " (List.map Rdf.string_of_term keys_vt)) in *)
	    focus_pred_args_index <- nested_index_of_results_varterm_list
				       ~mapfilter:mapfilter_term_opt
				       keys_vt s_sparql.Lisql2sparql.focus_graph_opt results
       )

  (* the following methods are valid when results_ok = true *)
  method sparql : string option = sparql_opt
  method results = results
  method results_shape = results_shape
  method partial_results = (results.Sparql_endpoint.length = current_limit)
  method results_dim = results.Sparql_endpoint.dim
  method results_nb = results.Sparql_endpoint.length
  method results_page offset limit k = page_of_results offset limit s_sparql.Lisql2sparql.state#geolocs results k
  method results_shape_data k = shape_data_of_results results_shape results k
  method results_geolocations k = geolocations_of_results s_sparql.Lisql2sparql.state#geolocs results k
  method results_slides k = slides_of_results results k

                          
  method ajax_get_more_results ?limit term_constr elts
	   ~(k_new_results : unit -> unit)
           ~(k_trivial : unit -> unit) =
    let limit =
      match limit with
      | Some n -> n
      | None -> current_limit + config_max_results#value in
    if self#partial_results && limit > current_limit
    then self#ajax_sparql_results ~limit term_constr elts
           k_new_results
    else k_trivial ()
    
  (* counts: must be called after [ajax_sparql_results] has terminated *)
  method estimate_count_var (var : Rdf.var) : (int * bool (* partial *)) option =
    let partial = self#partial_results in
    let count_from_results () =
      (* compute from results, without AJAX call *)
      let count = count_of_results_varterm (Rdf.Var var) results in
      Some (count, partial) in
    if self#partial_results
    then (* try and get result of previous SPARQL evaluation *)
      match s_sparql.Lisql2sparql.query_count_opt with
      | None -> None (* should not happen *)
      | Some query_count ->
	 let froms = Sparql_endpoint.config_default_graphs#froms in
	 let sparql = query_count var ~froms () in
	 ( match Sparql_endpoint.cache_eval endpoint sparql with
	   | Some res -> (* reuse previous result, not partial *)
	      ( match Sparql_endpoint.float_of_results res with
		| Some f -> Some (int_of_float f, false)
		| None -> count_from_results () (* should not happen *) )
	   | None -> count_from_results () )
    else count_from_results ()
    
  method ajax_count_id (id : Lisql.id) elts
		       ~(k_count : int option -> unit) =
    match s_sparql.Lisql2sparql.query_count_opt with
    | None ->
       k_count None
    | Some query_count ->
       let var = id_labelling#get_id_var id in
       let froms = Sparql_endpoint.config_default_graphs#froms in
       let sparql : string = query_count var ~froms () in
       Sparql_endpoint.ajax_in elts ajax_pool endpoint sparql
	 (fun sparql res ->
	  let count_opt =
	    match Sparql_endpoint.float_of_results res with
	    | Some f -> Some (int_of_float f)
	    | None -> None in
	  k_count count_opt)
	 (fun code -> k_count None)
	
  (* indexes: must be called in the continuation of [ajax_sparql_results] *)

  method private ajax_forest_terms_init ?(freq0 = false) ~(inverse : bool) constr elts (k : (suggestions, exn) Result.t -> unit) =
    let process results_term =
      let list_term = list_of_results_column "term" results_term in
      let value = if freq0 then 0 else 1 in
      let max_value = None in
      let partial = results_term.Sparql_endpoint.length = config_max_results#value in
      let unit = Results in
      let incr_index = new incr_freq_tree_index term_hierarchy in
      List.iter
	(fun t ->
	 enqueue_term t;
	 (match t with Rdf.URI uri -> term_hierarchy#enqueue uri | _ -> ());
	 incr_index#add (Lisql.IncrTerm t, Some { value; max_value; partial; unit }))
	list_term;
      (* synchronizing hierarchies and lexicons and continuing *)
      sync_terms (* datatypes and entities *)
	(fun () ->
	 term_hierarchy#sync
	   (fun () ->
             let forest = incr_index#filter_map_forest ~inverse (fun x -> Some x) in
             let suggestions = {partial; forest} in
             let _, suggestions = hook_suggestions (Entities, suggestions) in
	     k (Result.Ok suggestions)))
    in
    let sparql_genvar = new Lisql2sparql.genvar in
    let sparql_term =
      Sparql.((select
                 ~froms:Sparql_endpoint.config_default_graphs#froms
                 ~distinct:true
                 ~projections:[`Bare, "term"]
                 ~limit:config_max_results#value
                 (join [ pattern_of_formula (Lisql2sparql.search_constr_entity sparql_genvar (var "term") constr OnlyIRIs);
                         pattern_hidden_URIs "term";
                         filter (log_not (expr_func "isBlank" [var "term"])) ])
               :> string)) in
    Sparql_endpoint.ajax_in ~tentative:true elts ajax_pool endpoint sparql_term (* tentative because uses a non-standard feature 'bif:contains' *)
      (fun _ results_term -> process results_term)
      (fun code -> k (Result.Error (Failure ("Initial term suggestions: HTTP error code " ^ string_of_int code))))

  method ajax_forest_terms_inputs_ids ?(inverse = false) constr elts (k : (suggestions, exn) Result.t -> unit) =
    if focus_descr#term = `Undefined then
      k (Result.Ok ({partial = false; forest = []}))
    else if focus_descr#unconstrained then
      self#ajax_forest_terms_init ~inverse constr elts k
    else if focus_term_index#is_empty
            (* except when it is expected to have an empty term index *)
            && not (some_focus_term_is_not_queryable
                    || Lisql.is_undef_expr_focus focus) then
      (* typically, when no match for query+constr, then show constr match with freq=0 *)
      self#ajax_forest_terms_init ~freq0:true ~inverse constr elts k
    else
      let process () =
        let max_value = None (*Some self#results_nb*) in
        let partial = self#partial_results in
        let unit = Results in
        let incr_index = new incr_freq_tree_index term_hierarchy in
        (* adding selection increments *)
        incr_index#add (Lisql.IncrSelection (NAndSel, []), None);
        incr_index#add (Lisql.IncrSelection (NOrSel, []), None);
        (* adding increment 'anything' *)
        if focus_term_index#length > 1 && Lisql.insert_increment Lisql.IncrAnything focus <> None then
	  incr_index#add (Lisql.IncrAnything, None);
        (* adding term increments *)
        focus_term_index#iter (*rev_map*)
	  (fun (t, (freq,_)) ->
	    enqueue_term t;
	    (match t with Rdf.URI uri -> term_hierarchy#enqueue uri | _ -> ());
	    incr_index#add (Lisql.IncrTerm t, Some { value=freq; max_value; partial; unit }));
        (* adding input increments *)
        if Lisql.is_undef_expr_focus focus then
	  List.iter
	    (fun (dt : Lisql.input_type) ->
	      if Lisql_type.is_insertable_input (Lisql_type.of_input_type dt) focus_type_constraints then
	        incr_index#add (Lisql.IncrInput ("",dt), None))
	    [IRIInput; StringInput; FloatInput; IntegerInput; DateInput; TimeInput; DateTimeInput; DurationInput];
        (* adding ids *)
        ( match s_sparql.Lisql2sparql.focus_term_opt with
          | Some term ->
	     if focus_descr#incr then
	       begin
	         let dim = results.Sparql_endpoint.dim in
	         let vars = results.Sparql_endpoint.vars in
	         let freqs = Array.make dim 0 in
	         List.iter
	           (fun binding ->
		     let t_focus_opt =
		       match term with
		       | Rdf.Var v -> (try binding.(List.assoc v vars) with Not_found -> None)
		       | t -> Some t in
		     Array.iteri
		       (fun i t_opt ->
		         match t_opt, t_focus_opt with
		         | Some t1, Some t2 when t1=t2 -> freqs.(i) <- freqs.(i) + 1
		         | _ -> ())
		       binding)
	           results.Sparql_endpoint.bindings;
	         List.iter
	           (fun i ->
		     if freqs.(i) <> 0 then
		       let v = try Common.list_rev_assoc i vars with _ -> assert false in
		       if term <> (Rdf.Var v) then
		         (try
		            let id = id_labelling#get_var_id v in
		            incr_index#add (Lisql.IncrId (id, None), Some { value=freqs.(i); max_value; partial; unit })
		          with _ -> ()))  (* ex: aggregation variables *)
	           (Common.from_downto (dim-1) 0)
	       end;
	     if Lisql.is_undef_expr_focus focus then
	       begin
	         List.iter
	           (fun id -> (* TODO: filter according to empirical type *)
		     let ldt = self#id_typing id in
		     let comp_arg, comp_res =
		       Lisql_type.compatibles_insertion_list
		         (List.map (fun dt -> (None,dt)) ldt)
		         focus_type_constraints in
		     if comp_res.Lisql_type.bool then
		       incr_index#add (Lisql.IncrId (id, comp_res.Lisql_type.conv_opt), None))
	           (Lisql_annot.seq_view_defs s_sparql.Lisql2sparql.seq_view)
	       end
          | _ -> () );
        (* synchronizing hierarchies and lexicons and continuing *)
        sync_terms (* datatypes and entities *)
	  (fun () ->
	    term_hierarchy#sync
	      (fun () ->
                let forest = incr_index#filter_map_forest ~inverse (fun x -> Some x) in
                let suggestions = {partial; forest} in
                let _, suggestions = hook_suggestions (Entities, suggestions) in
	        k (Result.Ok suggestions)))
      in
      if constr = current_term_constr
      then process ()
      else self#ajax_sparql_results constr elts
             (fun () -> process ())

  method private ajax_forest_properties_init ?(freq0=false) ~(inverse : bool) constr elts (k : (suggestions, exn) Result.t -> unit) =
    let process results_class results_prop results_pred =
      let max_value = None in
      let partial_class = results_class.Sparql_endpoint.length = config_max_classes#value in
      let partial_prop = results_prop.Sparql_endpoint.length = config_max_properties#value in
      let partial_pred = results_pred.Sparql_endpoint.length = config_max_properties#value in
      let partial = partial_class || partial_prop || partial_pred in
      let unit = Entities in
      let int_index_class = index_of_results_varterm_list (List.map (fun v -> Rdf.Var v) Lisql2sparql.WhichClass.pattern_vars) results_class in
      let int_index_prop = index_of_results_varterm_list (List.map (fun v -> Rdf.Var v) Lisql2sparql.WhichProp.pattern_vars) results_prop in
      let int_index_pred = index_of_results_varterm_list (List.map (fun v -> Rdf.Var v) Lisql2sparql.WhichPred.pattern_vars) results_pred in
      let incr_index = new incr_freq_tree_index term_hierarchy in
      int_index_class#iter
	(fun (lt, count) ->
	 List.iter
	   (function
	     | Some (Rdf.URI uri) ->
		Ontology.enqueue_class uri;
		Lexicon.enqueue_class uri
	     | _ -> ())
	   lt;
	 let freq = { value=(if freq0 then 0 else count); max_value; partial=partial_class; unit } in
	 Lisql2sparql.WhichClass.increments_of_terms ~init:true lt |>
	   List.iter
	     (fun incr -> incr_index#add (incr, Some freq)));
      int_index_prop#iter
	(fun (lt, count) ->
	 List.iter
	   (function
	     | Some (Rdf.URI uri) ->
		Ontology.enqueue_property uri;
		Lexicon.enqueue_property uri
	     | _ -> ())
	   lt;
	 let freq = { value=(if freq0 then 0 else count); max_value; partial=partial_prop; unit } in
	 Lisql2sparql.WhichProp.increments_of_terms ~init:true lt |>
	   List.iter
	     (fun incr -> incr_index#add (incr, Some freq)));
      int_index_pred#iter
	(fun (lt, count) ->
	 List.iter
	   (function
	     | Some (Rdf.URI p) ->
		Ontology.enqueue_pred p;
		Lexicon.enqueue_property p
	     | _ -> ()) lt;
	 let freq = { value=(if freq0 then 0 else count); max_value; partial=partial_pred; unit } in
	 Lisql2sparql.WhichPred.increments_of_terms ~init:true lt |>
	   List.iter
	     (fun incr ->
	      incr_index#add (incr, Some freq);
	      Lisql2sparql.WhichPred.increments_hidden_by_increment ~init:true incr |>
		List.iter incr_index#remove));
      (* adding other increments *)
      if not freq0 then (
	incr_index#add (Lisql.IncrTriple Lisql.S, None);
	incr_index#add (Lisql.IncrTriple Lisql.O, None)
      );
      sync_concepts (fun () ->
          let forest = incr_index#filter_map_forest ~inverse (fun x -> Some x) in
          let suggestions = {partial; forest} in
          let _, suggestions = hook_suggestions (Concepts, suggestions) in
	  k (Result.Ok suggestions))
    in
    let ajax_extent () =
      let sparql_genvar = new Lisql2sparql.genvar in
      let froms = Sparql_endpoint.config_default_graphs#froms in
      let graph_opt (gp : Sparql.pattern) : Sparql.pattern =
	match s_sparql.Lisql2sparql.focus_graph_opt with
	| Some _ when not focus_graph_index#is_empty ->
	   Sparql.union (focus_graph_index#filter_map_list (fun (tg,_) -> Some (Sparql.graph (Sparql.term tg) gp)))
	| _ -> gp
      in
      let make_sparql lv (make_pattern : ?hook:(string Lisql2sparql.formula_hook) -> unit -> Sparql.pattern) filter_constr config_max =
	let _ = assert (lv <> []) in
	let hook v form =
	  Sparql.formula_and_list
	    [formula_concept_profile v;
	     filter_constr sparql_genvar (Sparql.var v) constr;
	     form;
             formula_hidden_URIs v] in
	let g_pat = graph_opt (make_pattern ~hook ()) in
	Sparql.((select
		  ~froms
		  ~distinct:true
		  ~projections:(List.map (fun v -> `Bare, v) lv)
		  ~limit:config_max#value
                  g_pat
                (*		  (join (g_pat :: List.map (fun v -> pattern_hidden_URIs v) lv)) *)
	         :> string)) in
      let sparql_class = make_sparql
			   Lisql2sparql.WhichClass.pattern_vars
			   (fun ?hook () -> Lisql2sparql.WhichClass.pattern_of_term ?hook None)
			   Lisql2sparql.filter_constr_class
			   config_max_classes in
      let sparql_prop = make_sparql
			  Lisql2sparql.WhichProp.pattern_vars
			  (fun ?hook () -> Lisql2sparql.WhichProp.pattern_of_term ?hook None)
			  Lisql2sparql.filter_constr_property
			  config_max_properties in
      let sparql_pred =
	if config_nary_relations#value
	then make_sparql
	       Lisql2sparql.WhichPred.pattern_vars
	       (fun ?hook () -> Lisql2sparql.WhichPred.pattern_of_term ?hook None)
	       Lisql2sparql.filter_constr_property
	       config_max_properties
	else "" in
      Sparql_endpoint.ajax_list_in elts ajax_pool endpoint [sparql_class; sparql_prop; sparql_pred]
	(function
	| [results_class; results_prop; results_pred] -> process results_class results_prop results_pred
	| _ -> assert false)
	(fun code -> k (Result.Error (Failure ("Initial concept suggestions: HTTP error code " ^ string_of_int code))))
    in
    let ajax_intent () =
      let sparql_genvar = new Lisql2sparql.genvar in
      let froms = Sparql_endpoint.config_schema_graphs#froms in
      let make_sparql lv (make_pattern : ?hook:(string Lisql2sparql.formula_hook) -> unit -> Sparql.pattern) filter_constr config_max =
	let _ = assert (lv <> []) in
	let hook v form =
	  Sparql.formula_and_list
	    [ formula_concept_profile v;
	      filter_constr sparql_genvar (Sparql.var v) constr;
	      form;
              formula_hidden_URIs v ] in
	let pat = make_pattern ~hook () in
	Sparql.((select
		  ~froms
		  ~distinct:true
		  ~projections:(List.map (fun v -> `Bare, v) lv)
		  ~limit:config_max#value
                  pat
                 (*		  (join (pat :: List.map (fun v -> pattern_hidden_URIs v) lv))*)
		 :> string)) in
      let sparql_class = make_sparql
			   Lisql2sparql.WhichClass.pattern_vars
			   (fun ?hook () -> Lisql2sparql.WhichClass.intent_pattern ?hook ())
			   Lisql2sparql.filter_constr_class
			   config_max_classes in
      let sparql_prop = make_sparql
			  Lisql2sparql.WhichProp.pattern_vars
			  (fun ?hook () -> Lisql2sparql.WhichProp.intent_pattern ?hook ())
			  Lisql2sparql.filter_constr_property
			  config_max_properties in
      let sparql_pred =
	if config_nary_relations#value
	then make_sparql
	       Lisql2sparql.WhichPred.pattern_vars
	       (fun ?hook () -> Lisql2sparql.WhichPred.intent_pattern ?hook ())
	       Lisql2sparql.filter_constr_property
	       config_max_properties
	else "" in
      Sparql_endpoint.ajax_list_in ~tentative:true elts ajax_pool endpoint [sparql_class; sparql_prop; sparql_pred]
	(function
	  | [results_class; results_prop; results_pred] ->
             (*if partial && List.for_all Sparql_endpoint.results_are_empty lres
             then ajax_extent () (* looking at facts *)
	     else*) (* rather rely on configuration to choose extent/intent *)
             process results_class results_prop results_pred
	  | _ -> assert false)
        (fun code -> k (Result.Error (Failure ("Initial concept suggestions: HTTP error code " ^ string_of_int code))))
    in
    let process_wikidata results_class =
      let max_value = None in
      let partial = results_class.Sparql_endpoint.length = config_max_classes#value in
      let unit = Entities in
      let int_index_class = index_of_results_varterm_list_count [Rdf.Var "c"] "n" results_class in
      let incr_index = new incr_freq_tree_index term_hierarchy in
      int_index_class#iter
	(fun (lt, count) ->
	 List.iter
	   (function
	     | Some (Rdf.URI uri) ->
		Ontology.enqueue_class uri;
		Lexicon.enqueue_class uri
	     | _ -> ())
	   lt;
	 let freq = { value=(if freq0 then 0 else count); max_value; partial=false; unit } in
	 Lisql2sparql.WhichClass.increments_of_terms ~init:true lt |>
	   List.iter
	     (fun incr -> incr_index#add (incr, Some freq)));
      sync_concepts (fun () ->
          let forest = incr_index#filter_map_forest ~inverse (fun x -> Some x) in
          let suggestions = {partial; forest} in
          let _, suggestions = hook_suggestions (Concepts, suggestions) in
	  k (Result.Ok suggestions)) in
    let process_wikidata_with_external_search (lx : Rdf.var list) (ltq : Rdf.term list) (ltp : Rdf.term list) results_class =
      let freq = { value=(if freq0 then 0 else 1); max_value=None; partial=true; unit=Entities } in
      let incr_index = new incr_freq_tree_index term_hierarchy in
      let open Sparql_endpoint in
      (* adding class increments *)
      ( match results_class.bindings with
	| binding::_ -> (* LIMIT 1 => at most one binding *)
	   List.iter2
	     (fun x t ->
	      try
		let pos = List.assoc x results_class.vars in
		match t, binding.(pos) with
		| Rdf.URI uri, Some _ -> (* if some instance was found for t *)
		   Ontology.enqueue_class uri;
		   Lexicon.enqueue_class uri;
		   Lisql2sparql.WhichClass.increments_of_terms ~init:true [Some t] |>
		     List.iter
		       (fun incr -> incr_index#add (incr, Some freq))
		| _ -> ()
	      with Not_found -> assert false)
	     lx ltq
	| _ -> () );
      (* adding property increments *)
      List.iter
        (fun t ->
          match t with
          | Rdf.URI uri ->
             Ontology.enqueue_property uri;
             Lexicon.enqueue_property uri;
             let incrs =
               if config_nary_relations#value
               then
                 let uri_stat = Rdf.wikidata_rebase uri Rdf.wikidata_prop_base Rdf.wikidata_prop_statement_base in
                 Lisql2sparql.WhichPred.increments_of_terms ~init:true [Some t; None; Some (Rdf.URI uri_stat); None]
               else Lisql2sparql.WhichProp.increments_of_terms ~init:true [Some t; None] in
             List.iter
               (fun incr -> incr_index#add (incr, Some freq))
               incrs
          | _ -> ())
        ltp;
      sync_concepts (fun () ->
          let forest = incr_index#filter_map_forest ~inverse (fun x -> Some x) in
          let suggestions = {partial = true; forest} in
          let _, suggestions = hook_suggestions (Concepts, suggestions) in
	  k (Result.Ok suggestions))
    in
    let ajax_wikidata () =
      (* NOTE: pat+constraint does not work on wikidata, don't know why *)
      let sparql_class, lt_opt =
	let open Sparql in
	match constr with
	| Lisql.True ->
           Sparql.((select
                      ~distinct:true
                      ~projections:[`Bare, "c"; `Aggreg (COUNT, (var "x" :> term)), "n"]
                      ~froms:Sparql_endpoint.config_default_graphs#froms
                      ~groupings:[var "c"]
                      ~orderings:[DESC (fun e -> e), var "n"]
                      ~limit:1000
                      (rdf_type (var "x") (var "c"))
                    :> string)),
           None
	| Lisql.ExternalSearch (_, Some lt) ->
           let ltq, ltp = (* separating Qxxx and Pxxx *)
             List.partition
               (function
                | Rdf.URI uri -> Common.has_prefix uri Rdf.wikidata_entity_base
                | _ -> true) (* should not happen *)
             lt in
	   let lx = List.mapi (fun i t -> "x" ^ string_of_int (i+1)) ltq in
           Sparql.((select
                      ~distinct:false
                      ~projections:(List.map (fun x -> `Bare, x) lx)
                      ~froms:Sparql_endpoint.config_default_graphs#froms
                      ~limit:1
                      (join
                         (List.map2
                            (fun x t -> optional (rdf_type (var x) (term t)))
                            lx ltq))
                    :> string)),
           Some (lx,ltq,ltp)
	| _ -> "", None in (* avoiding timeouts in evaluations *)
      Jsutils.firebug sparql_class;
      if sparql_class = ""
      then k (Result.Error (Failure "Initial concept suggestions: only external constraints are supported on Wikidata"))
      else
	Sparql_endpoint.ajax_list_in
	  elts ajax_pool endpoint [sparql_class]
	  (function
	    | [results_class] ->
	       ( match lt_opt with
		 | Some (lx,ltq,ltp) -> process_wikidata_with_external_search lx ltq ltp results_class
		 | None -> process_wikidata results_class )
	    | _ -> assert false)
	  (fun code -> k (Result.Error (Failure ("Initial concept suggestions: HTTP error code " ^ string_of_int code))))
    in
    if Rdf.config_wikidata_mode#value
    then ajax_wikidata ()
    else
      if config_intentional_init_concepts#value && s_sparql.Lisql2sparql.focus_graph_opt = None
      then ajax_intent ()
      else ajax_extent ()

  method ajax_forest_properties ?(inverse = false) constr elts (k : (suggestions, exn) Result.t -> unit) =
    if (focus_descr#term = `Undefined && focus_descr#pred_args = `Undefined) || not focus_descr#incr then
      k (Result.Ok {partial = false; forest = []}) (* only constraints on aggregations (HAVING clause) *)
    else if focus_descr#unconstrained then
      self#ajax_forest_properties_init ~inverse constr elts k
    else begin
        let hierarchy_focus_as_incr_opt =
          let open Lisql in
          match focus with
          | AtS1 (np, RelX (p,ori,ctx)) ->
	     Some (IncrRel (p,ori))
          | AtS1 (_np, CConsX1 ((S|O as _argo), CNil _, PredX ((S|O as args), pred, _ctx))) ->
	     Some (IncrPred (args, pred))
          | AtSn (_cp, PredX ((S|O as args), pred, _ctx)) ->
	     Some (IncrPred (args, pred))
          | _ -> None in
        let process ~max_value_term ~max_value_arg ~partial ~unit results_class results_prop results_pred results_arg =
          let partial_class = partial || results_class.Sparql_endpoint.length = config_max_classes#value in
          let partial_prop = partial || results_prop.Sparql_endpoint.length = config_max_properties#value in
          let partial_pred = partial || results_pred.Sparql_endpoint.length = config_max_properties#value in
          let partial_arg = partial || results_arg.Sparql_endpoint.length = config_max_properties#value in
          let partial = partial_class || partial_prop || partial_pred || partial_arg in
          let int_index_class = index_of_results_varterm_list (List.map (fun v -> Rdf.Var v) Lisql2sparql.WhichClass.pattern_vars) results_class in
          let int_index_prop = index_of_results_varterm_list (List.map (fun v -> Rdf.Var v) Lisql2sparql.WhichProp.pattern_vars) results_prop in
          let int_index_pred = index_of_results_varterm_list (List.map (fun v -> Rdf.Var v) Lisql2sparql.WhichPred.pattern_vars) results_pred in
          let int_index_arg = index_of_results_varterm_list (List.map (fun v -> Rdf.Var v) Lisql2sparql.WhichArg.pattern_vars) results_arg in
          if constr <> Lisql.True
	     && int_index_class#is_empty
	     && int_index_prop#is_empty
	     && int_index_pred#is_empty
	     && int_index_arg#is_empty
          then self#ajax_forest_properties_init ~freq0:true ~inverse constr elts k
          else (
            let incr_index = new incr_freq_tree_index term_hierarchy in
            let incr_sim_ok = config_incr_sim#value && Lisql.(insert_sim (Prop "dummy") S O focus) <> None in
            let trans_rel = ref false in
            let fwd_prop = ref false in
            let bwd_prop = ref false in
            (* adding selection increments *)
            incr_index#add (Lisql.IncrSelection (AndSel, []), None);
            incr_index#add (Lisql.IncrSelection (OrSel, []), None);
            (* adding class increments *)
            int_index_class#iter
	      (fun (lt, count) ->
	        List.iter
	          (function
	           | Some (Rdf.URI uri) ->
		      Ontology.enqueue_class uri;
		      Lexicon.enqueue_class uri
	           | _ -> ())
	          lt;
	        Lisql2sparql.WhichClass.increments_of_terms ~init:false lt |>
	          List.iter
	            (fun incr -> incr_index#add (incr, Some { value=count; max_value=max_value_term; partial=partial_class; unit })));
            (* adding property increments + hierarchy + LatLong *)
            int_index_prop#iter
	      (fun (lt,count) ->
	        List.iter
	          (function
	           | Some (Rdf.URI uri) ->
		      Ontology.enqueue_property uri;
		      Lexicon.enqueue_property uri
	           | _ -> ())
	          lt;
	        let freq_opt = Some { value=count; max_value=max_value_term; partial=partial_prop; unit } in
	        Lisql2sparql.WhichProp.increments_of_terms ~init:false lt |>
	          List.iter
	            (fun incr ->
	              incr_index#add (incr, freq_opt);
	              if Some incr = hierarchy_focus_as_incr_opt then
		        trans_rel := true;
	              ( match incr with
		        | Lisql.IncrRel (p,ori) ->
		           ( match ori with
		             | Lisql.Fwd -> fwd_prop := true
		             | Lisql.Bwd -> bwd_prop := true );
		           if p = Rdf.rdf_first then
		             incr_index#add (Lisql.IncrRel (Rdf.rdf_item, ori), freq_opt);
		           if incr_sim_ok then (
		             let inv_incr = Lisql.IncrRel (p, Lisql.inverse_orientation ori) in
		             ( match incr_index#get inv_incr with
		               | None -> ()
		               | Some inv_freq_opt ->
			          let fwd_freq_opt, bwd_freq_opt =
			            match ori with
			            | Lisql.Fwd -> freq_opt, inv_freq_opt
			            | Lisql.Bwd -> inv_freq_opt, freq_opt in
			          incr_index#add (Lisql.(IncrSim(Prop p,S,O)), fwd_freq_opt);
			          incr_index#add (Lisql.(IncrSim(Prop p,O,S)), bwd_freq_opt))
		           )
		        | _ -> () );
	              ( match Lisql.latlong_of_increment incr with
		        | Some ll -> incr_index#add (Lisql.IncrLatLong ll, freq_opt)
		        | None -> () )));
            (* adding pred+arg increments *)
            int_index_pred#iter
	      (fun (lt, count) ->
	        List.iter
	          (function
	           | Some (Rdf.URI p) ->
		      Ontology.enqueue_pred p;
		      Lexicon.enqueue_property p
	           | _ -> ()) lt;
	        let freq_opt = Some { value=count; max_value=max_value_term; partial=partial_pred; unit } in
	        Lisql2sparql.WhichPred.increments_of_terms ~init:false lt |>
	          List.iter
	            (fun incr ->
	              incr_index#add (incr, freq_opt);
	              if Some incr = hierarchy_focus_as_incr_opt then
		        trans_rel := true;
	              ( match incr with
		        | Lisql.IncrPred ((Lisql.S | Lisql.O as arg),pred) ->
		           if incr_sim_ok then (
		             let inv_arg =
		               match arg with
		               | Lisql.S -> Lisql.O
		               | Lisql.O -> Lisql.S
		               | _ -> assert false in
		             let inv_incr = Lisql.IncrPred (inv_arg,pred) in
		             ( match incr_index#get inv_incr with
		               | None -> ()
		               | Some inv_freq_opt ->
			          let fwd_freq_opt, bwd_freq_opt =
			            match arg with
			            | Lisql.S -> freq_opt, inv_freq_opt
			            | Lisql.O -> inv_freq_opt, freq_opt
			            | _ -> assert false in
			          incr_index#add (Lisql.(IncrSim(pred,S,O)), fwd_freq_opt);
			          incr_index#add (Lisql.(IncrSim(pred,O,S)), bwd_freq_opt))
		           )
		        | _ -> () );
	              ( match Lisql.latlong_of_increment incr with
		        | Some ll -> incr_index#add (Lisql.IncrLatLong ll, freq_opt)
		        | None -> () );
	              Lisql2sparql.WhichPred.increments_hidden_by_increment ~init:false incr |>
	                List.iter incr_index#remove));
            int_index_arg#iter
	      (fun (lt,count) ->
	        List.iter
	          (function
	           | Some (Rdf.URI uri) ->
		      Ontology.enqueue_arg uri;
		      Lexicon.enqueue_arg uri
	           | _ -> ())
	          lt;
	        let freq_opt = Some { value=count; max_value=max_value_arg; partial=partial_arg; unit } in
	        Lisql2sparql.WhichArg.increments_of_terms lt |>
	          List.iter
	            (fun incr -> incr_index#add (incr,freq_opt)));
            (* adding hierarchy increments *)
            if !trans_rel then
	      List.iter
	        (fun incr ->
	          if Lisql.insert_increment incr focus <> None
	          then incr_index#add (incr,None))
	        [Lisql.IncrHierarchy true];
            (* adding other increments *)
            if !fwd_prop then incr_index#add (Lisql.IncrTriple Lisql.S, None);
            if !bwd_prop then incr_index#add (Lisql.IncrTriple Lisql.O, None);
            List.iter
	      (fun incr ->
	        if Lisql.insert_increment incr focus <> None
	        then incr_index#add (incr,None))
	      [Lisql.IncrInWhichThereIs (* should check that some focus values are named graphs *)];
            sync_concepts (fun () ->
                let forest = incr_index#filter_map_forest ~inverse (fun x -> Some x) in
                let suggestions = {partial; forest} in
                let _, suggestions = hook_suggestions (Concepts, suggestions) in
	        k (Result.Ok suggestions)))
        in
        let sparql_genvar = s_sparql.Lisql2sparql.state#genvar in
        let froms = Sparql_endpoint.config_default_graphs#froms in
        let ajax_intent () =
          (* focus_term_index is not empty *)
          let max_value_term, max_value_arg = None, None in
          let partial = self#partial_results in
          let unit = Results in
          let make_sparql (query_opt : Lisql2sparql.template option) filter_constr config_max =
	    match query_opt with
	    | None -> ""
	    | Some query ->
	       query
	         ~hook:(fun tx form ->
		   Sparql.formula_and_list
		     [formula_concept_profile_term tx;
		      filter_constr sparql_genvar tx constr;
                      form;
		      formula_hidden_URIs_term tx])
	         ~froms ~limit:config_max#value () in
          let sparql_class = make_sparql
		               s_sparql.Lisql2sparql.query_class_opt
		               Lisql2sparql.filter_constr_class
		               config_max_classes in
          let sparql_prop =
	    if Rdf.config_wikidata_mode#value && config_nary_relations#value
	    then ""
	    else make_sparql
	           s_sparql.Lisql2sparql.query_prop_opt
	           Lisql2sparql.filter_constr_property
	           config_max_properties in
          let sparql_pred =
	    if config_nary_relations#value
	    then make_sparql
	           s_sparql.Lisql2sparql.query_pred_opt
	           Lisql2sparql.filter_constr_property
	           config_max_properties
	    else "" in
          let sparql_arg = make_sparql
			     s_sparql.Lisql2sparql.query_arg_opt
			     Lisql2sparql.filter_constr_property
			     config_max_properties in
          Sparql_endpoint.ajax_list_in elts ajax_pool endpoint [sparql_class; sparql_prop; sparql_pred; sparql_arg]
	    (function
	     | [results_class; results_prop; results_pred; results_arg] ->
		process ~max_value_term ~max_value_arg ~partial ~unit results_class results_prop results_pred results_arg
	     | _ -> assert false)
	    (fun code -> k (Result.Error (Failure ("Concept suggestions: HTTP error code " ^ string_of_int code))))
        in
        let ajax_extent () =
          (* focus_term_index is not empty *)
          let sparql_genvar = new Lisql2sparql.genvar in
          let nb_samples_term, samples_term =
	    focus_term_index#sample_list config_max_increment_samples#value
	      (fun (t,(f,graph_index)) -> ([t],(f,graph_index))) in
          let max_value_term = Some nb_samples_term in
          let partial = self#partial_results || nb_samples_term < focus_term_index#length in
          let unit = Entities in
          let make_sparql ((nb_samples, samples) : int * (Rdf.term list * (int * Rdf.term int_index)) list) config_max filter_constr (lv : Rdf.var list) (make_pattern : ?hook:(string Lisql2sparql.formula_hook) -> Rdf.term list -> Sparql.pattern (* maybe empty *)) =
	    assert (lv <> []);
	    match samples with
	    | [] -> ""
	    | (key0, (_, graph_index0))::_ ->
	       let projections = List.map (fun v -> `Bare, v) lv in
               if not Rdf.config_wikidata_mode#value (* not in Wikidata *)
                  && not config_avoid_lengthy_queries#value (* lengthy queries OK *)
                  && config_concept_profile#value = "" (* no profile *)
                  && constr = Lisql.True (* no constraint *)
               then (* use this to have a better sample of properties *)
	         let graph_opt (graph_index : Rdf.term int_index) (gp : Sparql.pattern) : Sparql.pattern =
		   if gp = Sparql.empty then gp
                   else
                     match s_sparql.Lisql2sparql.focus_graph_opt with
		     | Some _ when not graph_index#is_empty ->
		        Sparql.union (graph_index#filter_map_list (fun (tg,_) -> Some (Sparql.graph (Sparql.term tg) gp)))
		     | _ -> gp
	         in
	         Sparql.((select
		            ~froms
                            ~projections
                            ~limit:(config_max#value * min 10 nb_samples)
                            (join
                               (union
		                  (List.map
		                     (fun (key,(_, graph_index)) ->
		                       let pat = graph_opt graph_index (make_pattern ?hook:None key) in
		                       if pat = Sparql.empty then pat
		                       else subquery
			                      (select
			                         ~distinct:true ~projections
			                         ~limit:config_max#value
			                         pat))
		                     samples)
                                :: List.map (fun v -> pattern_hidden_URIs v) lv))
                          :> string))
               else (* use this to avoid Garguanta queries (repeats of filters) *)
	         let key_vars = List.map (fun _ -> sparql_genvar#new_var "key") key0 in
	         let graph_var_opt =
		   match s_sparql.Lisql2sparql.focus_graph_opt with
		   | Some _ when not graph_index0#is_empty -> Some (sparql_genvar#new_var "graph")
		   | _ -> None in
	         let pat_values =
		   match graph_var_opt with
		   | None ->
		      Sparql.(values_tuple
			        (List.map Sparql.var key_vars)
			        (List.map
				   (fun (key,_) -> List.map Sparql.term key)
				   samples))
		   | Some gv ->
		      Sparql.(values_tuple
			        (List.map Sparql.var (gv::key_vars))
			        (List.concat
				   (List.map
				      (fun (key,(_, graph_index)) ->
				        (graph_index : Rdf.term int_index)#filter_map_list
				          (fun (tg,_) -> Some (List.map Sparql.term (tg::key) : Sparql.term list)))
				      samples))) in
	         let pat_incr =
	           let hook v form =
	             Sparql.formula_and_list
	               [formula_concept_profile v;
	                filter_constr sparql_genvar (Sparql.var v) constr;
	                form;
                        formula_hidden_URIs v] in
		   let pat = make_pattern ~hook (List.map (fun v -> Rdf.Var v) key_vars) in
		   if pat = Sparql.empty then pat
                   else
                     match graph_var_opt with
		     | None -> pat
		     | Some gv -> Sparql.(graph (var gv) pat) in
                 if pat_incr = Sparql.empty then (Sparql.empty :> string)
                 else
                   Sparql.((select
		              ~froms
			      ~distinct:true
			      ~projections:(List.map (fun k -> `Bare, k) key_vars @ projections)
                              ~limit:(config_max#value * min 10 nb_samples)
			      (join [pat_values; pat_incr])
                            :> string))
          in
          let sparql_class =
	    make_sparql (nb_samples_term, samples_term)
	      config_max_classes Lisql2sparql.filter_constr_class
	      Lisql2sparql.WhichClass.pattern_vars
	      (fun ?hook lt ->
		assert (lt<>[]);
		Lisql2sparql.WhichClass.pattern_of_term ?hook (Some (List.hd lt))) in
          let sparql_prop =
	    if Rdf.config_wikidata_mode#value && config_nary_relations#value
	    then ""
	    else make_sparql (nb_samples_term, samples_term)
		   config_max_properties Lisql2sparql.filter_constr_property
		   Lisql2sparql.WhichProp.pattern_vars
		   (fun ?hook lt ->
		     assert (lt<>[]);
		     Lisql2sparql.WhichProp.pattern_of_term ?hook (Some (List.hd lt))) in
          let sparql_pred =
	    if config_nary_relations#value
	    then make_sparql (nb_samples_term, samples_term)
		   config_max_properties Lisql2sparql.filter_constr_property
		   Lisql2sparql.WhichPred.pattern_vars
		   (fun ?hook lt ->
		     assert (lt<>[]);
		     Lisql2sparql.WhichPred.pattern_of_term ?hook (Some (List.hd lt)))
	    else "" in
          let max_value_arg, sparql_arg =
	    match s_sparql.Lisql2sparql.focus_pred_args_opt with
	    | None
	      | Some ((Lisql.Class _ | Lisql.Prop _),_) -> None, "" (* non-reified predicates *)
	    | Some (pred,args) ->
	       let nb_samples_arg, samples_arg =
	         focus_pred_args_index#sample_list config_max_increment_samples#value
		   (fun lt_v -> lt_v) in
	       Some nb_samples_arg,
	       make_sparql (nb_samples_arg, samples_arg)
		 config_max_properties Lisql2sparql.filter_constr_property
		 Lisql2sparql.WhichArg.pattern_vars
		 (fun ?hook lt ->
		   let args = List.map2 (fun (arg,_) t -> (arg,t)) args lt in
		   Lisql2sparql.WhichArg.pattern_of_pred_args ?hook pred args) in
          Sparql_endpoint.ajax_list_in elts ajax_pool endpoint [sparql_class; sparql_prop; sparql_pred; sparql_arg]
	    (function
	     | ([results_class; results_prop; results_pred; results_arg] as lres) ->
                if partial && List.for_all Sparql_endpoint.results_are_empty lres
                then ajax_intent ()
	        else process ~max_value_term ~max_value_arg ~partial ~unit results_class results_prop results_pred results_arg
	     | _ -> assert false)
            (fun code -> k (Result.Error (Failure ("Concept suggestions: HTTP error code " ^ string_of_int code))))
        in
        if focus_term_index#is_empty then
          if some_focus_term_is_not_queryable then ajax_intent ()
          else if not focus_pred_args_index#is_empty then ajax_extent ()
          else self#ajax_forest_properties_init ~freq0:true ~inverse constr elts k
        else
          if Sparql_endpoint.config_method_get#value (* to avoid lengthy queries *)
          then ajax_intent ()
          else ajax_extent ()
      end

  method forest_modifiers : suggestions =
    let open Lisql in
    let incrs =
      if focus_descr#unconstrained
      then [IncrIn]
      else
	let incrs = [] in
	let incrs =
	  IncrSelection (AggregSel, []) ::
	    (*IncrThatIs ::*) (* unnecessary and confusing *)
	    IncrSomethingThatIs :: IncrName "" :: IncrTriplify ::
	    IncrSimRankIncr :: IncrSimRankDecr ::
	    IncrAnd :: IncrDuplicate :: IncrOr :: IncrMaybe :: IncrNot :: IncrChoice ::
	    IncrIn ::
	    IncrUnselect ::
	    IncrHierarchy false ::
	    incrs in
	let incrs =
	  List.fold_left
	    (fun incrs order -> IncrOrder (Lisql_type.find_insertable_order order focus_type_constraints) :: incrs)
	    incrs
	    [ Highest None; Lowest None ] in
	let incrs =
	  match Lisql_annot.seq_view_available_dims s_sparql.Lisql2sparql.seq_view with
	  | None -> incrs
	  | Some ids ->
	      IncrForeachResult ::
	      List.fold_right
	      (fun id incrs -> IncrForeachId id :: IncrAggregId (Sample,id) :: incrs)
	      ids incrs in
	let incrs =
	  let aggreg_id_opt = Lisql.aggregated_id_opt focus in
	  IncrForeach ::
	  List.fold_left
	    (fun incrs aggreg ->
	      match Lisql_type.find_insertable_aggreg aggreg focus_type_constraints with
	      | Some aggreg_conv ->
		 let incrs =
		   match aggreg_id_opt with
		   | Some id2 -> IncrAggregId (aggreg_conv,id2) :: incrs
		   | None -> incrs in
		 IncrAggreg aggreg_conv :: incrs
	      | None -> incrs)
	    incrs
	    [ Lisql.NumberOf;
	      Lisql.ListOf;
	      Lisql.Sample;
	      Lisql.Total None;
	      Lisql.Average None;
	      Lisql.Maximum None;
	      Lisql.Minimum None ] in
	let incrs =
	  List.fold_left
	    (fun incrs (func,arity,pos) ->
	      let comp_arg, comp_res = Lisql_type.compatibles_insertion_func_pos func pos focus_type_constraints in
	      if comp_arg.Lisql_type.bool && comp_res.Lisql_type.bool
	      then
		let is_pred = Lisql_type.is_predicate func in
		IncrFuncArg (is_pred, func, arity, pos, comp_res.Lisql_type.conv_opt, comp_arg.Lisql_type.conv_opt) :: incrs
	      else incrs)
	    incrs
	    [ Str, 1, 1;
	      Lang, 1, 1;
	      Datatype, 1, 1;
	      IRI, 1, 1;
	      STRDT, 2, 1;
	      STRLANG, 2, 1;
	      Strlen, 1, 1;
	      Substr2, 2, 1;
	      Substr3, 3, 1;
	      Strbefore, 2, 1;
	      Strafter, 2, 1;
	      Concat, 2, 1;
	      Concat, 2, 2;
	      UCase, 1, 1;
	      LCase, 1, 1;
	      Encode_for_URI, 1, 1;
	      Replace, 3, 1;
	      Integer, 1, 1;
	      Decimal, 1, 1;
	      Double, 1, 1;
	      Indicator, 1, 1;
	      Add, 2, 1;
	      Add, 2, 2;
	      Sub, 2, 1;
	      Sub, 2, 2;
	      Mul, 2, 1;
	      Mul, 2, 2;
	      Div, 2, 1;
	      Div, 2, 2;
	      Neg, 1, 1;
	      Abs, 1, 1;
	      Round, 1, 1;
	      Ceil, 1, 1;
	      Floor, 1, 1;
	      Random2, 2, 1;
	      Random2, 2, 2;
	      Date, 1, 1;
	      Time, 1, 1;
	      Year, 1, 1;
	      Month, 1, 1;
	      Day, 1, 1;
	      Hours, 1, 1;
	      Minutes, 1, 1;
	      Seconds, 1, 1;
	      TODAY, 0, 0;
	      NOW, 0, 0;
	      And, 2, 1;
	      And, 2, 2;
	      Or, 2, 1;
	      Or, 2, 2;
	      Not, 1, 1;
	      EQ, 2, 1;
	      NEQ, 2, 1;
	      GT, 2, 1;
	      GEQ, 2, 1;
	      LT, 2, 1;
	      LEQ, 2, 1;
	      BOUND, 1, 1;
	      IF, 3, 1;
	      IF, 3, 2;
	      IF, 3, 3;
	      IsIRI, 1, 1;
	      IsBlank, 1, 1;
	      IsLiteral, 1, 1;
	      IsNumeric, 1, 1;
	      StrStarts, 2, 1;
	      StrEnds, 2, 1;
	      Contains, 2, 1;
	      LangMatches, 2, 1;
	      REGEX, 2, 1;
	      REGEX_i, 2, 1;
	    ] in
	incrs in
    let valid_incrs =
      List.filter
	(fun incr -> Lisql.insert_increment incr focus <> None)
	incrs in
    let forest =
      List.map
        (fun incr -> Node ((incr, None), []))
        valid_incrs in
    let suggestions = {partial = false; forest} in
    let _, suggestions = hook_suggestions (Modifiers, suggestions) in
    suggestions
	  
  method list_term_constraints (constr : Lisql.constr) : Lisql.constr list =
    let open Lisql in
    let l_constr =
      [ MatchesAll ["..."; "..."];
	MatchesAny ["..."; "..."];
	IsExactly "...";
	StartsWith "...";
	EndsWith "...";
	After "...";
	Before "...";
	FromTo ("...","...");
	HigherThan "...";
	LowerThan "...";
	Between ("...","...");
	HasLang "...";
	HasDatatype "..." ] in
    let l_constr =
      if Rdf.config_wikidata_mode#value then
	ExternalSearch (WikidataSearch ["..."], None) :: l_constr
      (*else if Lisql2sparql.config_fulltext_search#value = "text:query" then
	ExternalSearch (`TextQuery ["..."], None) :: l_constr*)
      else l_constr in
(*      else (* PEGASE specific hack *)
	let open Lisql in
	match focus with
	| AtS1 (_, CConsX1 (O, _, PredX (S, EO ("http://semlis-test/faers/associatedDrugEvent","http://semlis-test/faers/activeIngredient"), _))) ->
	   Jsutils.firebug "PEGASE Express!";
	   ExternalSearch (`TextQuery ["..."], None) :: l_constr
	| _ -> l_constr in *)
    let l_constr =
      List.filter
	(fun constr ->
	 Lisql_type.is_insertable_constr constr focus_type_constraints)
	l_constr in
    if l_constr = []
    then [Lisql.reset_constr constr]
    else l_constr

  method list_property_constraints (constr : Lisql.constr) : Lisql.constr list =
    let open Lisql in
    let l_constr =
      [ MatchesAll ["..."; "..."];
	MatchesAny ["..."; "..."];
	IsExactly "...";
	StartsWith "...";
	EndsWith "..." ] in
    if Rdf.config_wikidata_mode#value then
      ExternalSearch (WikidataSearch ["..."], None) :: l_constr
    (*else if Lisql2sparql.config_fulltext_search#value = "text:query" then
      ExternalSearch (`TextQuery ["..."], None) :: l_constr*)
    else l_constr

  method list_modifier_constraints (constr : Lisql.constr) : Lisql.constr list =
    let open Lisql in
    [ MatchesAll ["..."; "..."];
      MatchesAny ["..."; "..."] ]
      
end
