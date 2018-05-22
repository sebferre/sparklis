(*
  Copyright 2013-2017 Sébastien Ferré, IRISA, Université de Rennes 1

  This file is part of Sparklis.
*)

open Js

class ['a,'b] index ?(parents : ('a -> 'a list) option) () =
object (self)
  val mutable organized : bool = false
  val mutable h : ('a, 'b * 'a list ref) Hashtbl.t = Hashtbl.create 101
  val mutable roots : 'a list = []

  method add (elt, info : 'a * 'b) : unit = Hashtbl.add h elt (info, ref [])
  method remove (elt : 'a) : unit = Hashtbl.remove h elt
    
  method private organize : unit = (* must be called after all additions *)
    match organized, parents with
    | _, None -> ()
    | true, _ -> ()
    | false, Some parents ->
      let add_child k_parent k_child : bool = (* returns true if parent exists *)
	try
	  let _v, ref_children = Hashtbl.find h k_parent in
	  ref_children := k_child::!ref_children;
	  true
	with Not_found -> false (* absent parents are ignored *)
      in
      Hashtbl.iter
	(fun k_child _ ->
	  let has_parent =
	    List.fold_left
	      (fun res k_parent ->
		let res1 = add_child k_parent k_child in
		res || res1)
	      false (parents k_child) in
	  if not has_parent then roots <- k_child::roots)
	h;
      organized <- true

  method is_empty : bool = (Hashtbl.length h = 0)
  method length : int = Hashtbl.length h
  method fold : 'c. ('c -> 'a * 'b -> 'c) -> 'c -> 'c =
    fun f init -> Hashtbl.fold (fun k (v,_) res -> f res (k,v)) h init
  method iter : ('a * 'b -> unit) -> unit =
    fun f -> Hashtbl.iter (fun k (v,_) -> f (k,v)) h
  method map_list : 'c. ('a * 'b -> 'c) -> 'c list =
    fun f -> Hashtbl.fold (fun k (v,_) res -> (f (k,v))::res) h []
  method map_tree : 'c. ('a * 'b -> 'c) -> ([`Node of 'c * 'd list] as 'd) list =
    fun f ->
      self#organize;
      if organized then
	let rec aux (keys : 'a list) =
	  let elts =
	    List.map
	      (fun k -> try k, Hashtbl.find h k with Not_found -> assert false)
	      keys in
	  List.map
	    (fun (k,(v,ref_children)) ->
	      `Node (f (k,v), aux !ref_children))
	    elts
	in
	aux roots
      else (* no tree organization *)
	Hashtbl.fold
	  (fun k (v,_) res -> `Node (f (k,v), []) :: res)
	  h []
end
  
let empty_index () = new index ()
let singleton_index elt_info =
  let index = new index () in
  index#add elt_info;
  index
							  
class ['a] int_index = ['a,int] index ()
class ['a,'b] nested_int_index = ['a, int * 'b int_index] index ()

type freq_unit = [`Results | `Entities | `Concepts | `Modifiers]
type freq = { value : int; max_value : int option; partial : bool; unit : freq_unit }
class incr_freq_index = [Lisql.increment, freq option] index ()

let term_hierarchy_of_focus focus =
  match Lisql.hierarchy_of_focus focus with
  | None -> Ontology.no_relation
  | Some (id,p,ori,inv) ->
     let hierarchy_spec =
       let inverse =
	 match ori with
	 | Lisql.Fwd -> inv
	 | Lisql.Bwd -> not inv in
       Ontology.Hierarchy (p, inverse) in
     Ontology.sparql_relations#get
       ~froms:Sparql_endpoint.config_default_graphs#froms
       hierarchy_spec
						       
let increment_parents (term_hierarchy : Ontology.relation) = function
  | Lisql.IncrTerm (Rdf.URI uri) -> List.map (fun u -> Lisql.IncrTerm (Rdf.URI u)) (term_hierarchy#info uri)
  | Lisql.IncrType uri -> List.map (fun u -> Lisql.IncrType u) (Ontology.config_class_hierarchy#value#info uri)
  | Lisql.IncrRel (uri,xwd) -> List.map (fun u -> Lisql.IncrRel (u,xwd)) (Ontology.config_property_hierarchy#value#info uri)
  | _ -> []
class incr_freq_tree_index th = [Lisql.increment, freq option] index ~parents:(increment_parents th) ()


(* configuration *)

let config_intentional_init_concepts = new Config.boolean_input ~key:"intentional_init_concepts" ~input_selector:"#input-intentional-init-concepts" ~default:true ()
let config_regexp_hidden_URIs = new Config.string_input ~key:"regexp_hidden_URIs" ~input_selector:"#input-regexp-hidden-uris" ~default:"^(http://www.w3.org/2002/07/owl#|http://www.openlinksw.com/|nodeID://)" ()
let config_max_results = new Config.integer_input ~key:"max_results" ~input_selector:"#input-max-results" ~min:1 ~default:200 ()
let config_max_classes = new Config.integer_input ~key:"max_classes" ~input_selector:"#input-max-classes" ~min:0 ~default:200 ()
let config_max_properties = new Config.integer_input ~key:"max_properties" ~input_selector:"#input-max-properties" ~min:0 ~default:200 ()

let formula_hidden_URIs_term (tx : _ Sparql.any_term) : Sparql.formula =
  match config_regexp_hidden_URIs#value with
  | "" -> Sparql.True
  | re -> Sparql.(Filter (log_not (log_and [expr_func "BOUND" [tx]; expr_regex (expr_func "str" [tx]) re])))
let formula_hidden_URIs (v : string) : Sparql.formula =
  formula_hidden_URIs_term (Sparql.var v)

let filter_hidden_URIs (v : string) : string =
  (Sparql.pattern_of_formula (formula_hidden_URIs v) :> string)
    
(* extraction of the extension and indexes *)

let lexicon_enqueue_term = function
  | Rdf.URI uri -> Lexicon.config_entity_lexicon#value#enqueue uri
  | Rdf.TypedLiteral (_,dt) -> Lexicon.config_class_lexicon#value#enqueue dt
  | _ -> ()

let page_of_results (offset : int) (limit : int) (geolocs : (Sparql.term * (Rdf.var * Rdf.var)) list) results (k : Sparql_endpoint.results -> unit) : unit =
  let open Sparql_endpoint in
  let rec aux offset limit acc = function
    | [] -> acc
    | binding::l ->
      if offset > 0 then aux (offset-1) limit acc l
      else if limit > 0 then begin
	Array.iter
	  (function
	    | Some t -> lexicon_enqueue_term t
	    | None -> ())
	  binding;
	aux offset (limit-1) (binding :: acc) l end
      else acc
  in
  let partial_vars =
    List.filter
      (fun (v,i) -> not (List.exists (fun (_,(vlat,vlong)) -> v=vlat || v=vlong) geolocs))
      results.vars in
  let partial_bindings = List.rev (aux offset limit [] results.bindings) in
  Lexicon.config_class_lexicon#value#sync (fun () ->
    Lexicon.config_entity_lexicon#value#sync (fun () ->
      k { results with vars = partial_vars; bindings = partial_bindings }))

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
    Firebug.console##log(string ("list_of_results_column: missing variable " ^ var));
    []

(* deprecated
      
let fill_index_of_results_column index ?(filter : Rdf.term -> bool = fun _ -> true) (var : Rdf.var) results : unit =
  let open Sparql_endpoint in
  try
    let i = List.assoc var results.vars in
    let ht = Hashtbl.create 1000 in
    List.iter
      (fun binding ->
	match binding.(i) with
	| None -> ()
	| Some term ->
	  let cpt =
	    try Hashtbl.find ht term
	    with Not_found ->
	      let cpt = ref 0 in
	      Hashtbl.add ht term cpt;
	      cpt in
	  incr cpt)
      results.bindings;
    Hashtbl.iter
      (fun term cpt ->
	if filter term then index#add (term,!cpt))
      ht
  with Not_found ->
    Firebug.console##log(string ("index_of_results_column: missing variable " ^ var))
let index_of_results_column ?filter var results : Rdf.term int_index =
  let index = new int_index in
  fill_index_of_results_column index ?filter var results;
  index

      
let fill_index_of_results_column_list index ?(filter : Rdf.term list -> bool = fun _ -> true) (var_list : Rdf.var list) results : unit =
  let open Sparql_endpoint in
  try
    let i_list = List.map (fun var -> List.assoc var results.vars) var_list in
    let ht = Hashtbl.create 1000 in
    List.iter
      (fun binding ->
       let term_list_opt =
	 List.fold_right
	   (fun i res ->
	    match binding.(i), res with
	    | Some term, Some tl -> Some (term :: tl)
	    | _ -> None)
	   i_list (Some []) in
	match term_list_opt with
	| None -> ()
	| Some term_list ->
	  let cpt =
	    try Hashtbl.find ht term_list
	    with Not_found ->
	      let cpt = ref 0 in
	      Hashtbl.add ht term_list cpt;
	      cpt in
	  incr cpt)
      results.bindings;
    Hashtbl.iter
      (fun term_list cpt ->
	if filter term_list then index#add (term_list,!cpt))
      ht
  with Not_found ->
    Firebug.console##log(string ("index_of_results_column_list: missing variable among " ^ String.concat ", " var_list))
let index_of_results_column_list ?filter var_list results : Rdf.term list int_index =
  let index = new int_index in
  fill_index_of_results_column_list index ?filter var_list results;
  index

let fill_nested_index_of_results_columns index
    ?(filter1 : Rdf.term -> bool = fun _ -> true)
    ?(filter2 : Rdf.term -> bool = fun _ -> true)
    (var1 : Rdf.var) (nested_spec : Rdf.term option) results =
  let open Sparql_endpoint in
  try
    let i1 = List.assoc var1 results.vars in
    let get2 =
      match nested_spec with
      | None -> (fun binding -> None)
      | Some (Rdf.Var var2) ->
	let i2 = List.assoc var2 results.vars in
	(fun binding -> binding.(i2))
      | Some term2 -> (fun binding -> Some term2)
    in
    let ht = Hashtbl.create 1000 in
    List.iter
      (fun binding ->
	match binding.(i1) with
	  | None -> ()
	  | Some term1 ->
	    let cpt1, nested_ht =
	      try Hashtbl.find ht term1
	      with Not_found ->
		let data = ref 0, Hashtbl.create 3 in
		Hashtbl.add ht term1 data;
		data in
	    incr cpt1;
	    ( match get2 binding with
	    | None -> ()
	    | Some term2 ->
	      let cpt2 =
		try Hashtbl.find nested_ht term2
		with Not_found ->
		  let cpt2 = ref 0 in
		  Hashtbl.add nested_ht term2 cpt2;
		  cpt2 in
	      incr cpt2 ))
      results.bindings;
    Hashtbl.iter
      (fun term1 (cpt1,nested_ht) ->
	if filter1 term1
	then begin
	  let nested_index = new int_index in
	  Hashtbl.iter
	    (fun term2 cpt2 ->
	      if filter2 term2 then nested_index#add (term2, !cpt2))
	    nested_ht;
	  index#add (term1, (!cpt1, nested_index))
	end)
      ht
  with Not_found ->
    Firebug.console##log(string ("index_of_results_column_nested: missing variable " ^ var1 ^ " or nested variable"))
let nested_index_of_results_columns ?filter1 ?filter2 var1 nested_spec results : (Rdf.term, Rdf.term) nested_int_index =
  let index = new nested_int_index in
  fill_nested_index_of_results_columns index ?filter1 ?filter2 var1 nested_spec results;
  index

 *)
      
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
    (fun binding ->
     List.map
       (fun vt -> get vt binding)
       keys_vt) in
(*    let keys_get = List.map get keys_vt in
    (fun binding ->
     List.fold_right
       (fun get keys_opt ->
	match get binding, keys_opt with
	| _, None -> None
	| None, _ -> None
	| Some key, Some keys -> Some (key::keys))
       keys_get (Some [])) in *)
  let get_nested =
    match nested_vt_opt with
    | None -> (fun binding -> None)
    | Some nested_vt -> (fun binding -> get nested_vt binding)
  in
  let ht = Hashtbl.create 1000 in
  List.iter
    (fun binding ->
     match get_keys binding with
     | (*None -> ()
     | Some*) keys ->
	let cpt1, nested_ht =
	  try Hashtbl.find ht keys
	  with Not_found ->
	    let data = ref 0, Hashtbl.create 3 in
	    Hashtbl.add ht keys data;
	    data in
	incr cpt1;
	( match get_nested binding with
	  | (*None -> ()
	  | Some*) nested ->
	     let cpt2 =
	       try Hashtbl.find nested_ht nested
	       with Not_found ->
		 let cpt2 = ref 0 in
		 Hashtbl.add nested_ht nested cpt2;
		 cpt2 in
	     incr cpt2 ))
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

let index_of_results_2columns (var_x : Rdf.var) (var_count : Rdf.var) results : Rdf.term int_index =
  let open Sparql_endpoint in
  let index = new int_index in
  try
    let i_x = List.assoc var_x results.vars in
    let i_count = try List.assoc var_count results.vars with _ -> -1 in
    List.iter
      (fun binding ->
	match binding.(i_x) with
	| None -> ()
	| Some x ->
	  let count =
	    if i_count < 0
	    then 1
	    else
	      match binding.(i_count) with
	      | Some (Rdf.Number (f,s,dt)) -> (try int_of_string s with _ -> 0)
	      | Some (Rdf.TypedLiteral (s,dt)) -> (try int_of_string s with _ -> 0)
	      | _ -> 0 in
	  index#add (x, count))
      results.bindings;
    index
  with Not_found ->
    Firebug.console##log(string ("index_of_results_2columns: missing variables " ^ var_x ^ ", " ^ var_count));
    index


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
  k (List.rev rev_l)
      
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
		 (lat,long,term)::data
	      | _ -> data)
	    data results.bindings
	with Not_found ->
	  Jsutils.firebug ("Missing geoloc vars in results: " ^ v_lat ^ ", " ^ v_long);
	  data)
      [] geolocs in
  k l

(* LIS navigation places *)

class place (endpoint : string) (focus : Lisql.focus) =
  let focus_descr, s_annot = Lisql_annot.annot_focus focus in
object (self)
  (* essential state *)

  val endpoint = endpoint
  method endpoint = endpoint

  method focus = focus
  method query = s_annot

  (* derived state *)

  val mutable term_hierarchy : Ontology.relation = Ontology.no_relation
		   
  val mutable id_labelling = new Lisql2nl.id_labelling []
  method id_labelling = id_labelling

  val mutable s_sparql : Lisql2sparql.s_sparql =
    Lisql2sparql.({
      state = new Lisql2sparql.state (new Lisql2nl.id_labelling []);
      focus_term_opt = None;
      focus_graph_opt = None;
      focus_pred_args_opt = None;
      query_opt = None;
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

  (* SPARQL query and results *)

  val mutable results = Sparql_endpoint.empty_results
  val mutable results_typing : Lisql_type.datatype list array = [||]
  val mutable focus_type_constraints : Lisql_type.focus_type_constraints = Lisql_type.default_focus_type_constraints
  val mutable focus_term_index : (Rdf.term, Rdf.term) nested_int_index = new nested_int_index (* used when some focus term *)
  val mutable focus_graph_index : Rdf.term int_index = new int_index (* used when no focus_term but some focus graph *)
  val mutable focus_pred_args_index : (Rdf.term list, Rdf.term) nested_int_index = new nested_int_index (* used when some focus-pred-args *)
  val mutable some_focus_term_is_blank : bool = false

  method id_typing (id : Lisql.id) : Lisql_type.datatype list =
    let v = id_labelling#get_id_var id in
    try
      let i = List.assoc v results.Sparql_endpoint.vars in
      results_typing.(i)
    with Not_found ->
      Jsutils.firebug ("No datatype for id #" ^ string_of_int id);
      []
    
  method ajax_sparql_results term_constr elts
    ~(k_sparql : string option -> unit)
    ~(k_results : string option -> unit) =
    (* re-initializing *)
    let filter_term =
      function
      | Rdf.URI uri when String.contains uri ' ' -> false
      (* URIs with spaces inside are not allowed in SPARQL queries *)
      | Rdf.Bnode _ -> some_focus_term_is_blank <- true ; false
      (* blank nodes are not allowed in SPARQL queries *)
      | _ -> true in
    let mapfilter_term_opt =
      function
      | Some t -> if filter_term t then Some t else None
      | None -> None
    in
    results <- Sparql_endpoint.empty_results;
    results_typing <- [||];
    focus_term_index <- new nested_int_index;
    focus_graph_index <- new int_index;
    focus_pred_args_index <- new nested_int_index;
    some_focus_term_is_blank <- false;
    (* computing results and derived attributes *)
    match s_sparql.Lisql2sparql.query_opt with
    | None ->
        k_sparql None;
	( match s_sparql.Lisql2sparql.focus_term_opt with
	  | None -> ()
	  | Some vt -> focus_term_index <- nested_index_of_results_varterm ~filter:filter_term vt None results );
(*	| Some (Rdf.Var _) -> ()
	| Some term -> focus_term_index#add (term, (1, new int_index))
	| None -> () ); *)
	k_results None
    | Some query ->
        let sparql_genvar = s_sparql.Lisql2sparql.state#genvar in
	let froms = Sparql_endpoint.config_default_graphs#froms in
	let limit = config_max_results#value in
	let sparql = query ~hook:(fun tx -> Lisql2sparql.filter_constr_entity sparql_genvar tx term_constr) ~froms ~limit in
	k_sparql (Some sparql);
	Sparql_endpoint.ajax_in ~send_results_to_yasgui:true elts ajax_pool endpoint sparql
	  (fun res ->
	    results <- res;
	    results_typing <- Lisql_type.of_sparql_results res;
	    focus_type_constraints <- Lisql_type.of_focus
	      (fun id -> Some (self#id_typing id))
	      focus;
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
	    );
	    (* callback *)
	    k_results (Some sparql))
	  (fun code -> k_results (Some sparql))

  method partial_results = (results.Sparql_endpoint.length = config_max_results#value)
  method results_dim = results.Sparql_endpoint.dim
  method results_nb = results.Sparql_endpoint.length
  method results_page offset limit k = page_of_results offset limit s_sparql.Lisql2sparql.state#geolocs results k
  method results_geolocations k = geolocations_of_results s_sparql.Lisql2sparql.state#geolocs results k
  method results_slides k = slides_of_results results k

  (* indexes: must be called in the continuation of [ajax_sparql_results] *)

  method private ajax_index_terms_init constr elt (k : partial:bool -> incr_freq_index -> unit) =
    let process results_term =
      let list_term = list_of_results_column "term" results_term in
      let max_value = None in
      let partial = results_term.Sparql_endpoint.length = config_max_results#value in
      let unit = `Results in
      let incr_index = new incr_freq_tree_index term_hierarchy in
      List.iter
	(fun t -> incr_index#add (Lisql.IncrTerm t, Some { value=1; max_value; partial; unit }))
	list_term;
      k ~partial incr_index
    in
    let sparql_genvar = new Lisql2sparql.genvar in
    let sparql_froms = Sparql_endpoint.config_default_graphs#sparql_froms in
    let sparql_term =
      "SELECT DISTINCT ?term " ^ sparql_froms ^ "WHERE { " ^
	(Sparql.pattern_of_formula (Lisql2sparql.search_constr_entity sparql_genvar (Sparql.var "term") constr) :> string) ^
	filter_hidden_URIs "term" ^
	" FILTER (!IsBlank(?term)) } LIMIT " ^ string_of_int config_max_results#value in
    Sparql_endpoint.ajax_in ~tentative:true elt ajax_pool endpoint sparql_term (* tentative because uses a non-standard feature 'bif:contains' *)
      (fun results_term -> process results_term)
      (fun code -> process Sparql_endpoint.empty_results)

  method ajax_index_terms_inputs_ids constr elt (k : partial:bool -> incr_freq_index -> unit) =
    if focus_descr#term = `Undefined then
      k ~partial:false (new incr_freq_index)
    else if focus_descr#unconstrained then
      self#ajax_index_terms_init constr elt k
    else
      let max_value = None (*Some self#results_nb*) in
      let partial = self#partial_results in
      let unit = `Results in
      let incr_index = new incr_freq_tree_index term_hierarchy in
    (* adding selection increments *)
      incr_index#add (Lisql.IncrSelection (`NAnd, []), None);
      incr_index#add (Lisql.IncrSelection (`NOr, []), None);
    (* adding increment 'anything' *)
      if Lisql.insert_increment Lisql.IncrAnything focus <> None then
	incr_index#add (Lisql.IncrAnything, None);
    (* adding term increments *)
      focus_term_index#iter (*rev_map*)
	(fun (t, (freq,_)) ->
	  (match t with Rdf.URI uri -> term_hierarchy#enqueue uri | _ -> ());
	  lexicon_enqueue_term t;
	  incr_index#add (Lisql.IncrTerm t, Some { value=freq; max_value; partial; unit }));
    (* adding input increments *)
      if Lisql.is_undef_expr_focus focus then
	List.iter
	  (fun (dt : Lisql.input_type) ->
	    if Lisql_type.is_insertable_input (dt :> Lisql_type.datatype) focus_type_constraints then
	      incr_index#add (Lisql.IncrInput ("",dt), None))
	  [`IRI; `String; `Float; `Integer; `Date; `Time; `DateTime];
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
      term_hierarchy#sync (fun () ->
	Lexicon.config_entity_lexicon#value#sync (fun () ->
	  Lexicon.config_class_lexicon#value#sync (fun () ->
	    k ~partial incr_index)))

  method private ajax_index_properties_init constr elt (k : partial:bool -> incr_freq_index -> unit) =
    let process results_class results_prop results_pred =
      let max_value = None in
      let partial_class = results_class.Sparql_endpoint.length = config_max_classes#value in
      let partial_prop = results_prop.Sparql_endpoint.length = config_max_properties#value in
      let partial_pred = results_pred.Sparql_endpoint.length = config_max_properties#value in
      let partial = partial_class || partial_prop || partial_pred in
      let unit = `Entities in
      let int_index_class = index_of_results_varterm_list (List.map (fun v -> Rdf.Var v) Lisql2sparql.WhichClass.pattern_vars) results_class in
      let int_index_prop = index_of_results_varterm_list (List.map (fun v -> Rdf.Var v) Lisql2sparql.WhichProp.pattern_vars) results_prop in
      let int_index_pred = index_of_results_varterm_list (List.map (fun v -> Rdf.Var v) Lisql2sparql.WhichPred.pattern_vars) results_pred in
      let incr_index = new incr_freq_tree_index term_hierarchy in
      int_index_class#iter
	(fun (lt, count) ->
	 List.iter
	   (function
	     | Some (Rdf.URI uri) ->
		Ontology.config_class_hierarchy#value#enqueue uri;
		Ontology.config_hierarchy_inheritance#value#enqueue uri;
		Lexicon.config_class_lexicon#value#enqueue uri
	     | _ -> ())
	   lt;
	 let freq = { value=count; max_value; partial=partial_class; unit } in
	 Lisql2sparql.WhichClass.increments_of_terms ~init:true lt |>
	   List.iter
	     (fun incr -> incr_index#add (incr, Some freq)));
      int_index_prop#iter
	(fun (lt, count) ->
	 List.iter
	   (function
	     | Some (Rdf.URI uri) ->
		Ontology.config_property_hierarchy#value#enqueue uri;
		Ontology.config_hierarchy_inheritance#value#enqueue uri;
		Lexicon.config_property_lexicon#value#enqueue uri
	     | _ -> ())
	   lt;
	 let freq = { value=count; max_value; partial=partial_prop; unit } in
	 Lisql2sparql.WhichProp.increments_of_terms ~init:true lt |>
	   List.iter
	     (fun incr -> incr_index#add (incr, Some freq)));
      int_index_pred#iter
	(fun (lt, count) ->
	 List.iter
	   (function
	     | Some (Rdf.URI p) -> Lexicon.config_property_lexicon#value#enqueue p
	     | _ -> ()) lt;
	 let freq = { value=count; max_value; partial=partial_pred; unit } in
	 Lisql2sparql.WhichPred.increments_of_terms ~init:true lt |>
	   List.iter
	     (fun incr ->
	      incr_index#add (incr, Some freq);
	      Lisql2sparql.WhichPred.increments_hidden_by_increment ~init:true incr |>
		List.iter incr_index#remove));
      Ontology.config_class_hierarchy#value#sync (fun () ->
	Ontology.config_property_hierarchy#value#sync (fun () ->
	  Ontology.config_hierarchy_inheritance#value#sync (fun () ->
	    Lexicon.config_class_lexicon#value#sync (fun () ->
	      Lexicon.config_property_lexicon#value#sync (fun () ->
	        k ~partial incr_index)))))
    in
    let ajax_extent () =
      let sparql_genvar = new Lisql2sparql.genvar in
      let sparql_froms = Sparql_endpoint.config_default_graphs#sparql_froms in
      let graph_opt (gp : Sparql.pattern) : Sparql.pattern =
	match s_sparql.Lisql2sparql.focus_graph_opt with
	| None -> gp
	| Some _ ->  Sparql.union (focus_graph_index#map_list (fun (tg,_) -> Sparql.graph (Sparql.term tg) gp))
      in
      let make_sparql lv (pat : Sparql.pattern) filter_constr config_max =
	let _ = assert (lv <> []) in
	let main_v = List.hd lv in
	let g_pat = (graph_opt pat :> string) in
	"SELECT DISTINCT ?" ^ String.concat " ?" lv ^ " " ^ sparql_froms ^ "WHERE { " ^
	  g_pat ^
	  (Sparql.pattern_of_formula (filter_constr sparql_genvar (Sparql.var main_v) constr) :> string) ^
	  filter_hidden_URIs main_v ^
	  " } LIMIT " ^ string_of_int config_max#value in
      let sparql_class = make_sparql
			   Lisql2sparql.WhichClass.pattern_vars
			   (Lisql2sparql.WhichClass.pattern_of_term None)
			   Lisql2sparql.filter_constr_class
			   config_max_classes in
      let sparql_prop = make_sparql
			  Lisql2sparql.WhichProp.pattern_vars
			  (Lisql2sparql.WhichProp.pattern_of_term None)
			  Lisql2sparql.filter_constr_property
			  config_max_properties in
      let sparql_pred = make_sparql
			  Lisql2sparql.WhichPred.pattern_vars
			  (Lisql2sparql.WhichPred.pattern_of_term None)
			  Lisql2sparql.filter_constr_property
			  config_max_properties in
      Sparql_endpoint.ajax_list_in [elt] ajax_pool endpoint [sparql_class; sparql_prop; sparql_pred]
	(function
	| [results_class; results_prop; results_pred] -> process results_class results_prop results_pred
	| _ -> assert false)
	(fun code -> process Sparql_endpoint.empty_results Sparql_endpoint.empty_results Sparql_endpoint.empty_results)
    in
    let ajax_intent () =
      let sparql_genvar = new Lisql2sparql.genvar in
      let sparql_froms = Sparql_endpoint.config_schema_graphs#sparql_froms in
      let make_sparql lv pat filter_constr config_max =
	let _ = assert (lv <> []) in
	let main_v = List.hd lv in
	"SELECT DISTINCT ?" ^ String.concat " ?" lv ^ " " ^ sparql_froms ^ "WHERE { " ^
	  pat ^
	  (* "FILTER EXISTS { [] a ?class } " ^ *) (* 'EXISTS' not widely supported, and also fails for pure ontologies! *)
	  (Sparql.pattern_of_formula (filter_constr sparql_genvar (Sparql.var main_v) constr) :> string) ^
	  filter_hidden_URIs main_v ^
	    " } LIMIT " ^ string_of_int config_max#value in
      let sparql_class = make_sparql
			   Lisql2sparql.WhichClass.pattern_vars
			   (Lisql2sparql.WhichClass.intent_pattern () :> string)
			   Lisql2sparql.filter_constr_class
			   config_max_classes in
      let sparql_prop = make_sparql
			  Lisql2sparql.WhichProp.pattern_vars
			  (Lisql2sparql.WhichProp.intent_pattern () :> string)
			  Lisql2sparql.filter_constr_property
			  config_max_properties in
      let sparql_pred = make_sparql
			  Lisql2sparql.WhichPred.pattern_vars
			  (Lisql2sparql.WhichPred.intent_pattern () :> string)
			  Lisql2sparql.filter_constr_property
			  config_max_properties in
      Sparql_endpoint.ajax_list_in ~tentative:true ~fail_on_empty_results:false(*true*) [elt] ajax_pool endpoint [sparql_class; sparql_prop; sparql_pred]
	(function
	  | [results_class; results_prop; results_pred] ->
	     process results_class results_prop results_pred
	  | _ -> assert false)
	(fun _ -> ajax_extent ()) (* looking at facts *)
    in
    let ajax_wikidata () =
      let sparql_genvar = new Lisql2sparql.genvar in
      let sparql_froms = Sparql_endpoint.config_default_graphs#sparql_froms in
      let graph_opt (gp : Sparql.pattern) : Sparql.pattern =
	match s_sparql.Lisql2sparql.focus_graph_opt with
	| None -> gp
	| Some _ ->  Sparql.union (focus_graph_index#map_list (fun (tg,_) -> Sparql.graph (Sparql.term tg) gp))
      in      
      let sparql_class = (* use (List.hd Lisql2sparql.WhichClass.pattern_vars = "c") as result variable *)
	"SELECT DISTINCT ?c " ^ sparql_froms ^ "WHERE { " ^
	  (graph_opt (Sparql.(rdf_type (var "x") (var "c"))) :> string) ^
	  (Sparql.pattern_of_formula (Lisql2sparql.filter_constr_class sparql_genvar (Sparql.var "c") constr) : Sparql.pattern :> string) ^
	    (*filter_hidden_URIs "class" ^*)
	  " } GROUP BY ?c ORDER BY DESC(COUNT(?x)) LIMIT " ^ string_of_int config_max_classes#value in
      Sparql_endpoint.ajax_list_in
	[elt] ajax_pool endpoint [sparql_class]
	(function
	  | [results_class] -> process results_class Sparql_endpoint.empty_results Sparql_endpoint.empty_results
	  | _ -> assert false)
	(fun code -> process Sparql_endpoint.empty_results Sparql_endpoint.empty_results Sparql_endpoint.empty_results)
    in
    if Rdf.config_wikidata_mode#value
    then ajax_wikidata ()
    else
      if config_intentional_init_concepts#value && s_sparql.Lisql2sparql.focus_graph_opt = None
      then ajax_intent ()
      else ajax_extent ()

  method ajax_index_properties constr elt (k : partial:bool -> incr_freq_index -> unit) =
    if (focus_descr#term = `Undefined && focus_descr#pred_args = `Undefined) || not focus_descr#incr then
      k ~partial:false (new incr_freq_index) (* only constraints on aggregations (HAVING clause) *)
    else if focus_descr#unconstrained then
      self#ajax_index_properties_init constr elt k
    else begin
    let focus_as_incr_rel_opt =
      match focus with
      | Lisql.AtS1 (np, Lisql.RelX (p,ori,ctx)) -> Some (Lisql.IncrRel (p,ori))
      | _ -> None in
    let process ~max_value ~partial ~unit results_class results_prop results_pred results_arg =
      let partial_class = partial || results_class.Sparql_endpoint.length = config_max_classes#value in
      let partial_prop = partial || results_prop.Sparql_endpoint.length = config_max_properties#value in
      let partial_pred = partial || results_pred.Sparql_endpoint.length = config_max_properties#value in
      let partial_arg = partial || results_arg.Sparql_endpoint.length = config_max_properties#value in
      let partial = partial_class || partial_prop || partial_pred || partial_arg in
      let int_index_class = index_of_results_varterm_list (List.map (fun v -> Rdf.Var v) Lisql2sparql.WhichClass.pattern_vars) results_class in
      let int_index_prop = index_of_results_varterm_list (List.map (fun v -> Rdf.Var v) Lisql2sparql.WhichProp.pattern_vars) results_prop in
      let int_index_pred = index_of_results_varterm_list (List.map (fun v -> Rdf.Var v) Lisql2sparql.WhichPred.pattern_vars) results_pred in
      let int_index_arg = index_of_results_varterm_list (List.map (fun v -> Rdf.Var v) Lisql2sparql.WhichArg.pattern_vars) results_arg in
      let incr_index = new incr_freq_tree_index term_hierarchy in
      let trans_rel = ref false in
      let fwd_prop = ref false in
      let bwd_prop = ref false in
      (* adding selection increments *)
      incr_index#add (Lisql.IncrSelection (`And, []), None);
      incr_index#add (Lisql.IncrSelection (`Or, []), None);
      (* adding class increments *)
      int_index_class#iter
	(fun (lt, count) ->
	 List.iter
	   (function
	     | Some (Rdf.URI uri) ->
		Ontology.config_class_hierarchy#value#enqueue uri;
		Ontology.config_hierarchy_inheritance#value#enqueue uri;
		Lexicon.config_class_lexicon#value#enqueue uri
	     | _ -> ())
	   lt;
	  Lisql2sparql.WhichClass.increments_of_terms ~init:false lt |>
	    List.iter
	      (fun incr -> incr_index#add (incr, Some { value=count; max_value; partial=partial_class; unit })));
      (* adding property increments + hierarchy + LatLong *)
      int_index_prop#iter
	(fun (lt,count) ->
	 List.iter
	   (function
	     | Some (Rdf.URI uri) ->
		Ontology.config_property_hierarchy#value#enqueue uri;
		Ontology.config_hierarchy_inheritance#value#enqueue uri;
		Lexicon.config_property_lexicon#value#enqueue uri
	     | _ -> ())
	   lt;
	 let freq_opt = Some { value=count; max_value; partial=partial_prop; unit } in
	 Lisql2sparql.WhichProp.increments_of_terms ~init:false lt |>
	   List.iter
	     (fun incr ->
	      incr_index#add (incr, freq_opt);
	      if Some incr = focus_as_incr_rel_opt then
		trans_rel := true;
	      ( match incr with
		| Lisql.IncrRel (_,Lisql.Fwd) -> fwd_prop := true
		| Lisql.IncrRel (_,Lisql.Bwd) -> bwd_prop := true
		| _ -> () );
	      ( match Lisql.latlong_of_increment incr with
		| Some ll -> incr_index#add (Lisql.IncrLatLong ll, freq_opt)
		| None -> () )));
      (* adding pred+arg increments *)
      int_index_pred#iter
	(fun (lt, count) ->
	 List.iter
	   (function
	     | Some (Rdf.URI p) -> Lexicon.config_property_lexicon#value#enqueue p
	     | _ -> ()) lt;
	 let freq_opt = Some { value=count; max_value; partial=partial_pred; unit } in
	 Lisql2sparql.WhichPred.increments_of_terms ~init:false lt |>
	   List.iter
	     (fun incr ->
	      incr_index#add (incr, freq_opt);
	      ( match Lisql.latlong_of_increment incr with
		| Some ll -> incr_index#add (Lisql.IncrLatLong ll, freq_opt)
		| None -> () );
	      Lisql2sparql.WhichPred.increments_hidden_by_increment ~init:false incr |>
	       List.iter incr_index#remove));
      int_index_arg#iter
	(fun (lt,count) ->
	 List.iter
	   (function
	     | Some (Rdf.URI uri) -> Lexicon.config_property_lexicon#value#enqueue uri
	     | _ -> ())
	   lt;
	 let freq_opt = Some { value=count; max_value; partial=partial_arg; unit } in
	 Lisql2sparql.WhichArg.increments_of_terms lt |>
	   List.iter
	     (fun incr -> incr_index#add (incr,freq_opt)));
      (* adding hierarchy increments *)
      if !trans_rel then
	List.iter
	  (fun incr ->
	   if Lisql.insert_increment incr focus <> None
	   then incr_index#add (incr,None))
	  [Lisql.IncrHierarchy (true,false);
	   Lisql.IncrHierarchy (true,true)];
      if !fwd_prop then incr_index#add (Lisql.IncrTriple Lisql.S, None);
      if !bwd_prop then incr_index#add (Lisql.IncrTriple Lisql.O, None);
      Ontology.config_class_hierarchy#value#sync (fun () ->
	Ontology.config_property_hierarchy#value#sync (fun () ->
	  Ontology.config_hierarchy_inheritance#value#sync (fun () ->
	    Lexicon.config_class_lexicon#value#sync (fun () ->
	      Lexicon.config_property_lexicon#value#sync (fun () ->
	        k ~partial incr_index)))))
    in
    let sparql_genvar = s_sparql.Lisql2sparql.state#genvar in
    let froms = Sparql_endpoint.config_default_graphs#froms in
    let ajax_intent () =
      let max_value = None in
      let partial = self#partial_results in
      let unit = `Results in
      let make_sparql (query_opt : Lisql2sparql.template option) filter_constr config_max =
	match query_opt with
	| None -> ""
	| Some query ->
	   query
	     ~hook:(fun tx -> Sparql.formula_and (filter_constr sparql_genvar tx constr) (formula_hidden_URIs_term tx))
	     ~froms ~limit:config_max#value in
      let sparql_class = make_sparql
		       s_sparql.Lisql2sparql.query_class_opt
		       Lisql2sparql.filter_constr_class
		       config_max_classes in
      let sparql_prop =
	if Rdf.config_wikidata_mode#value
	then ""
	else make_sparql
	       s_sparql.Lisql2sparql.query_prop_opt
	       Lisql2sparql.filter_constr_property
	       config_max_properties in
      let sparql_pred = make_sparql
			  s_sparql.Lisql2sparql.query_pred_opt
			  Lisql2sparql.filter_constr_property
			  config_max_properties in
      let sparql_arg = make_sparql
			 s_sparql.Lisql2sparql.query_arg_opt
			 Lisql2sparql.filter_constr_property
			 config_max_properties in
      Sparql_endpoint.ajax_list_in [elt] ajax_pool endpoint [sparql_class; sparql_prop; sparql_pred; sparql_arg]
	    (function
	      | [results_class; results_prop; results_pred; results_arg] ->
		 process ~max_value ~partial ~unit results_class results_prop results_pred results_arg
	      | _ -> assert false)
	    (fun code -> process ~max_value ~partial ~unit Sparql_endpoint.empty_results Sparql_endpoint.empty_results Sparql_endpoint.empty_results Sparql_endpoint.empty_results)
    in
    let ajax_extent () =
      let sparql_genvar = new Lisql2sparql.genvar in
      let graph_opt (graph_index : Rdf.term int_index) (gp : Sparql.pattern) : Sparql.pattern =
	match s_sparql.Lisql2sparql.focus_graph_opt with
	| None -> gp
	| Some _ ->  Sparql.union (graph_index#map_list (fun (tg,_) -> Sparql.graph (Sparql.term tg) gp))
      in
      let nb_focus_term = focus_term_index#length in
      let max_value = Some nb_focus_term in
      let partial = false in (* relative to computed entities *)
      let unit = `Entities in
      let make_sparql (type a) (index : (a,'b) nested_int_index) config_max filter_constr (lv : Rdf.var list) (make_pattern : a -> Sparql.pattern) =
	assert (lv <> []);
	let main_v = List.hd lv in
	let projections = List.map (fun v -> `Bare, v) lv in
	let gp = Sparql.union
		   (index#map_list
		      (fun (key,(_, graph_index)) ->
		       let pat = graph_opt graph_index (make_pattern key) in
		       if Rdf.config_wikidata_mode#value
		       then pat (* TODO: create an independent option for that because mostly useful when lack of shuffling in endpoint indexes *)
		       else Sparql.subquery
			      (Sparql.select
				 ~distinct:true ~projections
				 ~limit:config_max#value
				 pat))) in
	(Sparql.select
	   ~froms ~projections ~limit:(config_max#value * min 10 nb_focus_term)
	   (Sparql.pattern_of_formula
	      (Sparql.formula_and_list
		 ( Sparql.Pattern gp
		   :: filter_constr sparql_genvar (Sparql.var main_v) constr
		   :: List.map (fun v -> formula_hidden_URIs v) lv )))
	 :> string) in
      let sparql_class =
	make_sparql focus_term_index config_max_classes Lisql2sparql.filter_constr_class
		    Lisql2sparql.WhichClass.pattern_vars
		    (fun t -> Lisql2sparql.WhichClass.pattern_of_term (Some t)) in
      let sparql_prop =
	if Rdf.config_wikidata_mode#value
	then ""
	else make_sparql focus_term_index config_max_properties Lisql2sparql.filter_constr_property
		    Lisql2sparql.WhichProp.pattern_vars
		    (fun t -> Lisql2sparql.WhichProp.pattern_of_term (Some t)) in
      let sparql_pred =
	make_sparql focus_term_index config_max_properties Lisql2sparql.filter_constr_property
		    Lisql2sparql.WhichPred.pattern_vars
		    (fun t -> Lisql2sparql.WhichPred.pattern_of_term (Some t)) in
      let sparql_arg =
	match s_sparql.Lisql2sparql.focus_pred_args_opt with
	| None
	| Some ((Lisql.Class _ | Lisql.Prop _),_) -> "" (* non-reified predicates *)
	| Some (pred,args) -> 
	   make_sparql focus_pred_args_index config_max_properties Lisql2sparql.filter_constr_property
		       Lisql2sparql.WhichArg.pattern_vars
		       (fun lt ->
			let args = List.map2 (fun (arg,_) t -> (arg,t)) args lt in
			Lisql2sparql.WhichArg.pattern_of_pred_args pred args) in
      Sparql_endpoint.ajax_list_in ~fail_on_empty_results:false(*true*) [elt] ajax_pool endpoint [sparql_class; sparql_prop; sparql_pred; sparql_arg]
	(function
	| [results_class; results_prop; results_pred; results_arg] -> process ~max_value ~partial ~unit results_class results_prop results_pred results_arg
	| _ -> assert false)
	(fun _ -> ajax_intent ())
    in
    if focus_term_index#is_empty then
      if some_focus_term_is_blank then ajax_intent ()
      else if not focus_pred_args_index#is_empty then ajax_extent ()
      else self#ajax_index_properties_init constr elt k
    else
      if Sparql_endpoint.config_method_get#value (* to avoid lengthy queries *)
      then ajax_intent ()
      else ajax_extent ()
      end

  method index_modifiers : incr_freq_index =
    let open Lisql in
    let incrs =
      if focus_descr#unconstrained
      then [IncrIn]
      else
	let incrs = [] in
	let incrs =
	  IncrSelection (`Aggreg, []) ::
	  IncrThatIs :: IncrSomethingThatIs :: IncrName "" :: IncrTriplify ::
	    IncrAnd :: IncrDuplicate :: IncrOr :: IncrMaybe :: IncrNot :: IncrChoice ::
	    IncrIn :: IncrInWhichThereIs ::
	    IncrUnselect ::
	    IncrHierarchy (false,false) :: IncrHierarchy (false,true) ::
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
	  IncrForeach ::
	  List.fold_left
	    (fun incrs aggreg ->
	      match Lisql_type.find_insertable_aggreg aggreg focus_type_constraints with
	      | Some aggreg_conv -> IncrAggreg aggreg_conv :: incrs
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
	    [ `Str, 1, 1;
	      `Lang, 1, 1;
	      `Datatype, 1, 1;
	      `IRI, 1, 1;
	      `STRDT, 2, 1;
	      `STRLANG, 2, 1;
	      `Strlen, 1, 1;
	      `Substr2, 2, 1;
	      `Substr3, 3, 1;
	      `Strbefore, 2, 1;
	      `Strafter, 2, 1;
	      `Concat, 2, 1;
	      `Concat, 2, 2;
	      `UCase, 1, 1;
	      `LCase, 1, 1;
	      `Encode_for_URI, 1, 1;
	      `Replace, 3, 1;
	      `Integer, 1, 1;
	      `Decimal, 1, 1;
	      `Double, 1, 1;
	      `Indicator, 1, 1;
	      `Add, 2, 1;
	      `Add, 2, 2;
	      `Sub, 2, 1;
	      `Sub, 2, 2;
	      `Mul, 2, 1;
	      `Mul, 2, 2;
	      `Div, 2, 1;
	      `Div, 2, 2;
	      `Neg, 1, 1;
	      `Abs, 1, 1;
	      `Round, 1, 1;
	      `Ceil, 1, 1;
	      `Floor, 1, 1;
	      `Random2, 2, 1;
	      `Random2, 2, 2;
	      `Date, 1, 1;
	      `Time, 1, 1;
	      `Year, 1, 1;
	      `Month, 1, 1;
	      `Day, 1, 1;
	      `Hours, 1, 1;
	      `Minutes, 1, 1;
	      `Seconds, 1, 1;
	      `TODAY, 0, 0;
	      `NOW, 0, 0;
	      `And, 2, 1;
	      `And, 2, 2;
	      `Or, 2, 1;
	      `Or, 2, 2;
	      `Not, 1, 1;
	      `EQ, 2, 1;
	      `NEQ, 2, 1;
	      `GT, 2, 1;
	      `GEQ, 2, 1;
	      `LT, 2, 1;
	      `LEQ, 2, 1;
	      `BOUND, 1, 1;
	      `IF, 3, 1;
	      `IF, 3, 2;
	      `IF, 3, 3;
	      `IsIRI, 1, 1;
	      `IsBlank, 1, 1;
	      `IsLiteral, 1, 1;
	      `IsNumeric, 1, 1;
	      `StrStarts, 2, 1;
	      `StrEnds, 2, 1;
	      `Contains, 2, 1;
	      `LangMatches, 2, 1;
	      `REGEX, 2, 1;
	      `REGEX_i, 2, 1;
	    ] in
	incrs in
    let valid_incrs =
      List.filter
	(fun incr -> Lisql.insert_increment incr focus <> None)
	incrs in
    let incr_index = new incr_freq_index in
    List.iter (fun incr -> incr_index#add (incr,None)) valid_incrs;
    incr_index
	  
end
