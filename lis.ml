
open Js

class ['a,'b] index =
object
  val mutable l : ('a * 'b) list = []
  method is_empty : bool = (l=[])
  method length : int = List.length l
  method add (elt_info : 'a * 'b) : unit = l <- elt_info::l
  method fold : 'c. ('c -> 'a * 'b -> 'c) -> 'c -> 'c =
    fun f init -> List.fold_left f init l
  method iter : ('a * 'b -> unit) -> unit =
    fun f -> List.iter f l
  method map : 'c. ('a * 'b -> 'c) -> 'c list =
    fun f -> List.map f l
end
  
class ['a] int_index = ['a,int] index

type freq_unit = [`Results | `Entities | `Concepts | `Modifiers]
type freq = { value : int; max_value : int option; partial : bool; unit : freq_unit }
class incr_freq_index = [Lisql.increment, freq option] index

(* configuration *)

let config_intentional_init_concepts = new Config.boolean_input ~key:"intentional_init_concepts" ~input_selector:"#input-intentional-init-concepts" ~default:true ()
let config_regexp_hidden_URIs = new Config.string_input ~key:"regexp_hidden_URIs" ~input_selector:"#input-regexp-hidden-uris" ~default:"^(http://www.w3.org/2002/07/owl#|http://www.openlinksw.com/|nodeID://)" ()
let config_max_results = new Config.integer_input ~key:"max_results" ~input_selector:"#input-max-results" ~min:1 ~default:200 ()
let config_max_classes = new Config.integer_input ~key:"max_classes" ~input_selector:"#input-max-classes" ~min:0 ~default:200 ()
let config_max_properties = new Config.integer_input ~key:"max_properties" ~input_selector:"#input-max-properties" ~min:0 ~default:200 ()


let formula_hidden_URIs_term (tx : Sparql.term) : Sparql.formula =
  match config_regexp_hidden_URIs#value with
  | "" -> Sparql.True
  | re -> Sparql.(Filter (log_not (expr_regex (expr_func "str" [(tx :> expr)]) re)))
let formula_hidden_URIs (v : string) : Sparql.formula =
  formula_hidden_URIs_term (Sparql.var v :> Sparql.term)

let filter_hidden_URIs (v : string) : string =
  (Sparql.pattern_of_formula (formula_hidden_URIs v) :> string)
    
(* extraction of the extension and indexes *)

let lexicon_enqueue_term = function
  | Rdf.URI uri -> Lexicon.config_entity_lexicon#value#enqueue uri
  | Rdf.TypedLiteral (_,dt) -> Lexicon.config_class_lexicon#value#enqueue dt
  | _ -> ()

let page_of_results (offset : int) (limit : int) results (k : Sparql_endpoint.results -> unit) : unit =
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
  let partial_bindings = List.rev (aux offset limit [] results.bindings) in
  Lexicon.config_class_lexicon#value#sync (fun () ->
    Lexicon.config_entity_lexicon#value#sync (fun () ->
      k { results with bindings = partial_bindings }))

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

let index_of_results_column (var : Rdf.var) results : Rdf.term int_index =
  let open Sparql_endpoint in
  let index = new int_index in
  try
    let i = List.assoc var results.vars in
    let ht = Hashtbl.create 1000 in
    List.iter
      (fun binding ->
	match binding.(i) with
	  | None -> ()
	  | Some term ->
	    try
	      let cpt = Hashtbl.find ht term in
	      incr cpt
	    with Not_found ->
	      Hashtbl.add ht term (ref 1))
      results.bindings;
    Hashtbl.iter
      (fun term cpt -> index#add (term,!cpt))
      ht;
    index
  with Not_found ->
    Firebug.console##log(string ("index_of_results_column: missing variable " ^ var));
    index

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

(*      
let index_incr_of_index_term_uri ~max_value ~partial ~unit (f : Rdf.uri -> Lisql.increment) (int_index : Rdf.term int_index) : incr_freq_index =
  let incr_index = new incr_freq_index in
  int_index#iter
    (function
      | (Rdf.URI uri, freq) -> incr_index#add (f uri, Some { value=freq; max_value; partial; unit })
      | _ -> ());
  incr_index
*)
      
(* LIS navigation places *)

class place (endpoint : string) (focus : Lisql.focus) =
  let focus_term, s_annot = Lisql_annot.annot_focus focus in
  let focus_incr = match focus_term with `IdIncr _ | `TermIncr _ -> true | _ -> false in
object (self)
  (* essential state *)

  val endpoint = endpoint
  method endpoint = endpoint

  method focus = focus
  method query = s_annot

  (* derived state *)

  val mutable id_labelling = new Lisql2nl.id_labelling []
  method id_labelling = id_labelling

  val mutable focus_term_list : Rdf.term list = []
  method focus_term_list = focus_term_list
    
  val mutable query_opt : Lisql2sparql.template option = None
  val mutable query_class_opt : Lisql2sparql.template option = None
  val mutable query_prop_has_opt : Lisql2sparql.template option = None
  val mutable query_prop_isof_opt : Lisql2sparql.template option = None

  val mutable seq_view : Lisql_annot.seq_view = 0, Lisql_annot.Unit

  method private init =
    begin
      id_labelling <- Lisql2nl.id_labelling_of_s_annot Lisql2nl.config_lang#grammar s_annot;
      let t_list, q_opt, qc_opt, qph_opt, qpi_opt, seq_v =
	Lisql2sparql.s_annot id_labelling focus_term s_annot in
      focus_term_list <- t_list;
      query_opt <- q_opt;
      query_class_opt <- qc_opt;
      query_prop_has_opt <- qph_opt;
      query_prop_isof_opt <- qpi_opt;
      seq_view <- seq_v
    end

  initializer self#init

  (* utilities *)

  val ajax_pool = new Sparql_endpoint.ajax_pool
  method abort_all_ajax = ajax_pool#abort_all

  (* SPARQL query and results *)

  val mutable results = Sparql_endpoint.empty_results
  val mutable results_typing : Lisql_type.datatype list array = [||]
  val mutable focus_type_constraints : Lisql_type.focus_type_constraints = Lisql_type.default_focus_type_constraints
  val mutable focus_term_index : Rdf.term int_index = new int_index
  val mutable some_focus_term_is_blank : bool = false

  method id_typing (id : Lisql.id) : Lisql_type.datatype list =
    let v = id_labelling#get_id_var id in
    try
      let i = List.assoc v results.Sparql_endpoint.vars in
      results_typing.(i)
    with Not_found ->
      Jsutils.firebug ("No datatype for id #" ^ string_of_int id);
      []
    
  method ajax_sparql_results term_constr elts (k : string option -> unit) =
    (* re-initializing *)
    results <- Sparql_endpoint.empty_results;
    results_typing <- [||];
    focus_term_index <- new int_index;
    some_focus_term_is_blank <- false;
    (* computing results and derived attributes *)
    match query_opt with
      | None ->
	( match focus_term_list with
	| [Rdf.Var _] -> ()
	| [Rdf.Bnode _] ->  (* should not happen *)
	  Firebug.console##log(string "no query and focus_term_list is a Bnode");
	  some_focus_term_is_blank <- true
	| [term] -> focus_term_index#add (term,1)
	| _ -> () );
	k None
      | Some query ->
	let limit = config_max_results#value in
	let sparql = query ~hook:(fun tx -> Lisql2sparql.filter_constr_entity tx term_constr) ~limit in
	Sparql_endpoint.ajax_in ~send_results_to_yasgui:true elts ajax_pool endpoint sparql
	  (fun res ->
	    results <- res;
	    results_typing <- Lisql_type.of_sparql_results res;
	    focus_type_constraints <- Lisql_type.of_focus
	      (fun id -> Some (self#id_typing id))
	      focus;
	    ( match focus_term_list with
	    | [Rdf.Var v] ->
	      let index = index_of_results_column v results in
	      index#iter (* avoiding non recursive terminal fold_right *)
		(fun (t,freq) ->
		  match t with
		  | Rdf.URI uri when String.contains uri ' ' -> ()
	              (* URIs with spaces inside are not allowed in SPARQL queries *)
		  | Rdf.Bnode _ -> some_focus_term_is_blank <- true
		      (* blank nodes are not allowed in SPARQL queries *)
		  | _ -> focus_term_index#add (t,freq))
	    | [Rdf.Bnode _] ->
	      Firebug.console##log(string "focus_term_list is a Bnode");
	      some_focus_term_is_blank <- true (* should not happen *)
	    | [t] -> focus_term_index#add (t, 1)
	    | _ -> () );
	    k (Some sparql))
	  (fun code -> k (Some sparql))

  method partial_results = (results.Sparql_endpoint.length = config_max_results#value)
  method results_dim = results.Sparql_endpoint.dim
  method results_nb = results.Sparql_endpoint.length
  method results_page offset limit k = page_of_results offset limit results k

  (* indexes: must be called in the continuation of [ajax_sparql_results] *)

(* moved to next method *)
(*
  method index_ids : incr_freq_index =
    let index = new incr_freq_index in
    ( match focus_term_list with
    | [term] ->
      if focus_incr then
	begin
	  let dim = results.Sparql_endpoint.dim in
	  let vars = results.Sparql_endpoint.vars in
	  let freqs = Array.make dim 0 in
	  List.iter
	    (fun binding ->
	      let t_focus_opt =
		match term with
		| Rdf.Var v -> binding.(List.assoc v vars)
		| _ -> Some term in
	      Array.iteri
		(fun i t_opt ->
		  match t_opt, t_focus_opt with
		  | Some t1, Some t2 when t1=t2 -> freqs.(i) <- freqs.(i) + 1
		  | _ -> ())
		binding)
	    results.Sparql_endpoint.bindings;
	  let max_value = None (*Some results.Sparql_endpoint.length*) in
	  let partial = self#partial_results in
	  let unit = `Results in
	  List.iter
	    (fun i ->
	      if freqs.(i) <> 0 then
		let v = try Common.list_rev_assoc i vars with _ -> assert false in
		if term <> (Rdf.Var v) then
		  (try
		     let id = id_labelling#get_var_id v in
		     index#add (Lisql.IncrId id, Some { value=freqs.(i); max_value; partial; unit })
		   with _ -> ()))  (* ex: aggregation variables *)
	    (Common.from_downto (dim-1) 0)
	end;
      if Lisql.is_undef_expr_focus focus then
	begin
	  List.iter
	    (fun id -> (* TODO: filter according to empirical type *)
	    (*let id = id_labelling#get_var_id v in*)
	      let ldt = self#id_typing id in
	      if List.exists (fun dt -> Lisql_type.is_insertable (None, dt) focus_type_constraints) ldt then
		index#add (Lisql.IncrId id, None))
	    (Lisql_annot.seq_view_defs seq_view)
	end
    | _ -> () );
    index
*)

  method index_terms_inputs_ids (k : partial:bool -> incr_freq_index -> unit) =
    let max_value = None (*Some self#results_nb*) in
    let partial = self#partial_results in
    let unit = `Results in
    let incr_index = new incr_freq_index in
    (* adding term increments *)
    focus_term_index#iter (*rev_map*)
      (fun (t,freq) ->
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
    ( match focus_term_list with
    | [term] ->
      if focus_incr then
	begin
	  let dim = results.Sparql_endpoint.dim in
	  let vars = results.Sparql_endpoint.vars in
	  let freqs = Array.make dim 0 in
	  List.iter
	    (fun binding ->
	      let t_focus_opt =
		match term with
		| Rdf.Var v -> binding.(List.assoc v vars)
		| _ -> Some term in
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
		     incr_index#add (Lisql.IncrId id, Some { value=freqs.(i); max_value; partial; unit })
		   with _ -> ()))  (* ex: aggregation variables *)
	    (Common.from_downto (dim-1) 0)
	end;
      if Lisql.is_undef_expr_focus focus then
	begin
	  List.iter
	    (fun id -> (* TODO: filter according to empirical type *)
	    (*let id = id_labelling#get_var_id v in*)
	      let ldt = self#id_typing id in
	      if List.exists (fun dt -> Lisql_type.is_insertable (None, dt) focus_type_constraints) ldt then
		incr_index#add (Lisql.IncrId id, None))
	    (Lisql_annot.seq_view_defs seq_view)
	end
    | _ -> () );
    (* synchronizing lexicons and continuing *)
    Lexicon.config_entity_lexicon#value#sync (fun () ->
      Lexicon.config_class_lexicon#value#sync (fun () ->
	k ~partial incr_index))

  method ajax_index_terms_init constr elt (k : partial:bool -> incr_freq_index -> unit) =
    let process results_term =
      let list_term = list_of_results_column "term" results_term in
      let max_value = None in
      let partial = results_term.Sparql_endpoint.length = config_max_results#value in
      let unit = `Results in
      let incr_index = new incr_freq_index in
      List.iter
	(fun t -> incr_index#add (Lisql.IncrTerm t, Some { value=1; max_value; partial; unit }))
	list_term;
      k ~partial incr_index
    in
    let sparql_term =
	"SELECT DISTINCT ?term WHERE { " ^
	  (Sparql.pattern_of_formula (Lisql2sparql.search_constr (Sparql.var "term" :> Sparql.term) constr) :> string) ^
	  filter_hidden_URIs "term" ^
	  " FILTER (!IsBlank(?term)) } LIMIT " ^ string_of_int config_max_results#value in
    Sparql_endpoint.ajax_in ~tentative:true elt ajax_pool endpoint sparql_term (* tentative because uses a non-standard feature 'bif:contains' *)
      (fun results_term -> process results_term)
      (fun code -> (* trying standard yet inefficient approach *)
	let sparql_term =
	  "SELECT DISTINCT ?term WHERE { " ^
	    (Sparql.pattern_of_formula
	       (Sparql.formula_and_list
		  [ Sparql.Pattern (Sparql.something (Sparql.var "term" :> Sparql.term));
		    Lisql2sparql.filter_constr_entity (Sparql.var "term" :> Sparql.term) constr;
		    formula_hidden_URIs "term" ]) :> string) ^
	    " } LIMIT " ^  string_of_int config_max_results#value in
	Sparql_endpoint.ajax_in elt ajax_pool endpoint sparql_term
	  (fun results_term -> process results_term)
	  (fun code -> process Sparql_endpoint.empty_results))

  method ajax_index_properties_init constr elt (k : partial:bool -> incr_freq_index -> unit) =
    let process results_class results_prop =
      let max_value = None in
      let partial_class = results_class.Sparql_endpoint.length = config_max_classes#value in
      let partial_prop = results_prop.Sparql_endpoint.length = config_max_properties#value in
      let partial = partial_class || partial_prop in
      let unit = `Entities in
      let int_index_class = index_of_results_column "class" results_class in
      let int_index_prop = index_of_results_column "prop" results_prop in
      let incr_index = new incr_freq_index in
      int_index_class#iter
	(function
	| (Rdf.URI uri, count) ->
	  Lexicon.config_class_lexicon#value#enqueue uri;
	  incr_index#add (Lisql.IncrType uri, Some { value=count; max_value; partial=partial_prop; unit })
	| _ -> ());
      int_index_prop#iter
	(function
	| (Rdf.URI uri, count) ->
	  Lexicon.config_property_lexicon#value#enqueue uri;
	  let freq = { value=count; max_value; partial=partial_prop; unit } in
	  incr_index#add (Lisql.IncrRel (uri,Lisql.Fwd), Some freq);
	  incr_index#add (Lisql.IncrRel (uri,Lisql.Bwd), Some freq)
	| _ -> ());
  (*
      let index_a = index_incr_of_index_term_uri ~max_value ~partial:partial_class ~unit
	(fun c ->
	  Lexicon.config_class_lexicon#value#enqueue c;
	  Lisql.IncrType c)
	int_index_class in
      let index_has = index_incr_of_index_term_uri ~max_value ~partial:partial_prop ~unit
	(fun p ->
	  Lexicon.config_property_lexicon#value#enqueue p;
	  Lisql.IncrRel (p,Lisql.Fwd))
	int_index_prop in
      let index_isof = index_incr_of_index_term_uri ~max_value ~partial:partial_prop ~unit
	(fun p ->
	  Lisql.IncrRel (p,Lisql.Bwd))
	int_index_prop in
      let index = index_a @ index_has @ index_isof in
  *)
      Lexicon.config_class_lexicon#value#sync (fun () ->
	Lexicon.config_property_lexicon#value#sync (fun () ->
	  k ~partial incr_index))
    in
    let ajax_extent () =
      let sparql_class =
	"SELECT DISTINCT ?class WHERE { [] a ?class " ^
	  (Sparql.pattern_of_formula (Lisql2sparql.filter_constr_class (Sparql.var "class" :> Sparql.term) constr) :> string) ^
	  filter_hidden_URIs "class" ^
	  " } LIMIT " ^ string_of_int config_max_classes#value in
      let sparql_prop =
	"SELECT DISTINCT ?prop WHERE { [] ?prop [] " ^
	  (Sparql.pattern_of_formula (Lisql2sparql.filter_constr_property (Sparql.var "prop" :> Sparql.term) constr) :> string) ^
	  filter_hidden_URIs "prop" ^
	  " } LIMIT " ^ string_of_int config_max_properties#value in
      Sparql_endpoint.ajax_list_in [elt] ajax_pool endpoint [sparql_class; sparql_prop]
	(function
	| [results_class; results_prop] -> process results_class results_prop
	| _ -> assert false)
	(fun code -> process Sparql_endpoint.empty_results Sparql_endpoint.empty_results)
    in
    let ajax_intent () =
      let sparql_class =
	"SELECT DISTINCT ?class WHERE { { ?class a rdfs:Class } UNION { ?class a owl:Class } " ^
	  (* "FILTER EXISTS { [] a ?class } " ^ *) (* 'EXISTS' not widely supported, and also fails for pure ontologies! *)
	  (Sparql.pattern_of_formula (Lisql2sparql.filter_constr_class (Sparql.var "class" :> Sparql.term) constr) :> string) ^
	  filter_hidden_URIs "class" ^
	  " } LIMIT " ^ string_of_int config_max_classes#value in
      let sparql_prop =
	"SELECT DISTINCT ?prop WHERE { { ?prop a rdf:Property } UNION { ?prop a owl:ObjectProperty } UNION { ?prop a owl:DatatypeProperty } " ^
	  (* "FILTER EXISTS { [] ?prop [] } " ^ (* too costly *) *)
	  (Sparql.pattern_of_formula (Lisql2sparql.filter_constr_property (Sparql.var "prop" :> Sparql.term) constr) :> string) ^
	  filter_hidden_URIs "prop" ^
	  " } LIMIT " ^ string_of_int config_max_properties#value in
      Sparql_endpoint.ajax_list_in ~tentative:true ~fail_on_empty_results:true [elt] ajax_pool endpoint [sparql_class; sparql_prop]
	(function
	| [results_class; results_prop] -> process results_class results_prop
	| _ -> assert false)
	(fun _ -> ajax_extent ()) (* looking at facts *)
    in
    if config_intentional_init_concepts#value
    then ajax_intent ()
    else ajax_extent ()

  method ajax_index_properties constr elt (k : partial:bool -> incr_freq_index -> unit) =
    let process ~max_value ~partial ~unit results_a results_has results_isof =
      let partial_a = partial || results_a.Sparql_endpoint.length = config_max_classes#value in
      let partial_has = partial || results_has.Sparql_endpoint.length = config_max_properties#value in
      let partial_isof = partial || results_isof.Sparql_endpoint.length = config_max_properties#value in
      let partial = partial_a || partial_has || partial_isof in
      let int_index_a = index_of_results_column "class" results_a in
      let int_index_has = index_of_results_column "prop" results_has in
      let int_index_isof = index_of_results_column "prop" results_isof in
      let incr_index = new incr_freq_index in
      int_index_a#iter
	(function
	| (Rdf.URI uri, count) ->
	  Lexicon.config_class_lexicon#value#enqueue uri;
	  incr_index#add (Lisql.IncrType uri, Some { value=count; max_value; partial=partial_a; unit })
	| _ -> ());
      int_index_has#iter
	(function
	| (Rdf.URI uri, count) ->
	  Lexicon.config_property_lexicon#value#enqueue uri;
	  incr_index#add (Lisql.IncrRel (uri,Lisql.Fwd), Some { value=count; max_value; partial=partial_has; unit })
	| _ -> ());
      int_index_isof#iter
	(function
	| (Rdf.URI uri, count) ->
	  Lexicon.config_property_lexicon#value#enqueue uri;
	  incr_index#add (Lisql.IncrRel (uri,Lisql.Bwd), Some { value=count; max_value; partial=partial_has; unit })
	| _ -> ());
(*	
      let index_a = index_incr_of_index_term_uri ~max_value ~partial:partial_a ~unit
	(fun c ->
	  Lexicon.config_class_lexicon#value#enqueue c;
	  Lisql.IncrType c)
	(index_of_results_column "class" results_a) in (* increasing *)
      let index_has = index_incr_of_index_term_uri ~max_value ~partial:partial_has ~unit
	(fun p ->
	  Lexicon.config_property_lexicon#value#enqueue p;
	  Lisql.IncrRel (p,Lisql.Fwd))
	(index_of_results_column "prop" results_has) in (* increasing *)
      let index_isof = index_incr_of_index_term_uri ~max_value ~partial:partial_isof ~unit
	(fun p -> 
	  Lexicon.config_property_lexicon#value#enqueue p;
	  Lisql.IncrRel (p,Lisql.Bwd))
	(index_of_results_column "prop" results_isof) in (* increasing *)
      let index = index_a @ index_has @ index_isof in
*)
      if not int_index_isof#is_empty then incr_index#add (Lisql.IncrTriple Lisql.O, None);
      if not int_index_has#is_empty then incr_index#add (Lisql.IncrTriple Lisql.S, None);
      (*
	    let index = if index_isof = [] then index else (Lisql.IncrTriple Lisql.O, None) :: index in
      let index = if index_has = [] then index else (Lisql.IncrTriple Lisql.S, None) :: index in
      *)
      Lexicon.config_class_lexicon#value#sync (fun () ->
	Lexicon.config_property_lexicon#value#sync (fun () ->
	  k ~partial incr_index))
    in
    let ajax_intent () =
      let max_value = None in
      let partial = self#partial_results in
      let unit = `Results in
      match query_class_opt, query_prop_has_opt, query_prop_isof_opt with
	| None, None, None -> process ~max_value ~partial ~unit Sparql_endpoint.empty_results Sparql_endpoint.empty_results Sparql_endpoint.empty_results
	| Some query_a, Some query_has, Some query_isof ->
	  let sparql_a = query_a
	    ~hook:(fun tx -> Sparql.formula_and (Lisql2sparql.filter_constr_class tx constr) (formula_hidden_URIs_term tx))
	    ~limit:config_max_classes#value in
	  let sparql_has = query_has
	    ~hook:(fun tx -> Sparql.formula_and (Lisql2sparql.filter_constr_property tx constr) (formula_hidden_URIs_term tx))
	    ~limit:config_max_properties#value in
	  let sparql_isof = query_isof
	    ~hook:(fun tx -> Sparql.formula_and (Lisql2sparql.filter_constr_property tx constr) (formula_hidden_URIs_term tx))
	    ~limit:config_max_properties#value in
	  Sparql_endpoint.ajax_list_in [elt] ajax_pool endpoint [sparql_a; sparql_has; sparql_isof]
	    (function
	      | [results_a; results_has; results_isof] -> process ~max_value ~partial ~unit results_a results_has results_isof
	      | _ -> assert false)
	    (fun code -> process ~max_value ~partial ~unit Sparql_endpoint.empty_results Sparql_endpoint.empty_results Sparql_endpoint.empty_results)
	| _ -> assert false
    in
    let ajax_extent () =
      let nb_focus_term = focus_term_index#length in
      let max_value = Some nb_focus_term in
      let partial = false in (* relative to computed entities *)
      let unit = `Entities in
      let sparql_a =
	let gp = Sparql.union (focus_term_index#map
				 (fun (t,_) ->
				   Sparql.subquery
				     (Sparql.select ~distinct:true ~projections:[`Bare, "class"] ~limit:(config_max_classes#value / min 10 nb_focus_term)
					(Sparql.rdf_type (Sparql.term t) (Sparql.var "class" :> Sparql.term))))) in
	(Sparql.select ~projections:[`Bare, "class"] ~limit:config_max_classes#value
	   (Sparql.pattern_of_formula
	      (Sparql.formula_and_list
		 [ Sparql.Pattern gp;
		   (Lisql2sparql.filter_constr_class (Sparql.var "class" :> Sparql.term) constr);
		   formula_hidden_URIs "class" ]))
	 :> string) in
      let sparql_has =
	let gp =
	  Sparql.union (focus_term_index#map
			  (fun (t,_) ->
			    Sparql.subquery
			      (Sparql.select ~distinct:true ~projections:[`Bare, "prop"] ~limit:(config_max_properties#value / min 10 nb_focus_term)
				 (Sparql.triple (Sparql.term t) (Sparql.var "prop" :> Sparql.term) (Sparql.bnode ""))))) in
	(Sparql.select ~projections:[`Bare, "prop"] ~limit:config_max_properties#value
	   (Sparql.pattern_of_formula
	      (Sparql.formula_and_list
		 [ Sparql.Pattern gp;
		   Lisql2sparql.filter_constr_property (Sparql.var "prop" :> Sparql.term) constr;
		   formula_hidden_URIs "prop" ]))
	 :> string) in
      let sparql_isof =
	let gp = Sparql.union (focus_term_index#map
				 (fun (t,_) ->
				   Sparql.subquery
				     (Sparql.select ~distinct:true ~projections:[`Bare, "prop"] ~limit:(config_max_properties#value / min 10 nb_focus_term)
					(Sparql.triple (Sparql.bnode "") (Sparql.var "prop" :> Sparql.term) (Sparql.term t))))) in
	(Sparql.select ~projections:[`Bare, "prop"] ~limit:config_max_properties#value
	   (Sparql.pattern_of_formula
	      (Sparql.formula_and_list
		 [ Sparql.Pattern gp;
		   Lisql2sparql.filter_constr_property (Sparql.var "prop" :> Sparql.term) constr;
		   formula_hidden_URIs "prop" ]))
	 :> string) in
      Sparql_endpoint.ajax_list_in ~fail_on_empty_results:true [elt] ajax_pool endpoint [sparql_a; sparql_has; sparql_isof]
	(function
	| [results_a; results_has; results_isof] -> process ~max_value ~partial ~unit results_a results_has results_isof
	| _ -> assert false)
	(fun _ -> ajax_intent ())
    in
    if not focus_incr then k ~partial:false (new incr_freq_index) (* only constraints on aggregations (HAVING clause) *)
    else if focus_term_index#is_empty then
      if some_focus_term_is_blank
      then ajax_intent ()
      else self#ajax_index_properties_init constr elt k
    else
      if Sparql_endpoint.config_method_get#value (* to avoid lengthy queries *)
      then ajax_intent ()
      else ajax_extent ()

  method index_modifiers ~init : incr_freq_index =
    let open Lisql in
    let incrs =
      if init
      then [IncrIs]
      else
	let incrs = [] in
	let incrs =
	  IncrIs :: IncrName "" :: IncrTriplify ::
	    IncrAnd :: IncrOr :: IncrMaybe :: IncrNot ::
	    IncrUnselect ::
	    incrs in
	let incrs =
	  List.fold_left
	    (fun incrs order -> IncrOrder (Lisql_type.find_insertable_order order focus_type_constraints) :: incrs)
	    incrs
	    [ Highest None; Lowest None ] in
	let incrs =
	  match Lisql_annot.seq_view_available_dims seq_view with
	  | None -> incrs
	  | Some ids ->
	      IncrForeachResult ::
	      List.fold_right
	      (fun id incrs -> IncrForeach id :: incrs)
	      ids incrs in
	let incrs =
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
	      if Lisql_type.is_insertable_func_pos func pos focus_type_constraints
	      then
		let is_pred = Lisql_type.is_predicate func in
		IncrFuncArg (is_pred,func,arity,pos) :: incrs
	      else incrs)
	    incrs
	    [ `Str, 1, 1;
	      `Lang, 1, 1;
	      `Datatype, 1, 1;
	      `IRI, 1, 1;
	      `STRDT, 1, 1;
	      `STRLANG, 1, 1;
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
