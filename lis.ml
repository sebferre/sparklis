
open Js
open Jsutils

type 'a index = ('a * int) list

(* extraction of the extension and indexes *)

let page_of_results (offset : int) (limit : int) results : Sparql_endpoint.results =
  let open Sparql_endpoint in
  let rec aux offset limit = function
    | [] -> []
    | binding::l ->
      if offset > 0 then aux (offset-1) limit l
      else if limit > 0 then binding :: aux offset (limit-1) l
      else []
  in
  { results with bindings = aux offset limit results.bindings }

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

let cmp_index_elt = fun (x1,f1) (x2,f2) -> Pervasives.compare (f2,x1) (f1,x2)
let cmp_index_elt_rev = fun (x1,f1) (x2,f2) -> Pervasives.compare (f1,x2) (f2,x1)

let index_of_results_column (var : Rdf.var) results : Rdf.term index =
  let open Sparql_endpoint in
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
    let index =
      Hashtbl.fold
	(fun term cpt res -> (term,!cpt)::res)
	ht [] in
    List.sort cmp_index_elt_rev index
  with Not_found ->
    Firebug.console##log(string ("index_of_results_column: missing variable " ^ var));
    []

let index_of_results_2columns (var_x : Rdf.var) (var_count : Rdf.var) results : Rdf.term index =
  let open Sparql_endpoint in
  try
    let i_x = List.assoc var_x results.vars in
    let i_count = try List.assoc var_count results.vars with _ -> -1 in
    let index =
      List.fold_left
	(fun res binding ->
	  match binding.(i_x) with
	    | None -> res
	    | Some x ->
	      let count =
		if i_count < 0
		then 1
		else
		  match binding.(i_count) with
		    | Some (Rdf.Number (f,s,dt)) -> (try int_of_string s with _ -> 0)
		    | Some (Rdf.TypedLiteral (s,dt)) -> (try int_of_string s with _ -> 0)
		    | _ -> 0 in
	      (x, count)::res)
	[] results.bindings in
    index
(*
    List.sort
      (fun (_,f1) (_,f2) -> Pervasives.compare f1 f2)
      index
*)
  with Not_found ->
    Firebug.console##log(string ("index_of_results_2columns: missing variables " ^ var_x ^ ", " ^ var_count));
    []

let index_incr_of_index_term_uri (f : Rdf.uri -> Lisql.increment) (l : Rdf.term index) : Lisql.increment index =
  List.fold_left
    (fun res -> function
      | (Rdf.URI uri, freq) -> (f uri, freq)::res
      | _ -> res)
    [] l

(* LIS navigation places *)

let max_results = 200
let max_classes = 200
let max_properties = 1000

class place (endpoint : string) (focus : Lisql.focus) =
object (self)
  (* essential state *)

  val endpoint = endpoint
  method endpoint = endpoint

  val focus = focus
  method focus = focus

  (* derived state *)

  val mutable focus_term_list : Rdf.term list = []
  method focus_term_list = focus_term_list

  val mutable query_opt : Lisql.sparql_template option = None
  val mutable query_class_opt : Lisql.sparql_template option = None
  val mutable query_prop_has_opt : Lisql.sparql_template option = None
  val mutable query_prop_isof_opt : Lisql.sparql_template option = None

  method private init =
    begin
      let t_list, q_opt, qc_opt, qph_opt, qpi_opt = Lisql.sparql_of_focus focus in
      focus_term_list <- t_list;
      query_opt <- q_opt;
      query_class_opt <- qc_opt;
      query_prop_has_opt <- qph_opt;
      query_prop_isof_opt <- qpi_opt
    end

  initializer self#init

  val mutable results = Sparql_endpoint.empty_results
  val mutable focus_term_index : (Rdf.term * int) list = []


  (* utilities *)

  val ajax_pool = new ajax_pool
  method abort_all_ajax = ajax_pool#abort_all

  (* SPARQL query and results *)

  method ajax_sparql_results term_constr elts (k : string option -> unit) =
    match query_opt with
      | None ->
	results <- Sparql_endpoint.empty_results;
	focus_term_index <-
	  ( match focus_term_list with
	    | [Rdf.Var _] -> []
	    | [term] -> [(term,1)]
	    | _ -> [] );
	k None
      | Some query ->
	let sparql = query ~constr:term_constr ~limit:max_results in
	Sparql_endpoint.ajax_in elts ajax_pool endpoint sparql
	  (fun res ->
	    results <- res;
	    focus_term_index <-
	      ( match focus_term_list with
		| [Rdf.Var v] ->
		  List.filter
		    (function
		      | (Rdf.URI uri, _) when String.contains uri ' ' -> false
	                (* URIs with spaces inside are not allowed in SPARQL queries *)
		      | _ -> true)
		    (index_of_results_column v results)
		| [t] -> [(t, 1)]
		| _ -> [] );
	    k (Some sparql))
	  (fun code ->
	    results <- Sparql_endpoint.empty_results;
	    focus_term_index <- [];
	    k (Some sparql))

  method results_dim = results.Sparql_endpoint.dim
  method results_nb = results.Sparql_endpoint.length
  method results_page offset limit = page_of_results offset limit results

  (* indexes: must be called in the continuation of [ajax_sparql_results] *)

  method index_terms =
    if focus_term_index = []
    then []
    else
      List.rev_map
	(fun (t,freq) -> (Lisql.IncrTerm t, freq))
	focus_term_index

  method ajax_index_terms_init constr elt (k : Lisql.increment index -> unit) =
    let process results_term =
      let list_term = list_of_results_column "term" results_term in
      let list_term =
	List.sort
	  (fun t1 t2 ->
	    Pervasives.compare (* TODO: more efficient and correct way? *)
	      (String.length (Rdf.string_of_term t2), t2)
	      (String.length (Rdf.string_of_term t1), t1))
	  list_term in
      let index =
	List.fold_left
	  (fun res t -> (Lisql.IncrTerm t, 1) :: res)
	  [] list_term in
      k index
    in
    let sparql_term =
      "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> " ^
	"SELECT DISTINCT ?term WHERE { " ^
	Lisql.sparql_search_constr (Rdf.Var "term") constr ^
	" } LIMIT 200" in
    Firebug.console##log(string sparql_term);
    Sparql_endpoint.ajax_in elt ajax_pool endpoint sparql_term
      (fun results_term -> process results_term)
      (fun code -> process Sparql_endpoint.empty_results)

  method ajax_index_properties_init constr elt (k : Lisql.increment index -> unit) =
    let process results_class results_prop =
      let list_class = list_of_results_column "class" results_class in
      let list_prop = list_of_results_column "prop" results_prop in
      let index =
	List.fold_left
	  (fun res -> function
	    | Rdf.URI c -> (Lisql.IncrClass c, 1) :: res
	    | _ -> res)
	  [] list_class in
      let index =
	List.fold_left
	  (fun res -> function
	    | Rdf.URI c -> (Lisql.IncrProp c, 1) :: (Lisql.IncrInvProp c, 1) :: res
	    | _ -> res)
	  index list_prop in
      let index = List.sort cmp_index_elt index in
      k index
    in
    let sparql_class =
      "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> " ^
	"PREFIX owl: <http://www.w3.org/2002/07/owl#> " ^
	"SELECT DISTINCT ?class WHERE { { ?class a rdfs:Class } UNION { ?class a owl:Class } " ^
	Lisql.sparql_constr (Rdf.Var "class") constr ^
	" } LIMIT 500" in
    let sparql_prop =
      "PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> " ^
        "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> " ^
        "PREFIX owl: <http://www.w3.org/2002/07/owl#> " ^
        "SELECT DISTINCT ?prop WHERE { { ?prop a rdf:Property } UNION { ?prop a owl:ObjectProperty } UNION { ?prop a owl:DatatypeProperty } " ^
	Lisql.sparql_constr (Rdf.Var "prop") constr ^
	" } LIMIT 500" in
    Sparql_endpoint.ajax_list_in [elt] ajax_pool endpoint [sparql_class; sparql_prop]
      (function
	| [results_class; results_prop] ->
	  if results_class.Sparql_endpoint.length > 0 || results_prop.Sparql_endpoint.length > 0
	  then process results_class results_prop
	  else
	    let sparql_class = "SELECT DISTINCT ?class WHERE { [] a ?class " ^ Lisql.sparql_constr (Rdf.Var "class") constr ^ " } LIMIT 200" in
	    let sparql_prop = "SELECT DISTINCT ?prop WHERE { [] ?prop [] " ^ Lisql.sparql_constr (Rdf.Var "prop") constr ^ " } LIMIT 200" in
	    Sparql_endpoint.ajax_list_in [elt] ajax_pool endpoint [sparql_class; sparql_prop]
	      (function
		| [results_class; results_prop] -> process results_class results_prop
		| _ -> assert false)
	      (fun code -> process Sparql_endpoint.empty_results Sparql_endpoint.empty_results)
	| _ -> assert false)
      (fun code -> process Sparql_endpoint.empty_results Sparql_endpoint.empty_results)


  method ajax_index_properties constr elt (k : Lisql.increment index -> unit) =
    if focus_term_index = []
    then k []
    else
      let process results_a results_has results_isof =
	let index_a = index_incr_of_index_term_uri (fun c -> Lisql.IncrClass c)
	  (index_of_results_column "class" results_a) in (* increasing *)
	let index_has = index_incr_of_index_term_uri (fun p -> Lisql.IncrProp p)
	  (index_of_results_column "prop" results_has) in (* increasing *)
	let index_isof = index_incr_of_index_term_uri (fun p -> Lisql.IncrInvProp p)
	  (index_of_results_column "prop" results_isof) in (* increasing *)
	let index = List.merge cmp_index_elt index_a (List.merge cmp_index_elt index_has index_isof) in
	k index
      in	
      let sparql_a =
	let lgp = List.map (fun (t,_) -> Lisql.sparql_type t (Rdf.Var "class")) focus_term_index in
	Lisql.sparql_select ~dimensions:["class"] ~limit:max_classes
	  (Lisql.sparql_join [Lisql.sparql_union lgp; Lisql.sparql_constr (Rdf.Var "class") constr]) in
      let sparql_has =
	let lgp = List.map (fun (t,_) -> Lisql.sparql_triple t (Rdf.Var "prop") (Rdf.Bnode "")) focus_term_index in
	Lisql.sparql_select ~dimensions:["prop"] ~limit:max_properties
	  (Lisql.sparql_join [Lisql.sparql_union lgp; Lisql.sparql_constr (Rdf.Var "prop") constr]) in
      let sparql_isof =
	let lgp = List.map (fun (t,_) -> Lisql.sparql_triple (Rdf.Bnode "") (Rdf.Var "prop") t) focus_term_index in
	Lisql.sparql_select ~dimensions:["prop"] ~limit:max_properties
	  (Lisql.sparql_join [Lisql.sparql_union lgp; Lisql.sparql_constr (Rdf.Var "prop") constr]) in
      Sparql_endpoint.ajax_list_in [elt] ajax_pool endpoint [sparql_a; sparql_has; sparql_isof]
	(function
	  | [results_a; results_has; results_isof] ->
	    if results_a.Sparql_endpoint.length > 0 || results_has.Sparql_endpoint.length > 0 || results_isof.Sparql_endpoint.length > 0
	    then process results_a results_has results_isof
	    else
	      ( match query_class_opt, query_prop_has_opt, query_prop_isof_opt with
		| None, None, None -> process Sparql_endpoint.empty_results Sparql_endpoint.empty_results Sparql_endpoint.empty_results
		| Some query_a, Some query_has, Some query_isof ->
		  let sparql_a = query_a ~constr ~limit:max_classes in
		  let sparql_has = query_has ~constr ~limit:max_properties in
		  let sparql_isof = query_isof ~constr ~limit:max_properties in
		  Sparql_endpoint.ajax_list_in [elt] ajax_pool endpoint [sparql_a; sparql_has; sparql_isof]
		    (function
		      | [results_a; results_has; results_isof] -> process results_a results_has results_isof
		      | _ -> assert false)
		    (fun code -> process Sparql_endpoint.empty_results Sparql_endpoint.empty_results Sparql_endpoint.empty_results)
		| _ -> assert false )
	  | _ -> assert false)
	(fun code -> process Sparql_endpoint.empty_results Sparql_endpoint.empty_results Sparql_endpoint.empty_results)

  method index_modifiers =
    let modif_list =
      let open Lisql in
      match focus with
	| AtP1 _ -> [IncrAnd; IncrOr; IncrMaybe; IncrNot]
	| AtS1 (f,ctx) ->
	  let modifs =
	    match f with
	      | Det (An (modif, head), _) ->
		let modifs =
		  if List.exists (function (Rdf.Number _, _) -> true | _ -> false) focus_term_index
		  then List.map (fun g -> IncrAggreg g) [Total; Average; Maximum; Minimum]
		  else [] in
		let modifs =
		  if List.exists (function (Rdf.Number _, _) | (Rdf.PlainLiteral _, _) | (Rdf.TypedLiteral _, _) -> true | _ -> false) focus_term_index
		  then IncrAggreg ListOf :: modifs
		  else modifs in
		let modifs =
		  IncrUnselect :: IncrAggreg NumberOf :: modifs in
		let modifs =
		  IncrOrder Highest :: IncrOrder Lowest :: modifs in
		modifs
	      | _ -> [] in
	  let modifs =
	    if ctx = ReturnX
	    then (* no coordination yet, except Or, on root NP to avoid disconnected graph patterns *)
	      if f = top_s1
	      then modifs
	      else IncrOr :: modifs
	    else IncrAnd :: IncrOr :: IncrMaybe :: IncrNot :: modifs in
	  modifs
	| _ -> [] in
    List.map (fun incr -> (incr,1)) modif_list

end