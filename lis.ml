
open Js
open Jsutils

type index = (Lisql.increment * int) list

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
    List.sort
      (fun t1 t2 -> Pervasives.compare t2 t1)
      (List.fold_left
	 (fun res binding ->
	   match binding.(i) with
	     | None -> res
	     | Some t -> t::res)
	 [] results.bindings)
  with Not_found ->
    Firebug.console##log(string ("list_of_results_column: missing variable " ^ var));
    []

let index_of_results_column (var : Rdf.var) results : (Rdf.term * int) list =
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
    List.sort
      (fun (i1,f1) (i2,f2) -> Pervasives.compare (f1,i2) (f2,i1))
      index
  with Not_found ->
    Firebug.console##log(string ("index_of_results_column: missing variable " ^ var));
    []

let index_of_results_2columns (var_x : Rdf.var) (var_count : Rdf.var) results : (Rdf.term * int) list =
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

  val mutable focus_term_opt : Rdf.term option = None
  method focus_term_opt = focus_term_opt

  val mutable query_opt : Lisql.sparql_template option = None
  val mutable query_class_opt : Lisql.sparql_template option = None
  val mutable query_prop_has_opt : Lisql.sparql_template option = None
  val mutable query_prop_isof_opt : Lisql.sparql_template option = None

  method private init =
    begin
      let t_opt, q_opt, qc_opt, qph_opt, qpi_opt = Lisql.sparql_of_focus focus in
      focus_term_opt <- t_opt;
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
	  ( match focus_term_opt with
	    | None -> []
	    | Some (Rdf.Var _) -> []
	    | Some term -> [(term,1)] );
	k None
      | Some query ->
	let sparql = query ~constr:term_constr ~limit:max_results in
	Sparql_endpoint.ajax_in elts ajax_pool endpoint sparql
	  (fun res ->
	    results <- res;
	    focus_term_index <-
	      ( match focus_term_opt with
		| None -> []
		| Some (Rdf.Var v) ->
		  List.filter
		    (function
		      | (Rdf.URI uri, _) when String.contains uri ' ' -> false
	                (* URIs with spaces inside are not allowed in SPARQL queries *)
		      | _ -> true)
		    (index_of_results_column v results)
		| Some t -> [(t, 1)] );
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
    List.rev_map
      (fun (t,freq) -> (Lisql.IncrTerm t, freq))
      focus_term_index

  method ajax_index_classes_init class_constr elt (k : index -> unit) =
    let process results =
      let class_list = list_of_results_column "class" results in
      let index =
	List.fold_left
	  (fun res -> function
	    | Rdf.URI c -> (Lisql.IncrClass c, 1) :: res
	    | _ -> res)
	  [] class_list in
      k index
    in
    let sparql =
      "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> " ^
	"PREFIX owl: <http://www.w3.org/2002/07/owl#> " ^
	"SELECT DISTINCT ?class WHERE { { ?class a rdfs:Class } UNION { ?class a owl:Class } " ^
	Lisql.sparql_constr (Rdf.Var "class") class_constr ^
	" } LIMIT 1000" in
    Sparql_endpoint.ajax_in [elt] ajax_pool endpoint sparql
      (fun results ->
	if results.Sparql_endpoint.length > 0
	then process results
	else
	  let sparql = "SELECT DISTINCT ?class WHERE { [] a ?class " ^ Lisql.sparql_constr (Rdf.Var "class") class_constr ^ " } LIMIT 200" in
	  Sparql_endpoint.ajax_in [elt] ajax_pool endpoint sparql
	    (fun results -> process results)
	    (fun code -> process Sparql_endpoint.empty_results))
      (fun code -> process Sparql_endpoint.empty_results)

  method ajax_index_properties_init property_constr elt (k : index -> unit) =
    let process results =
      let prop_list = list_of_results_column "prop" results in
      let index =
	List.fold_left
	  (fun res -> function
	    | Rdf.URI c -> (Lisql.IncrProp c, 1) :: (Lisql.IncrInvProp c, 1) :: res
	    | _ -> res)
	  [] prop_list in
      k index
    in
    let sparql =
      "PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> " ^
        "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> " ^
        "PREFIX owl: <http://www.w3.org/2002/07/owl#> " ^
        "SELECT DISTINCT ?prop WHERE { { ?prop a rdf:Property } UNION { ?prop a owl:ObjectProperty } UNION { ?prop a owl:DatatypeProperty } " ^
	Lisql.sparql_constr (Rdf.Var "prop") property_constr ^
	" } LIMIT 1000" in
    Sparql_endpoint.ajax_in [elt] ajax_pool endpoint sparql
      (fun results ->
	if results.Sparql_endpoint.length > 0
	then process results
	else
	  let sparql = "SELECT DISTINCT ?prop WHERE { [] ?prop [] " ^ Lisql.sparql_constr (Rdf.Var "prop") property_constr ^ " } LIMIT 200" in
	  Sparql_endpoint.ajax_in [elt] ajax_pool endpoint sparql
	    (fun results -> process results)
	    (fun code -> process Sparql_endpoint.empty_results))
      (fun code -> process Sparql_endpoint.empty_results)

  method ajax_index_classes class_constr elt (k : index -> unit) =
    let process results =
      let class_index = index_of_results_column "class" results in
      let index =
	List.fold_left
	  (fun res -> function
	    | (Rdf.URI c, freq) -> (Lisql.IncrClass c, freq) :: res
	    | _ -> res)
	  [] class_index in
      k index
    in
(*
	  let sparql =
	    let vals = String.concat " " (List.map (fun (t,_) -> sparql_term t) focus_term_index) in
	    "SELECT DISTINCT ?class (COUNT(DISTINCT ?focus) AS ?freq) WHERE { VALUES ?focus { " ^ vals ^ " } ?focus a ?class } GROUP BY ?class ORDER BY DESC(?freq) ?class LIMIT " ^ string_of_int max_classes in
*)
    let sparql =
      let lgp = List.map (fun (t,_) -> Lisql.sparql_triple t (Rdf.URI "a") (Rdf.Var "class")) focus_term_index in
      Lisql.sparql_select ~dimensions:["class"] ~limit:max_classes
	(Lisql.sparql_join [Lisql.sparql_union lgp; Lisql.sparql_constr (Rdf.Var "class") class_constr]) in
    Sparql_endpoint.ajax_in [elt] ajax_pool endpoint sparql
      (fun results ->
	if results.Sparql_endpoint.length > 0
	then process results
	else
	  match query_class_opt with
	    | None -> process Sparql_endpoint.empty_results
	    | Some query ->
	      let sparql = query ~constr:class_constr ~limit:max_classes in
	      Sparql_endpoint.ajax_in [elt] ajax_pool endpoint sparql
		(fun results -> process results)
		(fun code -> process Sparql_endpoint.empty_results))
      (fun code -> process Sparql_endpoint.empty_results)

  method ajax_index_properties property_constr elt (k : index -> unit) =
    let process results_has results_isof =
      let index_has = index_of_results_column "prop" results_has in (* increasing *)
      let index_isof = index_of_results_column "prop" results_isof in (* increasing *)
      let index =
	let rec aux acc l1 l2 =
	  match l1, l2 with
	    | (Rdf.URI c1, freq1)::r1, (_, freq2)::r2 when freq1 <= freq2 -> aux ((Lisql.IncrProp c1, freq1)::acc) r1 l2
	    | (_, freq1)::r1, (Rdf.URI c2, freq2)::r2 when freq1 > freq2 -> aux ((Lisql.IncrInvProp c2, freq2)::acc) l1 r2
	    | (Rdf.URI c1, freq1)::r1, [] -> aux ((Lisql.IncrProp c1, freq1)::acc) r1 []
	    | [], (Rdf.URI c2, freq2)::r2 -> aux ((Lisql.IncrInvProp c2, freq2)::acc) [] r2
	    | [], [] -> acc
	    | _ -> acc (* assert false *) in
	aux [] index_has index_isof in
      k index
    in	
(*
      let vals = String.concat " " (List.map (fun (t,_) -> sparql_term t) focus_term_index) in
      let sparql_has = "SELECT DISTINCT ?prop (COUNT (DISTINCT ?focus) AS ?freq) WHERE { VALUES ?focus { " ^ vals ^ " } ?focus ?prop [] } GROUP BY ?prop ORDER BY DESC(?freq) ?prop LIMIT " ^ string_of_int max_properties in
      let sparql_isof = "SELECT DISTINCT ?prop (COUNT(DISTINCT ?focus) AS ?freq) WHERE { VALUES ?focus { " ^ vals ^ " } [] ?prop ?focus } GROUP BY ?prop ORDER BY DESC(?freq) ?prop LIMIT " ^ string_of_int max_properties in
*)
    let sparql_has =
      let lgp = List.map (fun (t,_) -> Lisql.sparql_triple t (Rdf.Var "prop") (Rdf.Bnode "")) focus_term_index in
      Lisql.sparql_select ~dimensions:["prop"] ~limit:max_properties
	(Lisql.sparql_join [Lisql.sparql_union lgp; Lisql.sparql_constr (Rdf.Var "prop") property_constr]) in
    let sparql_isof =
      let lgp = List.map (fun (t,_) -> Lisql.sparql_triple (Rdf.Bnode "") (Rdf.Var "prop") t) focus_term_index in
      Lisql.sparql_select ~dimensions:["prop"] ~limit:max_properties
	(Lisql.sparql_join [Lisql.sparql_union lgp; Lisql.sparql_constr (Rdf.Var "prop") property_constr]) in
    Sparql_endpoint.ajax_list_in [elt] ajax_pool endpoint [sparql_has; sparql_isof]
      (function
	| [results_has; results_isof] ->
	  if results_has.Sparql_endpoint.length > 0 || results_isof.Sparql_endpoint.length > 0
	  then process results_has results_isof
	  else
	    ( match query_prop_has_opt, query_prop_isof_opt with
	      | None, None -> process Sparql_endpoint.empty_results Sparql_endpoint.empty_results
	      | Some query_has, Some query_isof ->
		let sparql_has = query_has ~constr:property_constr ~limit:max_properties in
		let sparql_isof = query_isof ~constr:property_constr ~limit:max_properties in
		Sparql_endpoint.ajax_list_in [elt] ajax_pool endpoint [sparql_has; sparql_isof]
		  (function
		    | [results_has; results_isof] -> process results_has results_isof
		    | _ -> assert false)
		  (fun code -> process Sparql_endpoint.empty_results Sparql_endpoint.empty_results)
	      | _ -> assert false )
	| _ -> assert false)
      (fun code -> process Sparql_endpoint.empty_results Sparql_endpoint.empty_results)

  method index_modifiers =
    let modif_list =
      let open Lisql in
      match focus with
	| AtP1 _ -> [IncrOr; IncrMaybe; IncrNot]
	| AtS1 (Det (An (modif, head), _), _) ->
	  let modifs =
	    if List.exists (function (Rdf.Number _, _) -> true | _ -> false) focus_term_index
	    then List.map (fun g -> IncrModifS2 (Aggreg (None,g))) [Total; Average; Maximum; Minimum]
	    else [] in
	  let modifs =
	    if List.exists (function (Rdf.Number _, _) | (Rdf.PlainLiteral _, _) | (Rdf.TypedLiteral _, _) -> true | _ -> false) focus_term_index
	    then IncrModifS2 (Aggreg (None,ListOf)) :: modifs
	    else modifs in
	  let modifs =
	    IncrModifS2 Any :: IncrModifS2 (Aggreg (None,NumberOf)) :: modifs in
	  let modifs =
	    match modif with
	      | Aggreg (_,g) -> IncrModifS2 (Aggreg (Some Highest, g)) :: IncrModifS2 (Aggreg (Some Lowest, g)) :: modifs
	      | _ -> IncrModifS2 (Order Highest) :: IncrModifS2 (Order Lowest) :: modifs in
	  modifs
	| _ -> [] in
    List.map (fun incr -> (incr,1)) modif_list

end

