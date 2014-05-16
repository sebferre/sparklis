
open Jsutils
open Lisql

(* translation from LISQL elts to SPARQL queries *)

(* SPARQL variable generator *)
class state (lex : Lisql2nl.lexicon) =
object
  method lexicon = lex

  val mutable vars : Rdf.var list = []
  method add_var v = if not (List.mem v vars) then vars <- v::vars
  method vars = List.rev vars

  val mutable focus_terms : Rdf.term list = []
  method add_focus_term t = if not (List.mem t focus_terms) then focus_terms <- t::focus_terms
  method focus_terms = focus_terms

  val h_var_modif : (Rdf.var, modif_s2) Hashtbl.t = Hashtbl.create 13
  method set_modif (v : Rdf.var) (modif : modif_s2) : unit =
    Hashtbl.add h_var_modif v modif
  method modif (v : Rdf.var) =
    try Hashtbl.find h_var_modif v
    with _ -> (Select, Unordered)
end


let filter_constr (t : Rdf.term) : constr -> Sparql.formula = function
  | True -> Sparql.True
  | MatchesAll [] -> Sparql.True
  | MatchesAll lpat ->
    Sparql.Filter
      (Sparql.log_and
	 (List.map
	    (fun pat -> Sparql.expr_regex (Sparql.expr_func "str" (Sparql.term t)) pat)
	    lpat))
  | MatchesAny [] -> Sparql.True
  | MatchesAny lpat ->
    Sparql.Filter
      (Sparql.log_or
	 (List.map
	    (fun pat -> Sparql.expr_regex (Sparql.expr_func "str" (Sparql.term t)) pat)
	    lpat))
  | After pat ->
    Sparql.Filter (Sparql.expr_comp ">=" (Sparql.expr_func "str" (Sparql.term t)) (Sparql.string pat))
  | Before pat ->
    Sparql.Filter (Sparql.expr_comp "<=" (Sparql.expr_func "str" (Sparql.term t)) (Sparql.string pat))
  | FromTo (pat1,pat2) ->
    Sparql.Filter
      (Sparql.log_and
	 [Sparql.expr_comp ">=" (Sparql.expr_func "str" (Sparql.term t)) (Sparql.string pat1);
	  Sparql.expr_comp "<=" (Sparql.expr_func "str" (Sparql.term t)) (Sparql.string pat2)])
  | HigherThan pat ->
    Sparql.Filter (Sparql.expr_comp ">=" (Sparql.term_numeric t) pat)
  | LowerThan pat ->
    Sparql.Filter (Sparql.expr_comp "<=" (Sparql.term_numeric t) pat)
  | Between (pat1,pat2) ->
    Sparql.Filter
      (Sparql.log_and
	 [Sparql.expr_comp ">=" (Sparql.term_numeric t) pat1;
	  Sparql.expr_comp "<=" (Sparql.term_numeric t) pat2])
  | HasLang pat ->
    Sparql.Filter
      (Sparql.log_and
	 [Sparql.expr_func "isLiteral" (Sparql.term t);
	  Sparql.expr_regex (Sparql.expr_func "lang" (Sparql.term t)) pat])
  | HasDatatype pat ->
    Sparql.Filter
      (Sparql.log_and
	 [Sparql.expr_func "isLiteral" (Sparql.term t);
	  Sparql.expr_regex (Sparql.expr_func "str" (Sparql.expr_func "datatype" (Sparql.term t))) pat])

let search_constr (t : Rdf.term) (c : constr) : Sparql.formula =
  let l = Rdf.Var "search_label" in
  match c with
    | MatchesAll (w::lw) ->
      Sparql.formula_and_list
	[Sparql.Pattern (Sparql.search_label t l);
	 Sparql.Pattern (Sparql.search_contains l w);
	 filter_constr l (MatchesAll lw)]
    | MatchesAny lw ->
      Sparql.formula_or_list
	(List.map
	   (fun w ->
	     Sparql.formula_and_list
	       [Sparql.Pattern (Sparql.search_label t l);
		Sparql.Pattern (Sparql.search_contains l w)])
	   lw)
    | _ ->
      Sparql.Pattern (Sparql.search_label t l)

let triple_arg arg x y z =
  Sparql.Pattern
    ( match arg with
      | S -> Sparql.triple x y z
      | P -> Sparql.triple y x z
      | O -> Sparql.triple y z x )

type sparql_p1 = Rdf.term -> Sparql.formula
type sparql_p2 = Rdf.term -> Rdf.term -> Sparql.formula
type sparql_s1 = sparql_p1 -> Sparql.formula
type sparql_s2 = sparql_p1 -> sparql_p1 -> Sparql.formula
type sparql_b1 = sparql_p2 -> Sparql.formula

let rec elt_p1 state : elt_p1 -> sparql_p1 = function
  | Is np -> elt_s1_as_p1 state np
  | Type c -> (fun x -> Sparql.Pattern (Sparql.rdf_type x (Rdf.URI c)))
  | Has (p,np) ->
    let q_np = elt_s1 state np in
    (fun x -> q_np (fun y -> Sparql.Pattern (Sparql.triple x (Rdf.URI p) y)))
  | IsOf (p,np) ->
    let q_np = elt_s1 state np in
    (fun x -> q_np (fun y -> Sparql.Pattern (Sparql.triple y (Rdf.URI p) x)))
  | Triple (arg,np1,np2) ->
    let q_np1 = elt_s1 state np1 in
    let q_np2 = elt_s1 state np2 in
    (fun x -> q_np1 (fun y -> q_np2 (fun z -> triple_arg arg x y z)))
  | Search c -> (fun x -> search_constr x c)
  | Filter c -> (fun x -> filter_constr x c)
  | And ar ->
    let ar_d = Array.map (fun elt -> elt_p1 state elt) ar in
    (fun x -> Sparql.formula_and_list (Array.to_list (Array.map (fun d -> d x) ar_d)))
  | Or ar ->
    let ar_d = Array.map (fun elt -> elt_p1 state elt) ar in
    (fun x -> Sparql.formula_or_list (Array.to_list (Array.map (fun d -> d x) ar_d)))
  | Maybe f ->
    let d = elt_p1 state f in
    (fun x -> Sparql.formula_optional (d x))
  | Not f ->
    let d = elt_p1 (Oo.copy state) f in
    (fun x -> Sparql.formula_not (d x))
  | IsThere -> (fun x -> Sparql.True)
and elt_s1_as_p1 state : elt_s1 -> sparql_p1 = function
  | Det (det,rel_opt) ->
    let d1 = elt_s2_as_p1 state det in
    let d2 = match rel_opt with None -> (fun x -> Sparql.True) | Some rel -> elt_p1 state rel in
    (fun x -> Sparql.formula_and (d1 x) (d2 x))
  | NAnd ar ->
    let ar_d = Array.map (fun elt -> elt_s1_as_p1 state elt) ar in
    (fun x -> Sparql.formula_and_list (Array.to_list (Array.map (fun d -> d x) ar_d)))
  | NOr ar ->
    let ar_d = Array.map (fun elt -> elt_s1_as_p1 state elt) ar in
    (fun x -> Sparql.formula_or_list (Array.to_list (Array.map (fun d -> d x) ar_d)))
  | NMaybe f ->
    let d = elt_s1_as_p1 state f in
    (fun x -> Sparql.formula_optional (d x))
  | NNot f ->
    let d = elt_s1_as_p1 (Oo.copy state) f in
    (fun x -> Sparql.formula_not (d x))
and elt_s2_as_p1 state : elt_s2 -> sparql_p1 = function
  | Term t ->
    (fun x -> Sparql.Filter (Sparql.expr_comp "=" (Sparql.term x) (Sparql.term t)))
(*    (fun x -> "BIND (" ^ Sparql.term t ^ " AS " ^ Sparql.term x ^ ")") *)
  | An (_id, _modif,head) ->
    let d_head =
      match head with
	| Thing -> (fun x -> Sparql.True)
	| Class c -> (fun x -> Sparql.Pattern (Sparql.rdf_type x (Rdf.URI c))) in
    d_head
  | The id ->
    (fun x ->
      let v = state#lexicon#get_id_var id in
      let t = Rdf.Var v in
      Sparql.Filter (Sparql.expr_comp "=" (Sparql.term x) (Sparql.term t)))    
and elt_s1 state : elt_s1 -> sparql_s1 = function
  | Det (det,rel_opt) ->
    let qu = elt_s2 state det in
    let d1 = match rel_opt with None -> (fun x -> Sparql.True) | Some rel -> elt_p1 state rel in
    (fun d -> qu d1 d)
  | NAnd ar ->
    let ar_q = Array.map (fun elt -> elt_s1 state elt) ar in
    (fun d -> Sparql.formula_and_list (Array.to_list (Array.map (fun q -> q d) ar_q)))
  | NOr ar ->
    let ar_q = Array.map (fun elt -> elt_s1 state elt) ar in
    (fun d -> Sparql.formula_or_list (Array.to_list (Array.map (fun q -> q d) ar_q)))
  | NMaybe f ->
    let q = elt_s1 state f in
    (fun d -> Sparql.formula_optional (q d))
  | NNot f ->
    let q = elt_s1 (Oo.copy state) f in
    (fun d -> Sparql.formula_not (q d))
and elt_s2 state : elt_s2 -> sparql_s2 = function
  | Term t -> (fun d1 d2 -> Sparql.formula_and (d1 t) (d2 t))
  | An (id, modif, head) ->
    let qhead = elt_head state head in
    let v = state#lexicon#get_id_var id in
    state#set_modif v modif;
    let t = Rdf.Var v in
    (fun d1 d2 -> state#add_var v; qhead t (Sparql.formula_and (d1 t) (d2 t)))
  | The id ->
    let v = state#lexicon#get_id_var id in
    let t = Rdf.Var v in
    (fun d1 d2 -> Sparql.formula_and (d1 t) (d2 t))
and elt_head state : elt_head -> (Rdf.term -> Sparql.formula -> Sparql.formula) = function
  | Thing ->
    (fun x form -> Sparql.formula_bind x form)
  | Class c ->
    (fun x form -> Sparql.formula_and (Sparql.Pattern (Sparql.rdf_type x (Rdf.URI c))) form)
and elt_s state : elt_s -> Sparql.formula = function
  | Return np ->
    let q = elt_s1 state np in
    q (fun t -> Sparql.True)

let rec elt_s1_bis state (q : sparql_s1) (q_alt : sparql_s1) : elt_s1 -> sparql_b1 = function
  | (Det _ as np1) -> (* q_alt is not used in this case *)
    let q1 = elt_s1 state np1 in
    (fun r -> q1 (fun x -> q (fun y -> r x y)))
  | NAnd ar -> elt_s1_bis_and state q q_alt (Array.to_list ar)
  | NOr ar ->
    let ar_b = Array.map (fun elt -> elt_s1_bis state q q_alt elt) ar in
    (fun r -> Sparql.formula_or_list (Array.to_list (Array.map (fun b -> b r) ar_b)))
  | NMaybe np1 -> elt_s1_bis state q q_alt np1
  | NNot np1 -> elt_s1_bis state q q_alt np1
and elt_s1_bis_and state q q_alt = function
  | [] -> (fun r -> Sparql.True)
  | [np1] -> elt_s1_bis state q q_alt np1
  | np1::nps ->
    let b1 = elt_s1_bis state q q_alt np1 in
    let b1_alt = elt_s1_bis state q_alt (fun d -> Sparql.False) np1 in
    let bs = elt_s1_bis_and state q q_alt nps in
    let bs_alt = elt_s1_bis_and state q_alt (fun d -> Sparql.False) nps in
    (fun r -> Sparql.formula_or_list [Sparql.formula_and (b1 r) (bs r);
				      Sparql.formula_and (b1 r) (bs_alt r);
				      Sparql.formula_and (b1_alt r) (bs r)])


let rec ctx_p1 state (d : sparql_p1) : ctx_p1 -> Sparql.formula = function
  | DetThatX (det,ctx) ->
    let q_det = elt_s2 state det in
    let d_det = elt_s2_as_p1 state det in
    ctx_s1 state
      (fun d2 -> q_det d d2)
      (fun d2 -> Sparql.False)
      (fun x -> Sparql.formula_and (d x) (d_det x))
      ctx
  | AndX (i,ar,ctx) ->
    let ar_d = Array.mapi (fun j elt -> if j=i then d else elt_p1 state elt) ar in
    ctx_p1 state
      (fun x ->	Sparql.formula_and_list (Array.to_list (Array.map (fun d -> d x) ar_d)))
      ctx
  (* ignoring algebra in ctx *)
  | OrX (i,ar,ctx) -> ctx_p1 state d ctx
  | MaybeX ctx -> ctx_p1 state d ctx
  | NotX ctx -> ctx_p1 state d ctx
and ctx_s1 state (q : sparql_s1) (q_alt : sparql_s1) (d : sparql_p1) : ctx_s1 -> Sparql.formula = function
  | IsX ctx -> ctx_p1 state d ctx
  | HasX (p,ctx) ->
    ctx_p1 state
      (fun x -> q (fun y -> Sparql.Pattern (Sparql.triple x (Rdf.URI p) y)))
      ctx
  | IsOfX (p,ctx) ->
    ctx_p1 state
      (fun x -> q (fun y -> Sparql.Pattern (Sparql.triple y (Rdf.URI p) x)))
      ctx
  | TripleX1 (arg,np,ctx) ->
    let q_np = elt_s1 state np in
    ctx_p1 state
      (fun x -> q (fun y -> q_np (fun z -> triple_arg arg x y z)))
      ctx
  | TripleX2 (arg,np,ctx) ->
    let b_np = elt_s1_bis state q q_alt np in
    ctx_p1 state
      (fun x -> b_np (fun y z -> triple_arg arg x y z))
      ctx
  | ReturnX ->
    q (fun t -> Sparql.True)
  | NAndX (i,ar,ctx) ->
    let ar_q = Array.mapi (fun j elt -> if j=i then q else elt_s1 state elt) ar in
    let ar_q_alt = let ar = Array.copy ar_q in ar.(i) <- q_alt; ar in
    let ar_d = Array.mapi (fun j elt -> if j=i then d else elt_s1_as_p1 state elt) ar in
    ctx_s1 state
      (fun d ->	Sparql.formula_and_list (Array.to_list (Array.map (fun q -> q d) ar_q)))
      (fun d -> Sparql.formula_and_list (Array.to_list (Array.map (fun q_alt -> q_alt d) ar_q_alt)))
      (fun x -> Sparql.formula_and_list (Array.to_list (Array.map (fun d -> d x) ar_d)))
      ctx
  (* ignoring algebra in ctx *)
  | NOrX (i,ar,ctx) ->
    let ar_q_alt = Array.mapi (fun j elt -> if j=i then q_alt else elt_s1 state elt) ar in
    ctx_s1 state
      q
      (fun d -> Sparql.formula_or_list (Array.to_list (Array.map (fun q_alt -> q_alt d) ar_q_alt)))
      d
      ctx
  | NMaybeX ctx -> ctx_s1 state q q_alt d ctx
  | NNotX ctx -> ctx_s1 state q q_alt d ctx

type template = ?constr:constr -> limit:int -> string

let focus (lex : Lisql2nl.lexicon) (focus : focus)
    : Rdf.term list * template option * template option * template option * template option =
  let state = new state lex in
  let form =
    match focus with
      | AtP1 (f,ctx) ->
	let d = elt_p1 state f in
	ctx_p1 state
	  (fun t -> state#add_focus_term t; d t)
	  ctx
      | AtS1 (f,ctx) ->
	let q = elt_s1 state f in
	let d = elt_s1_as_p1 state f in
	ctx_s1 state
	  (fun d -> q (fun t -> state#add_focus_term t; d t))
	  (fun d -> Sparql.False)
	  (fun x -> state#add_focus_term x; d x)
	  ctx
      | AtS f ->
	(*state#set_focus_term None;*)
	elt_s state f
  in
  let t_list = state#focus_terms in
  let query_opt =
    if form = Sparql.True
    then None
    else
      let lv = state#vars in
      let dimensions, aggregations, ordering =
	List.fold_right
	  (fun v (dims,aggregs,ordering) ->
	    let modif = state#modif v in
	    let dims, aggregs, order, v_order = (* v_order is to be used in ordering *)
	      match modif with
		| (Unselect,order) when t_list <> [Rdf.Var v] -> (* when not on focus *)
		  dims, aggregs, order, v
		| (Aggreg (g,gorder),order) when t_list <> [Rdf.Var v] -> (* when not on focus *)
		  let g_sparql, vg_prefix =
		    match g with
		      | NumberOf -> Sparql.DistinctCOUNT, "number_of_"
		      | ListOf -> Sparql.DistinctCONCAT, "list_of_"
		      | Total -> Sparql.SUM, "total_"
		      | Average -> Sparql.AVG, "average_"
		      | Maximum -> Sparql.MAX, "maximum_"
		      | Minimum -> Sparql.MIN, "minimum_" in
		  let vg = vg_prefix ^ v in
		  dims, (g_sparql,v,vg)::aggregs, gorder, vg
		| (_, order) -> v::dims, aggregs, order, v in
	    let ordering =
	      match order with
		| Unordered -> ordering
		| Lowest -> (Sparql.ASC, v_order) :: ordering
		| Highest -> (Sparql.DESC, v_order) :: ordering in
	    dims, aggregs, ordering)
	  lv ([],[],[]) in
      Some (fun ?(constr=True) ~limit ->
	Sparql.select ~distinct:true ~dimensions ~aggregations ~ordering ~limit
	  (Sparql.pattern_of_formula
	     (match t_list with [t] -> Sparql.formula_and form (filter_constr t constr) | _ -> form))) in
  let query_incr_opt x triple =
    match t_list with
      | [t] ->
	let tx = Rdf.Var x in
	let form_x =
	  match t with
	    | Rdf.Var v -> Sparql.formula_and form (triple t tx)
	    | _ -> triple t tx in
	Some (fun ?(constr=True) ~limit ->
	  Sparql.select ~dimensions:[x] ~limit
	    (Sparql.pattern_of_formula
	       (Sparql.formula_and form_x (filter_constr tx constr))))
      | _ -> None in
  let query_class_opt = query_incr_opt "class" (fun t tc -> Sparql.Pattern (Sparql.rdf_type t tc)) in
  let query_prop_has_opt = query_incr_opt "prop" (fun t tp -> Sparql.Pattern (Sparql.triple t tp (Rdf.Bnode ""))) in
  let query_prop_isof_opt = query_incr_opt "prop" (fun t tp -> Sparql.Pattern (Sparql.triple (Rdf.Bnode "") tp t)) in
  t_list, query_opt, query_class_opt, query_prop_has_opt, query_prop_isof_opt
