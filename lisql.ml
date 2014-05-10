
(* LISQL representations *)

(* LISQL constraints *)
type constr =
  | True
  | MatchesAll of string list
  | MatchesAny of string list
  | After of string
  | Before of string
  | FromTo of string * string
  | HigherThan of string
  | LowerThan of string
  | Between of string * string
  | HasLang of string
  | HasDatatype of string

let compile_constr constr : Rdf.term -> bool =
  let regexp_of_pat pat = Regexp.regexp_with_flag (Regexp.quote pat) "i" in
  let matches s re = Regexp.search re s 0 <> None in
  let leq t pat = try (Rdf.float_of_term t) <= (float_of_string pat) with _ -> false in
  let geq t pat = try (Rdf.float_of_term t) >= (float_of_string pat) with _ -> false in
  match constr with
    | True -> (fun t -> true)
    | MatchesAll lpat ->
      let lre = List.map regexp_of_pat lpat in
      (fun t ->
	let s = Rdf.string_of_term t in
	List.for_all (fun re -> matches s re) lre)
    | MatchesAny lpat ->
      let lre = List.map regexp_of_pat lpat in
      (fun t ->
	let s = Rdf.string_of_term t in
	List.exists (fun re -> matches s re) lre)
    | After pat ->
      (fun t -> (Rdf.string_of_term t) >= pat)
    | Before pat ->
      (fun t -> (Rdf.string_of_term t) <= pat)
    | FromTo (pat1,pat2) ->
      (fun t ->
	let s = Rdf.string_of_term t in
	pat1 <= s && s <= pat2)
    | HigherThan pat ->
      (fun t -> geq t pat)
    | LowerThan pat ->
      (fun t -> leq t pat)
    | Between (pat1,pat2) ->
      (fun t -> geq t pat1 && leq t pat2)
    | HasLang pat ->
      let re = regexp_of_pat pat in
      (function
	| Rdf.PlainLiteral (s,lang) -> matches lang re
	| _ -> false)
    | HasDatatype pat ->
      let re = regexp_of_pat pat in
      (function
	| Rdf.Number (_,s,dt)
	| Rdf.TypedLiteral (s,dt) -> matches dt re
	| _ -> false)

(* LISQL modifiers *)
type arg = S | P | O
type order = Unordered | Highest | Lowest
type aggreg = NumberOf | ListOf | Total | Average | Maximum | Minimum
type project = Unselect | Select | Aggreg of aggreg * order
type modif_s2 = project * order

(* LISQL elts *)
type elt_p1 =
  | Is of elt_s1
  | Type of Rdf.uri
  | Has of Rdf.uri * elt_s1
  | IsOf of Rdf.uri * elt_s1
  | Triple of arg * elt_s1 * elt_s1 (* abstraction arg + other S1 arguments in order: S, P, O *)
  | Search of constr
  | Constr of constr
  | And of elt_p1 array
  | Or of elt_p1 array
  | Maybe of elt_p1
  | Not of elt_p1
  | IsThere
and elt_s1 =
  | Det of elt_s2 * elt_p1 option
  | NAnd of elt_s1 array
  | NOr of elt_s1 array
  | NMaybe of elt_s1
  | NNot of elt_s1
and elt_s2 =
  | Term of Rdf.term
  | An of modif_s2 * elt_head
and elt_head =
  | Thing
  | Class of Rdf.uri
and elt_s =
  | Return of elt_s1

let top_p1 = IsThere
let top_s2 = An ((Select, Unordered), Thing)
let top_s1 = Det (top_s2,None)

let s2_of_term t = Term t
let s1_of_term t = Det (s2_of_term t, None)
let p1_of_term t = Is (s1_of_term t)

(* LISQL contexts *)
type ctx_p1 =
  | DetThatX of elt_s2 * ctx_s1
  | AndX of int * elt_p1 array * ctx_p1
  | OrX of int * elt_p1 array * ctx_p1
  | MaybeX of ctx_p1
  | NotX of ctx_p1
and ctx_s1 =
  | IsX of ctx_p1
  | HasX of Rdf.uri * ctx_p1
  | IsOfX of Rdf.uri * ctx_p1
  | TripleX1 of arg * elt_s1 * ctx_p1 (* context on first S1 arg *)
  | TripleX2 of arg * elt_s1 * ctx_p1 (* context on second S1 arg *)
  | ReturnX
  | NAndX of int * elt_s1 array * ctx_s1
  | NOrX of int * elt_s1 array * ctx_s1
  | NMaybeX of ctx_s1
  | NNotX of ctx_s1

(* LISQL focus *)
type focus =
  | AtP1 of elt_p1 * ctx_p1
  | AtS1 of elt_s1 * ctx_s1
  | AtS of elt_s

(* extraction of LISQL s element from focus *)

let rec elt_s_of_ctx_p1 (f : elt_p1) = function
  | DetThatX (det,ctx) -> elt_s_of_ctx_s1 (Det (det, Some f)) ctx
  | AndX (i,ar,ctx) -> ar.(i) <- f; elt_s_of_ctx_p1 (And ar) ctx
  | OrX (i,ar,ctx) -> ar.(i) <- f; elt_s_of_ctx_p1 (Or ar) ctx
  | MaybeX ctx -> elt_s_of_ctx_p1 (Maybe f) ctx
  | NotX ctx -> elt_s_of_ctx_p1 (Not f) ctx
and elt_s_of_ctx_s1 (f : elt_s1) = function
  | IsX ctx -> elt_s_of_ctx_p1 (Is f) ctx
  | HasX (p,ctx) -> elt_s_of_ctx_p1 (Has (p,f)) ctx
  | IsOfX (p,ctx) -> elt_s_of_ctx_p1 (IsOf (p,f)) ctx
  | TripleX1 (arg,np,ctx) -> elt_s_of_ctx_p1 (Triple (arg,f,np)) ctx
  | TripleX2 (arg,np,ctx) -> elt_s_of_ctx_p1 (Triple (arg,np,f)) ctx
  | ReturnX -> Return f
  | NAndX (i,ar,ctx) -> ar.(i) <- f; elt_s_of_ctx_s1 (NAnd ar) ctx
  | NOrX (i,ar,ctx) -> ar.(i) <- f; elt_s_of_ctx_s1 (NOr ar) ctx
  | NMaybeX ctx -> elt_s_of_ctx_s1 (NMaybe f) ctx
  | NNotX ctx -> elt_s_of_ctx_s1 (NNot f) ctx

let elt_s_of_focus = function
  | AtP1 (f,ctx) -> elt_s_of_ctx_p1 f ctx
  | AtS1 (f,ctx) -> elt_s_of_ctx_s1 f ctx
  | AtS f -> f

(* translation from LISQL elts to SPARQL queries *)

let prefix_of_uri uri = (* for variable names *)
  match Regexp.search (Regexp.regexp "[A-Za-z0-9_]+$") uri 0 with
    | Some (i,res) -> Regexp.matched_string res
    | None -> "thing"


(* SPARQL variable generator *)
class sparql_state =
object
  val mutable prefix_cpt = []
  method new_var prefix =
    let k =
      try
	let cpt = List.assoc prefix prefix_cpt in
	prefix_cpt <- (prefix,cpt+1)::List.remove_assoc prefix prefix_cpt;
	cpt+1
      with Not_found ->
	prefix_cpt <- (prefix,1)::prefix_cpt;
	1 in
    let v = prefix ^ (if k=1 && prefix<>"" then "" else string_of_int k) in
    v

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


let sparql_constr (t : Rdf.term) : constr -> Sparql.formula = function
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

let sparql_search_constr (t : Rdf.term) (constr : constr) : Sparql.formula =
  let l = Rdf.Var "search_label" in
  match constr with
    | MatchesAll (w::lw) ->
      Sparql.formula_and_list
	[Sparql.Pattern (Sparql.search_label t l);
	 Sparql.Pattern (Sparql.search_contains l w);
	 sparql_constr l (MatchesAll lw)]
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

let sparql_arg arg x y z =
  Sparql.Pattern
    ( match arg with
      | S -> Sparql.triple x y z
      | P -> Sparql.triple y x z
      | O -> Sparql.triple y z x )

let prefix_of_arg0 = function P -> "relation" | S | O -> ""
let prefix_of_arg1 = function S -> "relation" | P | O -> ""
let prefix_of_arg2 = function O -> "relation" | S | P -> ""

let rec sparql_of_elt_p1 state : elt_p1 -> (Rdf.term -> Sparql.formula) = function
  | Is np -> sparql_of_elt_s1_as_p1 state np
  | Type c -> (fun x -> Sparql.Pattern (Sparql.rdf_type x (Rdf.URI c)))
  | Has (p,np) ->
    let q_np = sparql_of_elt_s1 state ~prefix:(prefix_of_uri p) np in
    (fun x -> q_np (fun y -> Sparql.Pattern (Sparql.triple x (Rdf.URI p) y)))
  | IsOf (p,np) ->
    let q_np = sparql_of_elt_s1 state ~prefix:"" np in
    (fun x -> q_np (fun y -> Sparql.Pattern (Sparql.triple y (Rdf.URI p) x)))
  | Triple (arg,np1,np2) ->
    let q_np1 = sparql_of_elt_s1 state ~prefix:(prefix_of_arg1 arg) np1 in
    let q_np2 = sparql_of_elt_s1 state ~prefix:(prefix_of_arg2 arg) np2 in
    (fun x -> q_np1 (fun y -> q_np2 (fun z -> sparql_arg arg x y z)))
  | Search constr -> (fun x -> sparql_search_constr x constr)
  | Constr constr -> (fun x -> sparql_constr x constr)
  | And ar ->
    let ar_d = Array.map (fun elt -> sparql_of_elt_p1 state elt) ar in
    (fun x -> Sparql.formula_and_list (Array.to_list (Array.map (fun d -> d x) ar_d)))
  | Or ar ->
    let ar_d = Array.map (fun elt -> sparql_of_elt_p1 state elt) ar in
    (fun x -> Sparql.formula_or_list (Array.to_list (Array.map (fun d -> d x) ar_d)))
  | Maybe f ->
    let d = sparql_of_elt_p1 state f in
    (fun x -> Sparql.formula_optional (d x))
  | Not f ->
    let d = sparql_of_elt_p1 (Oo.copy state) f in
    (fun x -> Sparql.formula_not (d x))
  | IsThere -> (fun x -> Sparql.True)
and sparql_of_elt_s1_as_p1 state : elt_s1 -> (Rdf.term -> Sparql.formula) = function
  | Det (det,rel_opt) ->
    let d1 = sparql_of_elt_s2_as_p1 state det in
    let d2 = match rel_opt with None -> (fun x -> Sparql.True) | Some rel -> sparql_of_elt_p1 state rel in
    (fun x -> Sparql.formula_and (d1 x) (d2 x))
  | NAnd ar ->
    let ar_d = Array.map (fun elt -> sparql_of_elt_s1_as_p1 state elt) ar in
    (fun x -> Sparql.formula_and_list (Array.to_list (Array.map (fun d -> d x) ar_d)))
  | NOr ar ->
    let ar_d = Array.map (fun elt -> sparql_of_elt_s1_as_p1 state elt) ar in
    (fun x -> Sparql.formula_or_list (Array.to_list (Array.map (fun d -> d x) ar_d)))
  | NMaybe f ->
    let d = sparql_of_elt_s1_as_p1 state f in
    (fun x -> Sparql.formula_optional (d x))
  | NNot f ->
    let d = sparql_of_elt_s1_as_p1 (Oo.copy state) f in
    (fun x -> Sparql.formula_not (d x))
and sparql_of_elt_s2_as_p1 state : elt_s2 -> (Rdf.term -> Sparql.formula) = function
  | Term t ->
    (fun x -> Sparql.Filter (Sparql.expr_comp "=" (Sparql.term x) (Sparql.term t)))
(*    (fun x -> "BIND (" ^ sparql_term t ^ " AS " ^ sparql_term x ^ ")") *)
  | An (_modif,head) ->
    let d_head =
      match head with
	| Thing -> (fun x -> Sparql.True)
	| Class c -> (fun x -> Sparql.Pattern (Sparql.rdf_type x (Rdf.URI c))) in
    d_head
and sparql_of_elt_s1 state ~prefix : elt_s1 -> ((Rdf.term -> Sparql.formula) -> Sparql.formula) = function
  | Det (det,rel_opt) ->
    let prefix =
      if prefix = ""
      then
	match rel_opt with
	  | Some (IsOf (p,_)) -> prefix_of_uri p
	  | Some (Triple (arg,_,_)) -> prefix_of_arg0 arg
	  | _ -> prefix
      else prefix in
    let qu = sparql_of_elt_s2 state ~prefix det in
    let d1 = match rel_opt with None -> (fun x -> Sparql.True) | Some rel -> sparql_of_elt_p1 state rel in
    (fun d -> qu d1 d)
  | NAnd ar ->
    let ar_q = Array.map (fun elt -> sparql_of_elt_s1 state ~prefix elt) ar in
    (fun d -> Sparql.formula_and_list (Array.to_list (Array.map (fun q -> q d) ar_q)))
  | NOr ar ->
    let ar_q = Array.map (fun elt -> sparql_of_elt_s1 state ~prefix elt) ar in
    (fun d -> Sparql.formula_or_list (Array.to_list (Array.map (fun q -> q d) ar_q)))
  | NMaybe f ->
    let q = sparql_of_elt_s1 state ~prefix f in
    (fun d -> Sparql.formula_optional (q d))
  | NNot f ->
    let q = sparql_of_elt_s1 (Oo.copy state) ~prefix f in
    (fun d -> Sparql.formula_not (q d))
and sparql_of_elt_s2 state ~prefix : elt_s2 -> ((Rdf.term -> Sparql.formula) -> (Rdf.term -> Sparql.formula) -> Sparql.formula) = function
  | Term t -> (fun d1 d2 -> Sparql.formula_and (d1 t) (d2 t))
  | An (modif, head) ->
    let prefix, qhead = sparql_of_elt_head state ~prefix head in
    let v = state#new_var prefix in
    state#set_modif v modif;
    let t = Rdf.Var v in
    (fun d1 d2 -> state#add_var v; qhead t (Sparql.formula_and (d1 t) (d2 t)))
and sparql_of_elt_head state ~prefix : elt_head -> string * (Rdf.term -> Sparql.formula -> Sparql.formula) = function
  | Thing ->
    let prefix = if prefix<>"" then prefix else "thing" in
    prefix, (fun x form -> Sparql.formula_bind x form)
  | Class c ->
    let prefix = if prefix<>"" then prefix else prefix_of_uri c in
    prefix, (fun x form -> Sparql.formula_and (Sparql.Pattern (Sparql.rdf_type x (Rdf.URI c))) form)
and sparql_of_elt_s state : elt_s -> Sparql.formula = function
  | Return np ->
    let q = sparql_of_elt_s1 state ~prefix:"" np in
    q (fun t -> Sparql.True)

let rec sparql_of_ctx_p1 state ~prefix (d : Rdf.term -> Sparql.formula) : ctx_p1 -> Sparql.formula = function
  | DetThatX (det,ctx) ->
    let prefix =
      if prefix = ""
      then
	match ctx with
	  | HasX (p,_) -> prefix_of_uri p
	  | TripleX1 (arg,_,_) -> prefix_of_arg1 arg
	  | TripleX2 (arg,_,_) -> prefix_of_arg2 arg
	  | _ -> prefix
      else prefix in
    let q_det = sparql_of_elt_s2 state ~prefix det in
    let d_det = sparql_of_elt_s2_as_p1 state det in
    sparql_of_ctx_s1 state
      (fun d2 -> q_det d d2)
      (fun x -> Sparql.formula_and (d x) (d_det x))
      ctx
  | AndX (i,ar,ctx) ->
    let ar_d = Array.mapi (fun j elt -> if j=i then d else sparql_of_elt_p1 state elt) ar in
    sparql_of_ctx_p1 state ~prefix
      (fun x ->	Sparql.formula_and_list (Array.to_list (Array.map (fun d -> d x) ar_d)))
      ctx
  (* ignoring algebra in ctx *)
  | OrX (i,ar,ctx) -> sparql_of_ctx_p1 state ~prefix d ctx
  | MaybeX ctx -> sparql_of_ctx_p1 state ~prefix d ctx
  | NotX ctx -> sparql_of_ctx_p1 state ~prefix d ctx
and sparql_of_ctx_s1 state (q : (Rdf.term -> Sparql.formula) -> Sparql.formula) (d : Rdf.term -> Sparql.formula) : ctx_s1 -> Sparql.formula = function
  | IsX ctx -> sparql_of_ctx_p1 state ~prefix:"" d ctx
  | HasX (p,ctx) ->
    sparql_of_ctx_p1 state ~prefix:""
      (fun x -> q (fun y -> Sparql.Pattern (Sparql.triple x (Rdf.URI p) y)))
      ctx
  | IsOfX (p,ctx) ->
    sparql_of_ctx_p1 state ~prefix:(prefix_of_uri p)
      (fun x -> q (fun y -> Sparql.Pattern (Sparql.triple y (Rdf.URI p) x)))
      ctx
  | TripleX1 (arg,np,ctx) ->
    let q_np = sparql_of_elt_s1 state ~prefix:(prefix_of_arg2 arg) np in
    sparql_of_ctx_p1 state ~prefix:""
      (fun x -> q (fun y -> q_np (fun z -> sparql_arg arg x y z)))
      ctx
  | TripleX2 (arg,np,ctx) ->
    let q_np = sparql_of_elt_s1 state ~prefix:(prefix_of_arg1 arg) np in
    sparql_of_ctx_p1 state ~prefix:""
      (fun x -> q_np (fun y -> q (fun z -> sparql_arg arg x y z)))
      ctx
  | ReturnX ->
    q (fun t -> Sparql.True)
  | NAndX (i,ar,ctx) ->
    let ar_q = Array.mapi (fun j elt -> if j=i then q else sparql_of_elt_s1 state ~prefix:"" elt) ar in
    let ar_d = Array.mapi (fun j elt -> if j=i then d else sparql_of_elt_s1_as_p1 state elt) ar in
    sparql_of_ctx_s1 state
      (fun d ->	Sparql.formula_and_list (Array.to_list (Array.map (fun q -> q d) ar_q)))
      (fun x -> Sparql.formula_and_list (Array.to_list (Array.map (fun d -> d x) ar_d)))
      ctx
  (* ignoring algebra in ctx *)
  | NOrX (i,ar,ctx) -> sparql_of_ctx_s1 state q d ctx
  | NMaybeX ctx -> sparql_of_ctx_s1 state q d ctx
  | NNotX ctx -> sparql_of_ctx_s1 state q d ctx

type sparql_template = ?constr:constr -> limit:int -> string

let sparql_of_focus (focus : focus) : Rdf.term list * sparql_template option * sparql_template option * sparql_template option * sparql_template option =
  let state = new sparql_state in
  let form =
    match focus with
      | AtP1 (f,ctx) ->
	let prefix =
	  match f with
	    | IsOf (p, _) -> prefix_of_uri p
	    | Triple (arg,_,_) -> prefix_of_arg0 arg
	    | _ -> "" in
	let d = sparql_of_elt_p1 state f in
	sparql_of_ctx_p1 state ~prefix
	  (fun t -> state#add_focus_term t; d t)
	  ctx
      | AtS1 (f,ctx) ->
	let prefix =
	  match ctx with
	    | HasX (p,_) -> prefix_of_uri p
	    | TripleX1 (arg,_,_) -> prefix_of_arg1 arg
	    | TripleX2 (arg,_,_) -> prefix_of_arg2 arg
	    | _ -> "" in
	let q = sparql_of_elt_s1 state ~prefix f in
	let d = sparql_of_elt_s1_as_p1 state f in
	sparql_of_ctx_s1 state
	  (fun d -> q (fun t -> state#add_focus_term t; d t))
	  (fun x -> state#add_focus_term x; d x)
	  ctx
      | AtS f ->
	(*state#set_focus_term None;*)
	sparql_of_elt_s state f
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
	     (match t_list with [t] -> Sparql.formula_and form (sparql_constr t constr) | _ -> form))) in
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
	       (Sparql.formula_and form_x (sparql_constr tx constr))))
      | _ -> None in
  let query_class_opt = query_incr_opt "class" (fun t tc -> Sparql.Pattern (Sparql.rdf_type t tc)) in
  let query_prop_has_opt = query_incr_opt "prop" (fun t tp -> Sparql.Pattern (Sparql.triple t tp (Rdf.Bnode ""))) in
  let query_prop_isof_opt = query_incr_opt "prop" (fun t tp -> Sparql.Pattern (Sparql.triple (Rdf.Bnode "") tp t)) in
  t_list, query_opt, query_class_opt, query_prop_has_opt, query_prop_isof_opt

(* NL generation from focus *)

type nl_word =
  [ `Thing
  | `Class of Rdf.uri
  | `Prop of Rdf.uri
  | `Relation
  | `Op of string
  | `Term of Rdf.term
  | `Literal of string
  | `DummyFocus ]

type nl_focus =
  [ `NoFocus
  | `Focus of focus * [ `In | `At | `Out | `Ex ] ]

type nl_s = nl_focus *
  [ `Return of nl_np ]
and nl_np = nl_focus *
  [ `PN of nl_word * nl_rel
  | `Qu of nl_qu * nl_adj * nl_word * nl_rel
  | `QuOneOf of nl_qu * nl_word list
  | `And of nl_np array
  | `Or of int option * nl_np array (* the optional int indicates that the disjunction is in the context of the i-th element *)
  | `Maybe of bool * nl_np (* the bool indicates whether negation is suspended *)
  | `Not of bool * nl_np ] (* the bool indicates whether negation is suspended *)
and nl_qu = [ `A | `Any of bool | `The | `All | `One ]
and nl_adj =
  [ `Nil
  | `Order of nl_word
  | `Aggreg of bool * nl_adj * nl_word (* the bool is for 'suspended' *)
  | `Adj of nl_adj * nl_word ]
and nl_rel = nl_focus *
  [ `Nil
  | `That of nl_vp
  | `Of of nl_np
  | `Ing of nl_word * nl_np
  | `And of nl_rel array
  | `Or of int option * nl_rel array ]
and nl_vp = nl_focus *
  [ `IsThere
  | `IsNP of nl_np * nl_pp list
  | `IsPP of nl_pp
  | `HasProp of nl_word * nl_np * nl_pp list
  | `Has of nl_np * nl_pp list
  | `VT of nl_word * nl_np * nl_pp list
  | `And of nl_vp array
  | `Or of int option * nl_vp array (* the optional int indicates that the disjunction is in the context of the i-th element *)
  | `Maybe of bool * nl_vp (* the bool indicates whether negation is suspended *)
  | `Not of bool * nl_vp (* the bool indicates whether negation is suspended *)
  | `DummyFocus ]
and nl_pp =
  [ `Prep of nl_word * nl_np
  | `PrepBin of nl_word * nl_np * nl_word * nl_np ]

let top_vp = `Nofocus, `IsThere
let top_rel = `NoFocus, `Nil
let top_np = `NoFocus, `Qu (`A, `Nil, `Thing, top_rel)
let top_s = `NoFocus, `Return top_np

let np_of_word w = `NoFocus, `PN (w, top_rel)
let np_of_literal l = np_of_word (`Literal l)

let focus_pos_down = function `In -> `In | `At -> `In | `Out -> `Out | `Ex -> `Ex

let rec head_of_modif foc nn rel (modif : modif_s2) : nl_np =
  let susp = match foc with `Focus (_, `At) -> true | _ -> false in
  let qu, adj =
    match modif with
      | Select, order -> qu_adj_of_order order
      | Unselect, order -> `Any susp, snd (qu_adj_of_order order)
      | Aggreg (g,gorder), _ ->
	let qu_order, adj_order = qu_adj_of_order gorder in
	qu_order, adj_of_aggreg ~suspended:susp adj_order g in
  foc, `Qu (qu, adj, nn, rel)
and qu_adj_of_order : order -> nl_qu * nl_adj = function
  | Unordered -> `A, `Nil
  | Highest -> `The, `Order (`Op "highest-to-lowest")
  | Lowest -> `The, `Order (`Op "lowest-to-highest")
and adj_of_aggreg ~suspended adj : aggreg -> nl_adj = function
  | NumberOf -> `Aggreg (suspended, adj, `Op "number of")
  | ListOf -> `Aggreg (suspended, adj, `Op "list of")
  | Total -> `Aggreg (suspended, adj, `Op "total")
  | Average -> `Aggreg (suspended, adj, `Op "average")
  | Maximum -> `Aggreg (suspended, adj, `Op "maximum")
  | Minimum -> `Aggreg (suspended, adj, `Op "minimum")

let vp_of_elt_p1_Is (np : nl_np) = `IsNP (np, [])
let vp_of_elt_p1_Type (c : Rdf.uri) = `IsNP ((`NoFocus, `Qu (`A, `Nil, `Class c, top_rel)), [])
let vp_of_elt_p1_Has (p : Rdf.uri) (np : nl_np) = `HasProp (`Prop p, np, [])
let vp_of_elt_p1_IsOf (p : Rdf.uri) (np : nl_np) = `IsNP ((`NoFocus, `Qu (`The, `Nil, `Prop p, (`NoFocus, `Of np))), [])
let vp_of_elt_p1_Triple (arg : arg) (np1 : nl_np) (np2 : nl_np) =
  match arg with
    | S -> (* has relation npp to npo / has property npp with value npo / has p npo *)
      `HasProp (`Relation, np1, [`Prep (`Op "to", np2)])
    | O -> (* has relation npp from nps / is the value of npp of nps / is the p of nps *)
      `HasProp (`Relation, np2, [`Prep (`Op "from", np1)])
    | P -> (* is a relation from nps to npo / is a property of nps with value npo *)
      `IsNP ((`NoFocus, `Qu (`A, `Nil, `Relation, top_rel)), [`Prep (`Op "from", np1); `Prep (`Op "to", np2)])

let rec vp_of_elt_p1 pos ctx f : nl_vp =
  let nl =
    match f with
      | IsThere -> `IsThere
      | Is np -> vp_of_elt_p1_Is (np_of_elt_s1 (focus_pos_down pos) (IsX ctx) np)
      | Type c -> vp_of_elt_p1_Type c
      | Has (p,np) -> vp_of_elt_p1_Has p (np_of_elt_s1 (focus_pos_down pos) (HasX (p,ctx)) np)
      | IsOf (p,np) -> vp_of_elt_p1_IsOf p (np_of_elt_s1 (focus_pos_down pos) (IsOfX (p,ctx)) np)
      | Triple (arg,np1,np2) ->
	vp_of_elt_p1_Triple arg
	  (np_of_elt_s1 (focus_pos_down pos) (TripleX1 (arg,np2,ctx)) np1)
	  (np_of_elt_s1 (focus_pos_down pos) (TripleX2 (arg,np1,ctx)) np2)
      | Search c -> vp_of_constr c
      | Constr c -> vp_of_constr c
      | And ar -> `And (Array.mapi (fun i elt -> vp_of_elt_p1 (focus_pos_down pos) (AndX (i,ar,ctx)) elt) ar)
      | Or ar -> `Or (None, Array.mapi (fun i elt -> vp_of_elt_p1 (focus_pos_down pos) (OrX (i,ar,ctx)) elt) ar)
      | Maybe elt -> `Maybe (false, vp_of_elt_p1 (focus_pos_down pos) (MaybeX ctx) elt)
      | Not elt -> `Not (false, vp_of_elt_p1 (focus_pos_down pos) (NotX ctx) elt) in
  `Focus (AtP1 (f,ctx), pos), nl
and vp_of_constr = function
  | True -> `IsThere
  | MatchesAll lpat -> `VT (`Op "matches", (`NoFocus, `QuOneOf (`All, List.map (fun pat -> `Literal pat) lpat)), [])
  | MatchesAny lpat -> `VT (`Op "matches", (`NoFocus, `QuOneOf (`One, List.map (fun pat -> `Literal pat) lpat)), [])
  | After pat -> `IsPP (`Prep (`Op "after", np_of_literal pat))
  | Before pat -> `IsPP (`Prep (`Op "before", np_of_literal pat))
  | FromTo (pat1,pat2) -> `IsPP (`PrepBin (`Op "from", np_of_literal pat1, `Op "to", np_of_literal pat2))
  | HigherThan pat -> `IsPP (`Prep (`Op "higher than", np_of_literal pat))
  | LowerThan pat -> `IsPP (`Prep (`Op "lower than", np_of_literal pat))
  | Between (pat1,pat2) -> `IsPP (`PrepBin (`Op "between", np_of_literal pat1, `Op "and", np_of_literal pat2))
  | HasLang pat -> `Has ((`NoFocus, `Qu (`A, `Nil, `Op "language", (`NoFocus, `Ing (`Op "matching", (`NoFocus, `PN (`Literal pat, top_rel)))))), [])
  | HasDatatype pat -> `Has ((`NoFocus, `Qu (`A, `Nil, `Op "datatype", (`NoFocus, `Ing (`Op "matching", (`NoFocus, `PN (`Literal pat, top_rel)))))), [])
and np_of_elt_s1 pos ctx f : nl_np =
  let foc = `Focus (AtS1 (f,ctx),pos) in
  match f with
    | Det (det, None) -> det_of_elt_s2 foc top_rel det
    | Det (det, Some rel) ->
      let foc_rel, nl_rel = vp_of_elt_p1 (focus_pos_down pos) (DetThatX (det,ctx)) rel in
      det_of_elt_s2 foc (foc_rel, `That (`NoFocus, nl_rel)) det
    | NAnd ar -> foc, `And (Array.mapi (fun i elt -> np_of_elt_s1 (focus_pos_down pos) (NAndX (i,ar,ctx)) elt) ar)
    | NOr ar -> foc, `Or (None, Array.mapi (fun i elt -> np_of_elt_s1 (focus_pos_down pos) (NOrX (i,ar,ctx)) elt) ar)
    | NMaybe elt -> foc, `Maybe (false, np_of_elt_s1 (focus_pos_down pos) (NMaybeX ctx) elt)
    | NNot elt -> foc, `Not (false, np_of_elt_s1 (focus_pos_down pos) (NNotX ctx) elt)
and det_of_elt_s2 foc rel : elt_s2 -> nl_np = function
  | Term t -> foc, `PN (`Term t, rel)
  | An (modif, head) -> head_of_modif foc (match head with Thing -> `Thing | Class c -> `Class c) rel modif
and s_of_elt_s pos : elt_s -> nl_s = function
  | Return np -> `Focus (AtS (Return np), pos), `Return (np_of_elt_s1 (focus_pos_down pos) ReturnX np)

let rec s_of_ctx_p1 f (foc,nl as foc_nl) ctx : nl_s =
  match ctx with
    | DetThatX (det,ctx2) ->
      let f2 = Det (det, Some f) in
      let nl2 = det_of_elt_s2 (`Focus (AtS1 (f2,ctx2), `Out)) (foc, `That (`NoFocus, nl)) det in
      s_of_ctx_s1 f2 nl2 ctx2
    | AndX (i,ar,ctx2) ->
      let f2 = ar.(i) <- f; And ar in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 =
	`And (Array.mapi
		(fun j elt -> if j=i then foc_nl else vp_of_elt_p1 `Out (AndX (j,ar,ctx2)) elt)
		ar) in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
    | OrX (i,ar,ctx2) ->
      ar.(i) <- f;
      let f2 = Or ar in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Ex) in
      let nl2 =
	`Or (Some i,
	     Array.mapi
	       (fun j elt -> if j=i then foc_nl else vp_of_elt_p1 `Ex (OrX (j,ar,ctx2)) elt)
	       ar) in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
   | MaybeX ctx2 ->
      let f2 = Maybe f in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Ex) in
      let nl2 = `Maybe (true, foc_nl) in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
   | NotX ctx2 ->
      let f2 = Not f in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Ex) in
      let nl2 = `Not (true, foc_nl) in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
and s_of_ctx_s1 f (foc,nl as foc_nl) ctx =
  match ctx with
    | IsX ctx2 ->
      let f2 = Is f in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Is foc_nl in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
    | HasX (p,ctx2) ->
      let f2 = Has (p,f) in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Has p foc_nl in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
    | IsOfX (p,ctx2) ->
      let f2 = IsOf (p,f) in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_IsOf p foc_nl in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
    | TripleX1 (arg,np2,ctx2) ->
      let f2 = Triple (arg,f,np2) in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Triple arg foc_nl (np_of_elt_s1 `Out (TripleX2 (arg,f,ctx2)) np2) in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
    | TripleX2 (arg,np1,ctx2) ->
      let f2 = Triple (arg,np1,f) in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Triple arg (np_of_elt_s1 `Out (TripleX1 (arg,f,ctx2)) np1) foc_nl in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
    | ReturnX ->
      let f2 = Return f in
      let foc2 = `Focus (AtS f2, `Out) in
      let nl2 = `Return foc_nl in
      (foc2,nl2)
    | NAndX (i,ar,ctx2) ->
      let f2 = ar.(i) <- f; NAnd ar in
      let foc2 = `Focus (AtS1 (f2,ctx2), `Out) in
      let nl2 =
	`And (Array.mapi
		(fun j elt -> if j=i then foc_nl else np_of_elt_s1 `Out (NAndX (j,ar,ctx2)) elt)
		ar) in
      s_of_ctx_s1 f2 (foc2,nl2) ctx2
    | NOrX (i,ar,ctx2) ->
      ar.(i) <- f;
      let f2 = NOr ar in
      let foc2 = `Focus (AtS1 (f2,ctx2), `Ex) in
      let nl2 =
	`Or (Some i,
	     Array.mapi
	       (fun j elt -> if j=i then foc_nl else np_of_elt_s1 `Ex (NOrX (j,ar,ctx2)) elt)
	       ar) in
      s_of_ctx_s1 f2 (foc2,nl2) ctx2
   | NMaybeX ctx2 ->
      let f2 = NMaybe f in
      let foc2 = `Focus (AtS1 (f2,ctx2), `Ex) in
      let nl2 = `Maybe (true, foc_nl) in
      s_of_ctx_s1 f2 (foc2,nl2) ctx2
   | NNotX ctx2 ->
      let f2 = NNot f in
      let foc2 = `Focus (AtS1 (f2,ctx2), `Ex) in
      let nl2 = `Not (true, foc_nl) in
      s_of_ctx_s1 f2 (foc2,nl2) ctx2

let s_of_focus : focus -> nl_s = function
  | AtP1 (f,ctx) -> s_of_ctx_p1 f (vp_of_elt_p1 `At ctx f) ctx
  | AtS1 (f,ctx) -> s_of_ctx_s1 f (np_of_elt_s1 `At ctx f) ctx
  | AtS f -> s_of_elt_s `Out f

(* focus moves *)

let home_focus = AtS1 (top_s1, ReturnX)

let down_p1 (ctx : ctx_p1) : elt_p1 -> focus option = function
  | Is np -> Some (AtS1 (np, IsX ctx))
  | Type _ -> None
  | Has (p,np) -> Some (AtS1 (np, HasX (p,ctx)))
  | IsOf (p,np) -> Some (AtS1 (np, IsOfX (p,ctx)))
  | Triple (arg,np1,np2) -> Some (AtS1 (np1, TripleX1 (arg,np2,ctx)))
  | Search _ -> None
  | Constr _ -> None
  | And ar -> Some (AtP1 (ar.(0), AndX (0,ar,ctx)))
  | Or ar -> Some (AtP1 (ar.(0), OrX (0,ar,ctx)))
  | Maybe elt -> Some (AtP1 (elt, MaybeX ctx))
  | Not elt -> Some (AtP1 (elt, NotX ctx))
  | IsThere -> None
let down_s1 (ctx : ctx_s1) : elt_s1 -> focus option = function
  | Det (det,None) -> None
  | Det (An (modif, Thing), Some (IsOf (p,np))) -> Some (AtS1 (np, IsOfX (p, DetThatX (An (modif, Thing), ctx))))
  | Det (det, Some (And ar)) -> Some (AtP1 (ar.(0), AndX (0, ar, DetThatX (det, ctx))))
  | Det (det, Some rel) -> Some (AtP1 (rel, DetThatX (det,ctx)))
  | NAnd ar -> Some (AtS1 (ar.(0), NAndX (0,ar,ctx)))
  | NOr ar -> Some (AtS1 (ar.(0), NOrX (0,ar,ctx)))
  | NMaybe elt -> Some (AtS1 (elt, NMaybeX ctx))
  | NNot elt -> Some (AtS1 (elt, NNotX ctx))
let down_s : elt_s -> focus option = function
  | Return np -> Some (AtS1 (np,ReturnX))
let down_focus = function
  | AtP1 (f,ctx) -> down_p1 ctx f
  | AtS1 (f,ctx) -> down_s1 ctx f
  | AtS f -> down_s f

let rec up_p1 f = function
  | DetThatX (det,ctx) -> Some (AtS1 (Det (det, Some f), ctx))
  | AndX (i,ar,ctx) -> ar.(i) <- f; up_p1 (And ar) ctx (* Some (AtP1 (And ar, ctx)) *)
  | OrX (i,ar,ctx) -> ar.(i) <- f; Some (AtP1 (Or ar, ctx))
  | MaybeX ctx -> Some (AtP1 (Maybe f, ctx))
  | NotX ctx -> Some (AtP1 (Not f, ctx))
let rec up_s1 f = function
(*
  | HasX (p, DetThatX (An (modif, Thing), ctx)) -> Some (AtS1 (Det (An (modif, Thing), Some (Has (p,f))), ctx))
  | IsOfX (p, DetThatX (An (modif, Thing), ctx)) -> Some (AtS1 (Det (An (modif, Thing), Some (IsOf (p,f))), ctx))
*)
  | IsX ctx -> Some (AtP1 (Is f, ctx))
  | HasX (p,ctx) -> Some (AtP1 (Has (p,f), ctx))
  | IsOfX (p,ctx) -> Some (AtP1 (IsOf (p,f), ctx))
  | TripleX1 (arg,np,ctx) -> Some (AtP1 (Triple (arg,f,np), ctx))
  | TripleX2 (arg,np,ctx) -> Some (AtP1 (Triple (arg,np,f), ctx))
  | ReturnX -> Some (AtS (Return f))
  | NAndX (i,ar,ctx) -> ar.(i) <- f; up_s1 (NAnd ar) ctx
  | NOrX (i,ar,ctx) -> ar.(i) <- f; Some (AtS1 (NOr ar, ctx))
  | NMaybeX ctx -> Some (AtS1 (NMaybe f, ctx))
  | NNotX ctx -> Some (AtS1 (NNot f, ctx))
let up_focus = function
  | AtP1 (f,ctx) -> up_p1 f ctx
  | AtS1 (f,ctx) -> up_s1 f ctx
  | AtS f -> None

let right_p1 (f : elt_p1) : ctx_p1 -> focus option = function
  | DetThatX (det,ctx) -> None
  | AndX (i,ar,ctx) ->
    if i < Array.length ar - 1
    then begin
      ar.(i) <- f;
      Some (AtP1 (ar.(i+1), AndX (i+1, ar, ctx))) end
    else None
  | OrX (i,ar,ctx) ->
    if i < Array.length ar - 1
    then begin
      ar.(i) <- f;
      Some (AtP1 (ar.(i+1), OrX (i+1, ar, ctx))) end
    else None
  | MaybeX ctx -> None
  | NotX ctx -> None
let right_s1 (f : elt_s1) : ctx_s1 -> focus option = function
  | IsX _ -> None
  | HasX _ -> None
  | IsOfX _ -> None
  | TripleX1 (arg,np,ctx) -> Some (AtS1 (np, TripleX2 (arg,f,ctx)))
  | TripleX2 _ -> None
  | ReturnX -> None
  | NAndX (i,ar,ctx) ->
    if i < Array.length ar - 1
    then begin
      ar.(i) <- f;
      Some (AtS1 (ar.(i+1), NAndX (i+1, ar, ctx))) end
    else None
  | NOrX (i,ar,ctx) ->
    if i < Array.length ar - 1
    then begin
      ar.(i) <- f;
      Some (AtS1 (ar.(i+1), NOrX (i+1, ar, ctx))) end
    else None
  | NMaybeX ctx -> None
  | NNotX ctx -> None
let right_focus = function
  | AtP1 (f,ctx) -> right_p1 f ctx
  | AtS1 (f,ctx) -> right_s1 f ctx
  | AtS f -> None

let left_p1 (f : elt_p1) : ctx_p1 -> focus option = function
  | DetThatX (det,ctx) -> None
  | AndX (i,ar,ctx) ->
    if i > 0
    then begin
      ar.(i) <- f;
      Some (AtP1 (ar.(i-1), AndX (i-1, ar, ctx))) end
    else None
  | OrX (i,ar,ctx) ->
    if i > 0
    then begin
      ar.(i) <- f;
      Some (AtP1 (ar.(i-1), OrX (i-1, ar, ctx))) end
    else None
  | MaybeX ctx -> None
  | NotX ctx -> None
let left_s1 (f : elt_s1) : ctx_s1 -> focus option = function
  | IsX _ -> None
  | HasX _ -> None
  | IsOfX _ -> None
  | TripleX1 _ -> None
  | TripleX2 (arg,np,ctx) -> Some (AtS1 (np, TripleX1 (arg,f,ctx)))
  | ReturnX -> None
  | NAndX (i,ar,ctx) ->
    if i > 0
    then begin
      ar.(i) <- f;
      Some (AtS1 (ar.(i-1), NAndX (i-1, ar, ctx))) end
    else None
  | NOrX (i,ar,ctx) ->
    if i > 0
    then begin
      ar.(i) <- f;
      Some (AtS1 (ar.(i-1), NOrX (i-1, ar, ctx))) end
    else None
  | NMaybeX ctx -> None
  | NNotX ctx -> None
let left_focus = function
  | AtP1 (f,ctx) -> left_p1 f ctx
  | AtS1 (f,ctx) -> left_s1 f ctx
  | AtS f -> None

let rec focus_moves (steps : (focus -> focus option) list) (foc_opt : focus option) : focus option = (* makes as many steps as possible *)
  match steps, foc_opt with
    | _, None -> None
    | [], _ -> foc_opt
    | step::others, Some foc ->
      ( match step foc with
	| None -> Some foc
	| Some foc' -> focus_moves others (Some foc') )

(* increments *)

type increment =
  | IncrTerm of Rdf.term
  | IncrIs
  | IncrClass of Rdf.uri
  | IncrProp of Rdf.uri
  | IncrInvProp of Rdf.uri
  | IncrTriple of arg
  | IncrTriplify
  | IncrAnd
  | IncrOr
  | IncrMaybe
  | IncrNot
  | IncrUnselect
  | IncrAggreg of aggreg
  | IncrOrder of order

let term_of_increment : increment -> Rdf.term option = function
  | IncrTerm t -> Some t
  | IncrClass c -> Some (Rdf.URI c)
  | IncrProp p -> Some (Rdf.URI p)
  | IncrInvProp p -> Some (Rdf.URI p)
  | IncrTriple arg -> None
  | IncrTriplify -> None
  | IncrIs -> None
  | IncrAnd -> None
  | IncrOr -> None
  | IncrMaybe -> None
  | IncrNot -> None
  | IncrUnselect -> None
  | IncrAggreg _ -> None
  | IncrOrder order -> None

let append_and_p1 ctx elt_p1 = function
  | And ar ->
    let n = Array.length ar in
    let ar2 = Array.make (n+1) elt_p1 in
    Array.blit ar 0 ar2 0 n;
    AtP1 (elt_p1, AndX (n, ar2, ctx))
  | p1 ->
    AtP1 (elt_p1, AndX (1, [|p1; elt_p1|], ctx))
let append_or_p1 ctx elt_p1 = function
  | Or ar ->
    let n = Array.length ar in
    let ar2 = Array.make (n+1) elt_p1 in
    Array.blit ar 0 ar2 0 n;
    AtP1 (elt_p1, OrX (n, ar2, ctx))
  | p1 ->
    AtP1 (elt_p1, OrX (1, [|p1; elt_p1|], ctx))

let append_and_s1 ctx elt_s1 = function
  | NAnd ar ->
    let n = Array.length ar in
    let ar2 = Array.make (n+1) elt_s1 in
    Array.blit ar 0 ar2 0 n;
    AtS1 (elt_s1, NAndX (n, ar2, ctx))
  | s1 ->
    AtS1 (elt_s1, NAndX (1, [|s1; elt_s1|], ctx))
let append_or_s1 ctx elt_s1 = function
  | NOr ar ->
    let n = Array.length ar in
    let ar2 = Array.make (n+1) elt_s1 in
    Array.blit ar 0 ar2 0 n;
    AtS1 (elt_s1, NOrX (n, ar2, ctx))
  | s1 ->
    AtS1 (elt_s1, NOrX (1, [|s1; elt_s1|], ctx))

let insert_elt_p1 elt = function
  | AtP1 (IsThere, ctx) -> Some (AtP1 (elt, ctx))
  | AtP1 (f, AndX (i,ar,ctx)) -> ar.(i) <- f; Some (append_and_p1 ctx elt (And ar))
  | AtP1 (f, ctx) -> Some (append_and_p1 ctx elt f)
  | AtS1 (Det (det, None), ctx) -> Some (AtP1 (elt, DetThatX (det,ctx)))
  | AtS1 (Det (det, Some rel), ctx) -> Some (append_and_p1 (DetThatX (det,ctx)) elt rel)
  | AtS1 _ -> None (* no insertion of increments on complex NPs *)
  | AtS _ -> None

let insert_term t focus =
  let focus2_opt =
    match focus with
(*
      | AtP1 (f, DetThatX (det,ctx)) ->
	if det = Term t
	then Some (AtP1 (f, DetThatX (top_s2, ctx)))
	else Some (AtP1 (f, DetThatX (Term t, ctx)))
*)
      | AtP1 _ -> insert_elt_p1 (p1_of_term t) focus
      | AtS1 (Det (det,rel_opt), ctx) ->
	if det = Term t
	then Some (AtS1 (Det (top_s2, rel_opt), ctx))
	else Some (AtS1 (Det (Term t, rel_opt), ctx))
      | AtS1 _ -> None (* no insertion of terms on complex NPs *)
      | _ -> None in
  match focus2_opt with
    | Some (AtS1 (f, HasX (p, ctx))) -> Some (AtP1 (Has (p,f), ctx))
    | Some (AtS1 (f, IsOfX (p, ctx))) -> Some (AtP1 (IsOf (p,f), ctx))
    | Some (AtS1 (f, TripleX1 (arg,np,ctx))) -> Some (AtP1 (Triple (arg,f,np), ctx))
    | Some (AtS1 (f, TripleX2 (arg,np,ctx))) -> Some (AtP1 (Triple (arg,np,f), ctx))
    | other -> other

let insert_class c = function
  | AtS1 (Det (det,rel_opt), ctx) ->
    ( match det with
      | Term _ ->
	Some (AtS1 (Det (An ((Select, Unordered), Class c), rel_opt), ctx))
      | An (modif, Thing) ->
	Some (AtS1 (Det (An (modif, Class c), rel_opt), ctx))
      | An (modif, Class c2) when c2 = c ->
	Some (AtS1 (Det (An (modif, Thing), rel_opt), ctx))
      | _ ->
	let rel = match rel_opt with None -> IsThere | Some rel -> rel in
	insert_elt_p1 (Type c) (AtP1 (rel, DetThatX (det, ctx))) )
  | focus -> insert_elt_p1 (Type c) focus

let insert_property p focus =
  let foc_opt = insert_elt_p1 (Has (p, top_s1)) focus in
  focus_moves [down_focus] foc_opt

let insert_inverse_property p focus =
  let foc_opt = insert_elt_p1 (IsOf (p, top_s1)) focus in
  focus_moves [down_focus] foc_opt

let insert_triple arg focus =
  let foc_opt = insert_elt_p1 (Triple (arg, top_s1, top_s1)) focus in
  let steps = if arg = S then [down_focus; right_focus] else [down_focus] in
  focus_moves steps foc_opt

let insert_triplify = function
  | AtP1 (Has (p,np), ctx) -> Some (AtP1 (Triple (S, Det (Term (Rdf.URI p), None), np), ctx))
  | AtP1 (IsOf (p,np), ctx) -> Some (AtP1 (Triple (O, np, Det (Term (Rdf.URI p), None)), ctx))
  | AtP1 (Triple (S, Det (Term (Rdf.URI p), _), np), ctx) -> Some (AtP1 (Has (p,np), ctx))
  | AtP1 (Triple (O, np, Det (Term (Rdf.URI p), _)), ctx) -> Some (AtP1 (IsOf (p,np), ctx))
  | _ -> None

let insert_constr constr focus =
  match focus with
    | AtS1 (f, ReturnX) when f = top_s1 -> insert_elt_p1 (Search constr) focus
    | _ -> insert_elt_p1 (Constr constr) focus

let insert_is focus =
  let foc_opt = insert_elt_p1 (Is top_s1) focus in
  focus_moves [down_focus] foc_opt

let insert_and = function
  | AtP1 (And ar, ctx) -> Some (append_and_p1 ctx IsThere (And ar))
  | AtP1 (f, AndX (i,ar,ctx2)) -> ar.(i) <- f; Some (append_and_p1 ctx2 IsThere (And ar))
  | AtP1 (f, ctx) -> Some (append_and_p1 ctx IsThere f)
  | AtS1 (NAnd ar, ctx) -> Some (append_and_s1 ctx top_s1 (NAnd ar))
  | AtS1 (f, NAndX (i,ar,ctx2)) -> ar.(i) <- f; Some (append_and_s1 ctx2 top_s1 (NAnd ar))
  | AtS1 (f, ctx) -> Some (append_and_s1 ctx top_s1 f)
  | _ -> None

let insert_or = function
  | AtP1 (Or ar, ctx) -> Some (append_or_p1 ctx IsThere (Or ar))
  | AtP1 (f, OrX (i,ar,ctx2)) -> ar.(i) <- f; Some (append_or_p1 ctx2 IsThere (Or ar))
  | AtP1 (f, ctx) -> Some (append_or_p1 ctx IsThere f)
  | AtS1 (NOr ar, ctx) -> Some (append_or_s1 ctx top_s1 (NOr ar))
  | AtS1 (f, NOrX (i,ar,ctx2)) -> ar.(i) <- f; Some (append_or_s1 ctx2 top_s1 (NOr ar))
  | AtS1 (f, ctx) -> Some (append_or_s1 ctx top_s1 f)
  | _ -> None

let insert_maybe = function
  | AtP1 (Maybe f, ctx) -> Some (AtP1 (f,ctx))
  | AtP1 (f, ctx) -> if f = top_p1 then Some (AtP1 (f, MaybeX ctx)) else Some (AtP1 (Maybe f, ctx))
  | AtS1 (NMaybe f, ctx) -> Some (AtS1 (f,ctx))
  | AtS1 (f, ctx) -> if f = top_s1 then Some (AtS1 (f, NMaybeX ctx)) else Some (AtS1 (NMaybe f, ctx))
  | _ -> None

let insert_not = function
  | AtP1 (Not f, ctx) -> Some (AtP1 (f,ctx))
  | AtP1 (f, ctx) -> if f = top_p1 then Some (AtP1 (f, NotX ctx)) else Some (AtP1 (Not f, ctx))
  | AtS1 (NNot f, ctx) -> Some (AtS1 (f,ctx))
  | AtS1 (f, ctx) -> if f = top_s1 then Some (AtS1 (f, NNotX ctx)) else Some (AtS1 (NNot f, ctx))
  | _ -> None

let insert_modif_transf f = function
  | AtS1 (Det (An (modif, head), rel_opt), ctx) ->
    let modif2 = f modif in
    let foc2 = AtS1 (Det (An (modif2, head), rel_opt), ctx) in
    ( match fst modif2 with
      | Unselect | Aggreg _ -> up_focus foc2 (* to enforce visible aggregation *)
      | _ -> Some foc2 )
  | _ -> None

let insert_increment incr focus =
  match incr with
    | IncrTerm t -> insert_term t focus
    | IncrClass c -> insert_class c focus
    | IncrProp p -> insert_property p focus
    | IncrInvProp p -> insert_inverse_property p focus
    | IncrTriple arg -> insert_triple arg focus
    | IncrTriplify -> insert_triplify focus
    | IncrIs -> insert_is focus
    | IncrAnd -> insert_and focus
    | IncrOr -> insert_or focus
    | IncrMaybe -> insert_maybe focus
    | IncrNot -> insert_not focus
    | IncrUnselect ->
      insert_modif_transf
	(function
	  | (Unselect,order) -> Select, order
	  | (_,order) ->  Unselect, order)
	focus
    | IncrAggreg g ->
      insert_modif_transf
	(function
	  | (Aggreg (g0, gorder), order) when g = g0 -> Select, order
	  | (_, order) -> Aggreg (g, Unordered), order)
	focus
    | IncrOrder order ->
      insert_modif_transf
	(function
	  | (Aggreg (g,gorder), order0) -> 
	    if gorder = order
	    then Aggreg (g, Unordered), order0
	    else Aggreg (g, order), order0
	  | ((Select | Unselect) as proj, order0) ->
	    if order0 = order
	    then proj, Unordered
	    else proj, order)
	focus

let delete_array ar i =
  let n = Array.length ar in
  if n = 1 then `Empty
  else if n = 2 then `Single ar.(1-i)
  else
    let ar2 = Array.make (n-1) ar.(0) in
    Array.blit ar 0 ar2 0 i;
    Array.blit ar (i+1) ar2 i (n-i-1);
    if i = n-1 && i > 0 (* last elt is deleted *)
    then `Array (ar2, i-1)
    else `Array (ar2, i)

let rec delete_ctx_p1 = function
  | DetThatX (det,ctx) -> Some (AtS1 (Det (det,None), ctx))
  | AndX (i,ar,ctx) ->
    ( match delete_array ar i with
      | `Empty -> delete_ctx_p1 ctx
      | `Single elt -> Some (AtP1 (elt, ctx))
      | `Array (ar2,i2) -> Some (AtP1 (ar2.(i2), AndX (i2,ar2,ctx))) )
  | OrX (i,ar,ctx) ->
    ( match delete_array ar i with
      | `Empty -> delete_ctx_p1 ctx
      | `Single elt -> Some (AtP1 (elt, ctx))
      | `Array (ar2, i2) -> Some (AtP1 (ar2.(i2), OrX (i2, ar2, ctx))) )
  | MaybeX ctx -> delete_ctx_p1 ctx
  | NotX ctx -> delete_ctx_p1 ctx
and delete_ctx_s1 f ctx =
  match ctx with
    | IsX _
    | HasX _
    | IsOfX _
    | TripleX1 _
    | TripleX2 _ 
    | ReturnX -> if f = top_s1 then None else Some (AtS1 (top_s1, ctx))
    | NAndX (i,ar,ctx2) ->
      ( match delete_array ar i with
	| `Empty -> delete_ctx_s1 top_s1 ctx2
	| `Single elt -> Some (AtS1 (elt, ctx2))
	| `Array (ar2,i2) -> Some (AtS1 (ar2.(i2), NAndX (i2,ar2,ctx2))) )
    | NOrX (i,ar,ctx2) ->
      ( match delete_array ar i with
	| `Empty -> delete_ctx_s1 top_s1 ctx2
	| `Single elt -> Some (AtS1 (elt, ctx2))
	| `Array (ar2, i2) -> Some (AtS1 (ar2.(i2), NOrX (i2, ar2, ctx2))) )
    | NMaybeX ctx2 -> delete_ctx_s1 f ctx2
    | NNotX ctx2 -> delete_ctx_s1 f ctx2

let delete_focus = function
  | AtP1 (_, ctx) -> delete_ctx_p1 ctx
  | AtS1 (f, ctx) -> delete_ctx_s1 f ctx
  | AtS _ -> Some (AtS (Return top_s1))
