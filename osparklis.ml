
open Js
open XmlHttpRequest

(* ------------------------ *)

type uri = string

let prefix_of_uri uri = (* for variable names *)
  match Regexp.search (Regexp.regexp "[A-Za-z0-9_]+$") uri 0 with
    | Some (i,res) -> Regexp.matched_string res
    | None -> "thing"

let name_of_uri uri =
  let uri = to_string (decodeURI (string uri)) in
  match Regexp.search (Regexp.regexp "[^/#]+$") uri 0 with
    | Some (_,res) ->
      ( match Regexp.matched_string res with "" -> uri | name -> name )
    | None -> uri

let uri_has_ext uri exts =
  List.exists
    (fun ext -> Filename.check_suffix uri ext)
    exts
let uri_is_image uri = uri_has_ext uri ["jpg"; "JPG"; "jpeg"; "JPEG"; "png"; "PNG"; "gif"; "GIF"; "bmp"; "BMP"]

(* ------------------------- *)

type var = string

type term =
  | URI of uri
  | Number of float * string * string (* value, string, datatype *)
  | TypedLiteral of string * uri
  | PlainLiteral of string * string
  | Bnode of string
  | Var of var

let string_of_term = function
  | URI uri -> uri
  | Number (f,s,dt) -> s
  | TypedLiteral (s,dt) -> s
  | PlainLiteral (s,lang) -> s
  | Bnode id -> id
  | Var v -> v

let float_of_term = function
  | Number (f,_,_) -> f
  | _ -> invalid_arg "float_of_term"

let string_is_float =
  let re = Regexp.regexp "^[+-]?(\\d+|\\d*[.]\\d+|\\d+[.]\\d*[eE][+-]?\\d+|[.]\\d+[eE][+-]?\\d+|\\d+[eE][+-]?\\d+)$" in
  (fun s -> Regexp.string_match re s 0 <> None)

(* -------------------------- *)

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

let make_constr op pat =
  let lpat = List.filter ((<>) "") (Regexp.split (Regexp.regexp "[ ]+") pat) in
  if lpat = []
  then True
  else
    match op, lpat with
      | "matchesAll", _ -> MatchesAll lpat
      | "matchesAny", _ -> MatchesAny lpat
      | "after", pat::_ -> After pat
      | "before", pat::_ -> Before pat
      | "fromTo", pat1::[] -> After pat1
      | "fromTo", pat1::pat2::_ -> FromTo (pat1,pat2)
      | "higherThan", pat::_ ->
	if string_is_float pat 
	then HigherThan pat
	else invalid_arg "a numeric value is expected"
      | "lowerThan", pat::_ ->
	if string_is_float pat
	then LowerThan pat
	else invalid_arg "a numeric value is expected"
      | "between", pat::[] ->
	if string_is_float pat
	then HigherThan pat
	else invalid_arg "a numeric value is expected"
      | "between", pat1::pat2::_ ->
	if string_is_float pat1 && string_is_float pat2
	then Between (pat1, pat2)
	else invalid_arg "two numeric values are expected"
      | "hasLang", pat::_ -> HasLang pat
      | "hasDatatype", pat::_ -> HasDatatype pat
      | _ -> True

let operator_of_constr = function
  | True -> "matchesAll"
  | MatchesAll _ -> "matchesAll"
  | MatchesAny _ -> "matchesAny"
  | After _ -> "after"
  | Before _ -> "before"
  | FromTo _ -> "fromTo"
  | HigherThan _ -> "higherThan"
  | LowerThan _ -> "lowerThan"
  | Between _ -> "between"
  | HasLang _ -> "hasLang"
  | HasDatatype _ -> "hasDatatype"

let pattern_of_constr = function
  | True -> ""
  | MatchesAll lpat -> String.concat " " lpat
  | MatchesAny lpat -> String.concat " " lpat
  | After pat -> pat
  | Before pat -> pat
  | FromTo (pat1,pat2) -> pat1 ^ " " ^ pat2
  | HigherThan pat -> pat
  | LowerThan pat -> pat
  | Between (pat1,pat2) -> pat1 ^ " " ^ pat2
  | HasLang pat -> pat
  | HasDatatype pat -> pat

let compile_constr constr : term -> bool =
  let regexp_of_pat pat = Regexp.regexp_with_flag (Regexp.quote pat) "i" in
  let matches s re = Regexp.search re s 0 <> None in
  let leq t pat = try (float_of_term t) <= (float_of_string pat) with _ -> false in
  let geq t pat = try (float_of_term t) >= (float_of_string pat) with _ -> false in
  match constr with
    | True -> (fun t -> true)
    | MatchesAll lpat ->
      let lre = List.map regexp_of_pat lpat in
      (fun t ->
	let s = string_of_term t in
	List.for_all (fun re -> matches s re) lre)
    | MatchesAny lpat ->
      let lre = List.map regexp_of_pat lpat in
      (fun t ->
	let s = string_of_term t in
	List.exists (fun re -> matches s re) lre)
    | After pat ->
      (fun t -> (string_of_term t) >= pat)
    | Before pat ->
      (fun t -> (string_of_term t) <= pat)
    | FromTo (pat1,pat2) ->
      (fun t ->
	let s = string_of_term t in
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
	| PlainLiteral (s,lang) -> matches lang re
	| _ -> false)
    | HasDatatype pat ->
      let re = regexp_of_pat pat in
      (function
	| Number (_,s,dt)
	| TypedLiteral (s,dt) -> matches dt re
	| _ -> false)

(* ------------------------- *)

type order = Highest | Lowest
type aggreg = NumberOf | ListOf | Total | Average | Maximum | Minimum
type modif_s2 = Id | Any | Aggreg of order option * aggreg | Order of order

(* LISQL elts *)
type elt_p1 =
  | Type of uri
  | Has of uri * elt_s1
  | IsOf of uri * elt_s1
  | Constr of constr
  | And of elt_p1 array
  | Or of elt_p1 array
  | Maybe of elt_p1
  | Not of elt_p1
  | IsThere
and elt_s1 =
  | Det of elt_s2 * elt_p1 option
(*  | Aggreg of modif_s2 * aggreg * elt_s1 *)
and elt_s2 =
  | Term of term
  | An of modif_s2 * elt_head
and elt_head =
  | Thing
  | Class of uri
(*  | Aggreg of aggreg * elt_head * elt_p1 option *)
and elt_s =
  | Return of elt_s1

let top_p1 = IsThere
let top_s2 = An (Id, Thing)
let top_s1 = Det (top_s2,None)

(* LISQL contexts *)
type ctx_p1 =
  | DetThatX of elt_s2 * ctx_s1
  | AndX of int * elt_p1 array * ctx_p1
  | OrX of int * elt_p1 array * ctx_p1
  | MaybeX of ctx_p1
  | NotX of ctx_p1
and ctx_s1 =
  | HasX of uri * ctx_p1
  | IsOfX of uri * ctx_p1
(*  | AggregX of modif_s2 * aggreg * ctx_s1 *)
  | ReturnX

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
  | HasX (p,ctx) -> elt_s_of_ctx_p1 (Has (p,f)) ctx
  | IsOfX (p,ctx) -> elt_s_of_ctx_p1 (IsOf (p,f)) ctx
  | ReturnX -> Return f

let elt_s_of_focus = function
  | AtP1 (f,ctx) -> elt_s_of_ctx_p1 f ctx
  | AtS1 (f,ctx) -> elt_s_of_ctx_s1 f ctx
  | AtS f -> f


(* translation from LISQL elts to SPARQL queries *)

(* SPARQL variable generator *)
class sparql_state =
object
  val mutable prefix_cpt = []
  val mutable vars = []

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
    vars <- v::vars;
    v

  method vars = List.rev vars

  val mutable focus_term : term option = None
  method set_focus_term t_opt = focus_term <- t_opt
  method focus_term = focus_term

  val h_var_modif : (var, modif_s2) Hashtbl.t = Hashtbl.create 13
  method set_modif (v : var) (modif : modif_s2) : unit =
    Hashtbl.add h_var_modif v modif
  method modif (v : var) =
    try Hashtbl.find h_var_modif v
    with _ -> Id
end

let sparql_uri uri = 
  if uri = "a"
  then uri
  else "<" ^ uri ^ ">"

let sparql_var v = "?" ^ v

let sparql_string s =
  if String.contains s '\n' || String.contains s '"'
  then "\"\"\"" ^ s ^ "\"\"\""
  else "\"" ^ s ^ "\""

let rec sparql_term = function
  | URI uri -> sparql_uri uri
  | Number (f,s,dt) -> sparql_term (TypedLiteral (s,dt))
  | TypedLiteral (s,dt) -> sparql_string s ^ "^^" ^ sparql_uri dt
  | PlainLiteral (s,lang) -> sparql_string s ^ (if lang = "" then "" else "@" ^ lang)
  | Bnode name -> if name="" then "[]" else "_:" ^ name
  | Var v -> sparql_var v

let sparql_empty = ""

let sparql_triple s p o = sparql_term s ^ " " ^ sparql_term p ^ " " ^ sparql_term o ^ " . "

let sparql_expr_func f expr = f ^ "(" ^ expr ^ ")"
let sparql_expr_regex expr pat = "REGEX(" ^ expr ^ ", \"" ^ pat ^ "\", 'i')"
let sparql_expr_comp relop expr1 expr2 = expr1 ^ " " ^ relop ^ " " ^ expr2

let sparql_filter lexpr = "FILTER(" ^ String.concat " && " lexpr ^ ")"
let sparql_constr t = function
  | True -> sparql_empty
  | MatchesAll lpat ->
    sparql_filter
      (List.map
	 (fun pat -> sparql_expr_regex (sparql_expr_func "str" (sparql_term t)) pat)
	 lpat)
  | MatchesAny lpat ->
    sparql_filter
      [String.concat " || "
	  (List.map
	     (fun pat -> sparql_expr_regex (sparql_expr_func "str" (sparql_term t)) pat)
	     lpat) ]
  | After pat ->
    sparql_filter [sparql_expr_comp ">=" (sparql_expr_func "str" (sparql_term t)) (sparql_string pat)]
  | Before pat ->
    sparql_filter [sparql_expr_comp "<=" (sparql_expr_func "str" (sparql_term t)) (sparql_string pat)]
  | FromTo (pat1,pat2) ->
    sparql_filter
      [sparql_expr_comp ">=" (sparql_expr_func "str" (sparql_term t)) (sparql_string pat1);
       sparql_expr_comp "<=" (sparql_expr_func "str" (sparql_term t)) (sparql_string pat2)]
  | HigherThan pat ->
    sparql_filter
      [sparql_expr_func "isNumeric" (sparql_term t);
       sparql_expr_comp ">=" (sparql_term t) pat]
  | LowerThan pat ->
    sparql_filter
      [sparql_expr_func "isNumeric" (sparql_term t);
       sparql_expr_comp "<=" (sparql_term t) pat]
  | Between (pat1,pat2) ->
    sparql_filter
      [sparql_expr_func "isNumeric" (sparql_term t);
       sparql_expr_comp ">=" (sparql_term t) pat1;
       sparql_expr_comp "<=" (sparql_term t) pat2]
  | HasLang pat ->
    sparql_filter
      [sparql_expr_func "isLiteral" (sparql_term t);
       sparql_expr_regex (sparql_expr_func "lang" (sparql_term t)) pat]
  | HasDatatype pat ->
    sparql_filter
      [sparql_expr_func "isLiteral" (sparql_term t);
       sparql_expr_regex (sparql_expr_func "str" (sparql_expr_func "datatype" (sparql_term t))) pat]

let sparql_join lgp =
  String.concat "\n"
    (List.filter ((<>) "") lgp)
let sparql_union lgp =
  match List.filter ((<>) "") lgp with
  | [] -> sparql_empty
  | [gp] -> gp
  | lgp -> "{ " ^ String.concat " } UNION { " lgp ^ " }"
let sparql_optional gp = "OPTIONAL { " ^ gp ^ " }"
let sparql_not_exists gp = "FILTER NOT EXISTS { " ^ gp ^ " }"

let sparql_ask gp =
  "ASK WHERE {\n" ^ gp ^ "\n}"
let sparql_select ?(distinct=false) ~dimensions ?(aggregations=[]) ?(ordering=[]) ?limit gp =
  if dimensions = [] && aggregations = []
  then sparql_ask gp
  else
    let sparql_aggreg prefix_g v suffix_g vg = "(" ^ prefix_g ^ sparql_var v ^ suffix_g ^ " AS " ^ sparql_var vg ^ ")" in
    let sel =
      String.concat " " (List.map sparql_var dimensions) ^ " " ^
	String.concat " "
	(List.map
	   (fun (g,v,vg) ->
	     match g with
	       | NumberOf -> sparql_aggreg "COUNT(DISTINCT " v ")" vg
	       | Total -> sparql_aggreg "SUM(" v ")" vg
	       | Average -> sparql_aggreg "AVG(" v ")" vg
	       | Maximum -> sparql_aggreg "MAX(" v ")" vg
	       | Minimum -> sparql_aggreg "MIN(" v ")" vg
	       | ListOf -> sparql_aggreg "GROUP_CONCAT(" v (" ; separator=', ')") vg)
	   aggregations) in
    let s = "SELECT " ^ (if distinct then "DISTINCT " else "") ^ sel ^ " WHERE {\n" ^ gp ^ "\n}" in
    let s =
      if aggregations = [] || dimensions = []
      then s
      else s ^ "\nGROUP BY " ^ String.concat " " (List.map sparql_var dimensions) in
    let s =
      if ordering = []
      then s
      else s ^ "\nORDER BY " ^ String.concat " " (List.map (function `ASC v -> sparql_var v | `DESC v -> "DESC(" ^ sparql_var v ^ ")") ordering) in
    let s = match limit with None -> s | Some n -> s ^ "\nLIMIT " ^ string_of_int n in
    s

let rec sparql_of_elt_p1 state : elt_p1 -> (term -> string) = function
  | Type c -> (fun x -> sparql_triple x (URI "a") (URI c))
  | Has (p,np) -> (fun x -> sparql_of_elt_s1 state ~prefix:(prefix_of_uri p) np (fun y -> sparql_triple x (URI p) y))
  | IsOf (p,np) -> (fun x -> sparql_of_elt_s1 state ~prefix:"" np (fun y -> sparql_triple y (URI p) x))
  | Constr constr -> (fun x -> sparql_constr x constr)
  | And ar ->
    (fun x ->
      sparql_join
	(Array.to_list
	   (Array.map
	      (fun elt -> sparql_of_elt_p1 state elt x)
	      ar)))
  | Or ar ->
    (fun x ->
      sparql_union
	(Array.to_list
	   (Array.map
	      (fun elt -> sparql_of_elt_p1 state elt x)
	      ar)))
  | Maybe f -> (fun x -> sparql_optional (sparql_of_elt_p1 state f x))
  | Not f -> (fun x -> sparql_not_exists (sparql_of_elt_p1 state f x))
  | IsThere -> (fun x -> sparql_empty)
and sparql_of_elt_s1 state ~prefix : elt_s1 -> ((term -> string) -> string) = function
  | Det (det,rel_opt) ->
    let prefix =
      if prefix = ""
      then
	match rel_opt with
	  | Some (IsOf (p,_)) -> prefix_of_uri p
	  | _ -> prefix
      else prefix in
    let d1 = match rel_opt with None -> (fun x -> sparql_empty) | Some rel -> sparql_of_elt_p1 state rel in
    (fun d -> sparql_of_elt_s2 state ~prefix det d1 d)
and sparql_of_elt_s2 state ~prefix : elt_s2 -> ((term -> string) -> (term -> string) -> string) = function
  | Term t -> (fun d1 d2 -> sparql_join [d1 t; d2 t])
  | An (modif, head) ->
    (fun d1 d2 ->
      let v, dhead = sparql_of_elt_head state ~prefix head in
      state#set_modif v modif;
      let t = Var v in
      sparql_join [d2 t; dhead t; d1 t])
and sparql_of_elt_head state ~prefix : elt_head -> var * (term -> string) = function
  | Thing ->
    let prefix = if prefix<>"" then prefix else "thing" in
    state#new_var prefix, (fun t -> sparql_empty)
  | Class c ->
    let prefix = if prefix<>"" then prefix else prefix_of_uri c in
    state#new_var prefix, (fun t -> sparql_triple t (URI "a") (URI c))
(*
  | Aggreg (g, head2, rel2_opt) ->
    let v2, dhead2 = sparql_of_elt_head state ~prefix head2 in
    let v = match g with Count -> "number_of_" ^ v in
    let drel2 = match rel2_opt with None -> (fun t2 -> sparql_empty) | Some rel2 -> sparql_of_elt_p1 state rel2 in
    v, (fun t -> sparql_aggreg g t v2 (fun t2 -> sparql_join [dhead2 t2; drel2 t2]))
*)
and sparql_of_elt_s state : elt_s -> string = function
  | Return np ->
    sparql_of_elt_s1 state ~prefix:"" np (fun t -> "")

let rec sparql_of_ctx_p1 state ~prefix (d : term -> string) : ctx_p1 -> string = function
  | DetThatX (det,ctx) ->
    let prefix =
      if prefix = ""
      then
	match ctx with
	  | HasX (p,_) -> prefix_of_uri p
	  | _ -> prefix
      else prefix in
    sparql_of_ctx_s1 state 
      (fun d2 -> sparql_of_elt_s2 state ~prefix det d d2) 
      ctx
  | AndX (i,ar,ctx) ->
    sparql_of_ctx_p1 state ~prefix
      (fun x ->
	sparql_join
	  (Array.to_list
	     (Array.mapi
		(fun j elt ->
		  if j=i
		  then d x
		  else sparql_of_elt_p1 state elt x)
		ar)))
      ctx
  (* ignoring algebra in ctx *)
  | OrX (i,ar,ctx) -> sparql_of_ctx_p1 state ~prefix d ctx
  | MaybeX ctx -> sparql_of_ctx_p1 state ~prefix d ctx
  | NotX ctx -> sparql_of_ctx_p1 state ~prefix d ctx
and sparql_of_ctx_s1 state (q : (term -> string) -> string) : ctx_s1 -> string = function
  | HasX (p,ctx) ->
    sparql_of_ctx_p1 state ~prefix:""
      (fun x -> q (fun y -> sparql_triple x (URI p) y))
      ctx
  | IsOfX (p,ctx) ->
    sparql_of_ctx_p1 state ~prefix:(prefix_of_uri p)
      (fun x -> q (fun y -> sparql_triple y (URI p) x))
      ctx
  | ReturnX ->
    q (fun t -> "")

type sparql_template = ?constr:constr -> limit:int -> string

let sparql_of_focus (focus : focus) : term option * sparql_template option * sparql_template option * sparql_template option * sparql_template option =
  let state = new sparql_state in
  let gp =
    match focus with
      | AtP1 (f,ctx) ->
	let prefix =
	  match f with
	    | IsOf (p, _) -> prefix_of_uri p
	    | _ -> "" in
	sparql_of_ctx_p1 state ~prefix
	  (fun t ->
	    state#set_focus_term (Some t);
	    sparql_of_elt_p1 state f t)
	  ctx
      | AtS1 (f,ctx) ->
	let prefix =
	  match ctx with
	    | HasX (p,_) -> prefix_of_uri p
	    | _ -> "" in
	sparql_of_ctx_s1 state (fun d ->
	  sparql_of_elt_s1 state ~prefix f
	    (fun t ->
	      state#set_focus_term (Some t);
	      d t))
	  ctx
      | AtS f ->
	state#set_focus_term None;
	sparql_of_elt_s state f
  in
  let t_opt = state#focus_term in
  let query_opt =
    if gp = sparql_empty
    then None
    else
      let lv = state#vars in
      let dimensions, aggregations, ordering =
	List.fold_right
	  (fun v (dims,aggregs,ordering) ->
	    match state#modif v with
	      | Any when t_opt <> Some (Var v) -> dims, aggregs, ordering
	      | Aggreg (order_opt, g) when t_opt <> Some (Var v) ->
		let vg_prefix =
		  match g with
		    | NumberOf -> "number_of_"
		    | ListOf -> "list_of_"
		    | Total -> "total_"
		    | Average -> "average_"
		    | Maximum -> "maximum_"
		    | Minimum -> "minimum_" in
		let vg = vg_prefix ^ v in
		dims, (g,v,vg)::aggregs, (match order_opt with None -> ordering | Some Lowest -> (`ASC vg)::ordering | Some Highest -> (`DESC vg)::ordering)
	      | Order o ->
		let order =
		  match o with
		    | Lowest -> `ASC v
		    | Highest -> `DESC v in
		v::dims, aggregs, order::ordering
	      | _ -> v::dims, aggregs, ordering)
	  lv ([],[],[]) in
      Some (fun ?(constr=True) ~limit ->
	sparql_select ~distinct:true ~dimensions ~aggregations ~ordering ~limit
	  (match t_opt with None -> gp | Some t -> sparql_join [gp; sparql_constr t constr])) in
  let query_incr_opt x triple =
    match t_opt with
      | None -> None
      | Some t ->
	let tx = Var x in
	let gp_x =
	  match t with
	    | Var v -> sparql_join [gp; triple t tx]
	    | _ -> triple t tx in
	Some (fun ?(constr=True) ~limit ->
	  sparql_select ~dimensions:[x] ~limit
	    (sparql_join [gp_x; sparql_constr tx constr])) in
  let query_class_opt = query_incr_opt "class" (fun t tc -> sparql_triple t (URI "a") tc) in
  let query_prop_has_opt = query_incr_opt "prop" (fun t tp -> sparql_triple t tp (Bnode "")) in
  let query_prop_isof_opt = query_incr_opt "prop" (fun t tp -> sparql_triple (Bnode "") tp t) in
  t_opt, query_opt, query_class_opt, query_prop_has_opt, query_prop_isof_opt


(* NL generation from focus *)

type nl_word =
  [ `Thing
  | `Class of uri
  | `Prop of uri
  | `Op of string
  | `Term of term
  | `Literal of string
  | `DummyFocus ]

type nl_focus =
  [ `NoFocus
  | `Focus of focus * [ `In | `At | `Out ] ]

type nl_s =
  [ `Return of nl_focus * nl_np ]
and nl_np =
  [ `PN of nl_focus * nl_word * nl_rel
  | `Qu of nl_focus * nl_qu * nl_adj * nl_word * nl_rel
  | `QuOneOf of nl_qu * nl_word list ]
and nl_qu = [ `A | `Any | `The | `All ]
and nl_adj =
  [ `Nil
  | `Adj of nl_adj * nl_word ]
and nl_rel =
  [ `Nil
  | `That of nl_vp
  | `Of of nl_np
  | `Ing of nl_word * nl_np ]
and nl_vp =
  [ `IsThere of nl_focus
  | `IsA of nl_focus * nl_word * nl_rel
  | `IsPP of nl_focus * nl_pp
  | `HasProp of nl_focus * nl_word * nl_np
  | `Has of nl_focus * nl_np
  | `VT of nl_focus * nl_word * nl_np
  | `And of nl_focus * nl_vp array
  | `Or of nl_focus * nl_vp array
  | `Maybe of nl_focus * nl_vp
  | `Not of nl_focus * nl_vp
  | `DummyFocus ]
and nl_pp =
  [ `Prep of nl_word * nl_word
  | `PrepBin of nl_word * nl_word * nl_word * nl_word ]

let top_vp = `IsThere `NoFocus
let top_rel = `That top_vp
let top_np = `Qu (`NoFocus, `A, `Nil, `Thing, `Nil)
let top_s = `Return (`NoFocus, top_np)

let focus_pos_down = function `In -> `In | `At -> `In | `Out -> `Out

let rec head_of_modif foc nn rel : modif_s2 -> nl_np = function
  | Id -> `Qu (foc, `A, `Nil, nn, rel)
  | Any -> `Qu (foc, `Any, `Nil, nn, rel)
  | Order o -> `Qu (foc, `The, adj_of_order o, nn, rel)
  | Aggreg (None, g) -> `Qu (foc, `A, adj_of_aggreg `Nil g, nn, rel)
  | Aggreg (Some o, g) -> `Qu (foc, `The, adj_of_aggreg (adj_of_order o) g, nn, rel)
and adj_of_order : order -> nl_adj = function
  | Highest -> `Adj (`Nil, `Op "highest")
  | Lowest -> `Adj (`Nil, `Op "lowest")
and adj_of_aggreg adj : aggreg -> nl_adj = function
  | NumberOf -> `Adj (adj, `Op "number of")
  | ListOf -> `Adj (adj, `Op "list of")
  | Total -> `Adj (adj, `Op "total")
  | Average -> `Adj (adj, `Op "average")
  | Maximum -> `Adj (adj, `Op "maximum")
  | Minimum -> `Adj (adj, `Op "minimum")

let rec vp_of_elt_p1 pos ctx f : nl_vp =
  let foc = `Focus (AtP1 (f,ctx), pos) in
  match f with
    | IsThere -> `IsThere foc
    | Type c -> `IsA (foc, `Class c, `Nil)
    | Has (p,np) -> `HasProp (foc, `Prop p, np_of_elt_s1 (focus_pos_down pos) (HasX (p,ctx)) np)
    | IsOf (p,np) -> `IsA (foc, `Prop p, `Of (np_of_elt_s1 (focus_pos_down pos) (IsOfX (p,ctx)) np))
    | Constr c -> vp_of_constr foc c
    | And ar -> `And (foc, Array.mapi (fun i elt -> vp_of_elt_p1 (focus_pos_down pos) (AndX (i,ar,ctx)) elt) ar)
    | Or ar -> `Or (foc, Array.mapi (fun i elt -> vp_of_elt_p1 (focus_pos_down pos) (OrX (i,ar,ctx)) elt) ar)
    | Maybe elt -> `Maybe (foc, vp_of_elt_p1 (focus_pos_down pos) (MaybeX ctx) elt)
    | Not elt -> `Not (foc, vp_of_elt_p1 (focus_pos_down pos) (NotX ctx) elt)
and vp_of_constr foc : constr -> nl_vp = function
  | True -> `IsThere foc
  | MatchesAll lpat -> `VT (foc, `Op "matches", `QuOneOf (`All, List.map (fun pat -> `Literal pat) lpat))
  | MatchesAny lpat -> `VT (foc, `Op "matches", `QuOneOf (`Any, List.map (fun pat -> `Literal pat) lpat))
  | After pat -> `IsPP (foc, `Prep (`Op "after", `Literal pat))
  | Before pat -> `IsPP (foc, `Prep (`Op "before", `Literal pat))
  | FromTo (pat1,pat2) -> `IsPP (foc, `PrepBin (`Op "from", `Literal pat1, `Op "to", `Literal pat2))
  | HigherThan pat -> `IsPP (foc, `Prep (`Op "higher than", `Literal pat))
  | LowerThan pat -> `IsPP (foc, `Prep (`Op "lower than", `Literal pat))
  | Between (pat1,pat2) -> `IsPP (foc, `PrepBin (`Op "between", `Literal pat1, `Op "and", `Literal pat2))
  | HasLang pat -> `Has (foc, `Qu (`NoFocus, `A, `Nil, `Op "language", `Ing (`Op "matching", `PN (`NoFocus, `Literal pat, `Nil))))
  | HasDatatype pat -> `Has (foc, `Qu (`NoFocus, `A, `Nil, `Op "datatype", `Ing (`Op "matching", `PN (`NoFocus, `Literal pat, `Nil))))
and np_of_elt_s1 pos ctx f : nl_np =
  let foc = `Focus (AtS1 (f,ctx),pos) in
  match f with
    | Det (det, None) -> det_of_elt_s2 foc `Nil det
    | Det (det, Some rel) -> det_of_elt_s2 foc (`That (vp_of_elt_p1 (focus_pos_down pos) (DetThatX (det, ctx)) rel)) det
and det_of_elt_s2 foc rel : elt_s2 -> nl_np = function
  | Term t -> `PN (foc, `Term t, rel)
  | An (modif, head) -> head_of_modif foc (match head with Thing -> `Thing | Class c -> `Class c) rel modif
and s_of_elt_s pos : elt_s -> nl_s = function
  | Return np -> `Return (`Focus (AtS (Return np), pos), np_of_elt_s1 (focus_pos_down pos) ReturnX np)

let rec s_of_ctx_p1 f nl ctx : nl_s =
  match ctx with
    | DetThatX (det,ctx2) ->
      let f2 = Det (det, Some f) in
      let nl2 = det_of_elt_s2 (`Focus (AtS1 (f2,ctx2), `Out)) (`That nl) det in
      s_of_ctx_s1 f2 nl2 ctx2
    | AndX (i,ar,ctx2) ->
      let f2 = ar.(i) <- f; And ar in
      let nl2 =
	`And (`Focus (AtP1 (f2,ctx2), `Out),
	      Array.mapi
		(fun j elt -> if j=i then nl else vp_of_elt_p1 `Out (AndX (j,ar,ctx2)) elt)
		ar) in
      s_of_ctx_p1 f2 nl2 ctx2
    | OrX (i,ar,ctx2) ->
      ar.(i) <- f;
      let f2 = Or ar in
      let nl2 =
	`Or (`Focus (AtP1 (f2,ctx2), `Out),
	     Array.mapi
	       (fun j elt -> if j=i then nl else vp_of_elt_p1 `Out (OrX (j,ar,ctx2)) elt)
	       ar) in
      s_of_ctx_p1 f2 nl2 ctx2
   | MaybeX ctx2 ->
      let f2 = Maybe f in
      let nl2 = `Maybe (`Focus (AtP1 (f2,ctx2), `Out), nl) in
      s_of_ctx_p1 f2 nl2 ctx2
   | NotX ctx2 ->
      let f2 = Not f in
      let nl2 = `Not (`Focus (AtP1 (f2,ctx2), `Out), nl) in
      s_of_ctx_p1 f2 nl2 ctx2
and s_of_ctx_s1 f nl ctx =
  match ctx with
    | HasX (p,ctx2) ->
      let f2 = Has (p,f) in
      let nl2 = `HasProp (`Focus (AtP1 (f2,ctx2), `Out), `Prop p, nl) in
      s_of_ctx_p1 f2 nl2 ctx2
    | IsOfX (p,ctx2) ->
      let f2 = IsOf (p,f) in
      let nl2 = `IsA (`Focus (AtP1 (f2,ctx2), `Out), `Prop p, `Of nl) in
      s_of_ctx_p1 f2 nl2 ctx2
    | ReturnX ->
      let f2 = Return f in
      let nl2 = `Return (`Focus (AtS f2, `Out), nl) in
      nl2

let s_of_focus : focus -> nl_s = function
  | AtP1 (f,ctx) -> s_of_ctx_p1 f (vp_of_elt_p1 `At ctx f) ctx
  | AtS1 (f,ctx) -> s_of_ctx_s1 f (np_of_elt_s1 `At ctx f) ctx
  | AtS f -> s_of_elt_s `Out f

(* pretty-printing of terms, NL in HTML *)

let html_pre text =
  let text = Regexp.global_replace (Regexp.regexp "<") text "&lt;" in
  let text = Regexp.global_replace (Regexp.regexp ">") text "&gt;" in  
  "<pre>" ^ text ^ "</pre>"

let html_span ?id ?classe ?title text =
  "<span" ^
    (match id with None -> "" | Some id -> " id=\"" ^ id ^ "\"") ^
    (match classe with None -> "" | Some cl -> " class=\"" ^ cl ^ "\"") ^
    (match title with None -> "" | Some tit -> " title=\"" ^ tit ^ "\"") ^
    ">" ^ text ^ "</span>"

let html_div ?classe ?title text =
  "<div" ^
    (match classe with None -> "" | Some cl -> " class=\"" ^ cl ^ "\"") ^
    (match title with None -> "" | Some tit -> " title=\"" ^ tit ^ "\"") ^
    ">" ^ text ^ "</div>"

let html_a url html =
  "<a target=\"_blank\" href=\"" ^ url ^ "\">" ^ html ^ "</a>"

let html_img ?(height = 120) url =
  "<img src=\"" ^ url ^ "\" alt=\"" ^ name_of_uri url ^ "\" height=\"" ^ string_of_int height ^ "\">"

let html_count_unit count max unit units =
  if count = 0 then "No " ^ unit
  else if count = 1 then "1 " ^ unit
  else if count >= max then string_of_int count ^ "+ " ^ units
  else string_of_int count ^ " " ^ units

let html_literal s = html_span ~classe:"Literal" s
let html_uri uri = html_span ~classe:"URI" ~title:uri (name_of_uri uri)
let html_class c = html_span ~classe:"classURI" ~title:c (name_of_uri c)
let html_prop p = html_span ~classe:"propURI" ~title:p (name_of_uri p)
let html_modifier m = html_span ~classe:"modifier" m

let rec html_term ?(link = false) = function
  | URI uri ->
    (*if uri_is_image uri (* too heavy loading *)
    then
      if link
      then html_a uri (html_img uri)
      else html_img ~height:60 uri
    else*)
      if link
      then html_a uri (name_of_uri uri)
      else html_uri uri
  | Number (f,s,dt) -> html_term ~link (TypedLiteral (s,dt))
  | TypedLiteral (s,dt) -> html_literal s ^ " (" ^ name_of_uri dt ^ ")"
  | PlainLiteral (s,lang) -> html_literal s ^ (if lang="" then "" else " (" ^ lang ^ ")")
  | Bnode id -> "_:" ^ id
  | Var v -> "?" ^ v

let html_and ar_html =
  let html = ref ("<ul class=\"list-and\"><li>" ^ ar_html.(0) ^ "</li>") in
  for i=1 to Array.length ar_html - 1 do
    html := !html ^ " <li>and " ^ ar_html.(i) ^ "</li>"
  done;
  !html ^ "</ul>"
let html_or ar_html =
  let html = ref ("<ul class=\"list-or\"><li>" ^ ar_html.(0) ^ "</li>") in
  for i=1 to Array.length ar_html - 1 do
    html := !html ^ " <li>" ^ html_modifier "or" ^ " " ^ ar_html.(i) ^ "</li>"
  done;
  !html ^ "</ul>"
let html_maybe html = html_modifier "optionally" ^ " " ^ html
let html_not html = html_modifier "not" ^ " " ^ html
let html_is_there = "..."
let html_return np = "Give me " ^ np
let html_dummy_focus = "<span class=\"in-current-focus\">___</span>"

let html_current_focus html =
  html_span ~id:"current-focus" ~classe:"in-current-focus"
      (html ^ " <img src=\"icon-delete.png\" height=\"16\" alt=\"Delete\" id=\"delete-current-focus\" title=\"Click on this red cross to delete the current focus\">")

let html_word = function
  | `Thing -> "thing"
  | `Term t -> html_term t
  | `Class c -> html_class c
  | `Prop p -> html_prop p
  | `Literal l -> html_literal l
  | `Op op -> html_modifier op
  | `DummyFocus -> html_dummy_focus

let html_focus dico (foc : nl_focus) (html : string) : string =
  match foc with
    | `NoFocus -> html
    | `Focus (focus, pos) ->
      let id = dico#add focus in
      let html = "<span id=\"" ^ id ^ "\" class=\"focus" ^ (if pos <> `Out then " in-current-focus" else "") ^ "\">" ^ html ^ "</span>" in
      if pos = `At
      then html_current_focus html
      else html

let rec html_of_s dico : nl_s -> string = function
  | `Return (foc, np) -> html_focus dico foc (html_return (html_of_np dico np))
and html_of_np dico : nl_np -> string = function
  | `PN (foc, w, rel) -> html_focus dico foc (html_word w ^ html_of_rel dico rel)
  | `Qu (foc, `A, `Nil, `Thing, `Nil) -> html_focus dico foc "something"
  | `Qu (foc, qu, adj, `Thing, `That (`IsA (foc2, w, rel2))) ->
    html_focus dico foc (html_of_qu qu ^ html_of_adj adj ^ html_focus dico foc2 (html_word w ^ html_of_rel dico rel2))
  | `Qu (foc, qu, adj, w, rel) -> html_focus dico foc (html_of_qu qu ^ html_of_adj adj ^ html_word w ^ html_of_rel dico rel)
  | `QuOneOf (_, [w]) -> html_word w
  | `QuOneOf (qu, lw) -> html_of_qu qu ^ "of " ^ String.concat ", " (List.map html_word lw)
and html_of_qu : nl_qu -> string = function
  | `A -> "a "
  | `Any -> "any "
  | `The -> "the "
  | `All -> "all "
and html_of_adj : nl_adj -> string = function
  | `Nil -> ""
  | `Adj (a, w) -> html_of_adj a ^ html_word w ^ " "
and html_of_rel dico : nl_rel -> string = function
  | `Nil -> ""
(*  | `That (`HasProp (foc, p, `Qu (foc2, `A, `Nil, `Thing, `That vp))) -> " whose " ^ html_focus dico foc (html_word p ^ " " ^ html_focus dico foc2 (html_of_vp dico vp)) *)
  | `That vp -> " that " ^ html_of_vp dico vp
  | `Of np -> " of " ^ html_of_np dico np
  | `Ing (w, np) -> " " ^ html_word w ^ " " ^ html_of_np dico np
and html_of_vp dico : nl_vp -> string = function
  | `IsThere foc -> html_focus dico foc (html_is_there)
  | `IsA (foc, w, rel) -> html_focus dico foc ("is a " ^ html_word w ^ html_of_rel dico rel)
  | `IsPP (foc, pp) -> html_focus dico foc ("is " ^ html_of_pp dico pp)
  | `HasProp (foc, w, `Qu (foc2, qu, adj, `Thing, rel)) -> html_of_vp dico (`Has (foc, `Qu (foc2, qu, adj, w, rel)))
  | `HasProp (foc, p, np) -> html_focus dico foc ("has " ^ html_word p ^ " " ^ html_of_np dico np)
  | `Has (foc, np) -> html_focus dico foc ("has " ^ html_of_np dico np)
  | `VT (foc, w, np) -> html_focus dico foc (html_word w ^ " " ^ html_of_np dico np)
  | `And (foc, ar) -> html_focus dico foc (html_and (Array.map (html_of_vp dico) ar))
  | `Or (foc, ar) -> html_focus dico foc (html_or (Array.map (html_of_vp dico) ar))
  | `Maybe (foc, vp) -> html_focus dico foc (html_maybe (html_of_vp dico vp))
  | `Not (foc, vp) -> html_focus dico foc (html_not (html_of_vp dico vp))
  | `DummyFocus -> html_dummy_focus
and html_of_pp dico : nl_pp -> string = function
  | `Prep (prep,w) -> html_word prep ^ " " ^ html_word w
  | `PrepBin (prep1,w1,prep2,w2) -> html_word prep1 ^ " " ^ html_word w1 ^ " " ^ html_word prep2 ^ " " ^ html_word w2

let html_of_focus dico focus = html_of_s dico (s_of_focus focus)


(* focus moves *)

let home_focus = AtS1 (top_s1, ReturnX)

let down_p1 (ctx : ctx_p1) : elt_p1 -> focus option = function
  | Type _ -> None
  | Has (p,np) -> Some (AtS1 (np, HasX (p,ctx)))
  | IsOf (p,np) -> Some (AtS1 (np, IsOfX (p,ctx)))
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
let up_s1 f = function
(*
  | HasX (p, DetThatX (An (modif, Thing), ctx)) -> Some (AtS1 (Det (An (modif, Thing), Some (Has (p,f))), ctx))
  | IsOfX (p, DetThatX (An (modif, Thing), ctx)) -> Some (AtS1 (Det (An (modif, Thing), Some (IsOf (p,f))), ctx))
*)
  | HasX (p,ctx) -> Some (AtP1 (Has (p,f), ctx))
  | IsOfX (p,ctx) -> Some (AtP1 (IsOf (p,f), ctx))
  | ReturnX -> Some (AtS (Return f))
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
  | HasX _ -> None
  | IsOfX _ -> None
  | ReturnX -> None
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
  | HasX _ -> None
  | IsOfX _ -> None
  | ReturnX -> None
let left_focus = function
  | AtP1 (f,ctx) -> left_p1 f ctx
  | AtS1 (f,ctx) -> left_s1 f ctx
  | AtS f -> None

(* increments *)

type increment =
  | IncrTerm of term
  | IncrClass of uri
  | IncrProp of uri
  | IncrInvProp of uri
  | IncrOr
  | IncrMaybe
  | IncrNot
  | IncrModifS2 of modif_s2

let term_of_increment : increment -> term option = function
  | IncrTerm t -> Some t
  | IncrClass c -> Some (URI c)
  | IncrProp p -> Some (URI p)
  | IncrInvProp p -> Some (URI p)
  | IncrOr -> None
  | IncrMaybe -> None
  | IncrNot -> None
  | IncrModifS2 modif -> None

let insert_term t focus =
  let focus2_opt =
    match focus with
      | AtP1 (f, DetThatX (det,ctx)) ->
	if det = Term t
	then Some (AtP1 (f, DetThatX (top_s2, ctx)))
	else Some (AtP1 (f, DetThatX (Term t, ctx)))
      | AtS1 (Det (det,rel_opt), ctx) ->
	if det = Term t
	then Some (AtS1 (Det (top_s2, rel_opt), ctx))
	else Some (AtS1 (Det (Term t, rel_opt), ctx))
      | _ -> None in
  match focus2_opt with
    | Some (AtS1 (f, HasX (p, ctx))) -> Some (AtP1 (Has (p,f), ctx))
    | Some (AtS1 (f, IsOfX (p, ctx))) -> Some (AtP1 (IsOf (p,f), ctx))
    | other -> other

let append_and ctx elt_p1 = function
  | And ar ->
    let n = Array.length ar in
    let ar2 = Array.make (n+1) elt_p1 in
    Array.blit ar 0 ar2 0 n;
    AtP1 (elt_p1, AndX (n, ar2, ctx))
  | p1 ->
    AtP1 (elt_p1, AndX (1, [|p1; elt_p1|], ctx))
let append_or ctx elt_p1 = function
  | Or ar ->
    let n = Array.length ar in
    let ar2 = Array.make (n+1) elt_p1 in
    Array.blit ar 0 ar2 0 n;
    AtP1 (elt_p1, OrX (n, ar2, ctx))
  | p1 ->
    AtP1 (elt_p1, OrX (1, [|p1; elt_p1|], ctx))

let insert_elt_p1 elt = function
  | AtP1 (IsThere, ctx) -> Some (AtP1 (elt, ctx))
  | AtP1 (f, AndX (i,ar,ctx)) -> ar.(i) <- f; Some (append_and ctx elt (And ar))
  | AtP1 (f, ctx) -> Some (append_and ctx elt f)
  | AtS1 (Det (det, None), ctx) -> Some (AtP1 (elt, DetThatX (det,ctx)))
  | AtS1 (Det (det, Some rel), ctx) -> Some (append_and (DetThatX (det,ctx)) elt rel)
  | AtS _ -> None

let insert_class c = function
(*
  | AtP1 (f, DetThatX (det,ctx)) ->
    if det = Class c
    then Some (AtP1 (f, DetThatX (Something, ctx)))
    else Some (AtP1 (f, DetThatX (Class c, ctx)))
*)
  | AtS1 (Det (det,rel_opt), ctx) ->
    ( match det with
      | Term _ ->
	Some (AtS1 (Det (An (Id, Class c), rel_opt), ctx))
      | An (modif, Class c2) when c2 = c ->
	Some (AtS1 (Det (An (modif, Thing), rel_opt), ctx))
      | An (modif, _) ->
	Some (AtS1 (Det (An (modif, Class c), rel_opt), ctx)) )
  | focus -> insert_elt_p1 (Type c) focus

let insert_property p focus =
  match insert_elt_p1 (Has (p, top_s1)) focus with
    | Some foc -> down_focus foc
    | None -> None

let insert_inverse_property p focus =
  match insert_elt_p1 (IsOf (p, top_s1)) focus with
    | Some foc -> down_focus foc
    | None -> None

let insert_or = function
  | AtP1 (Or ar, ctx) -> Some (append_or ctx IsThere (Or ar))
  | AtP1 (f, OrX (i,ar,ctx2)) -> ar.(i) <- f; Some (append_or ctx2 IsThere (Or ar))
  | AtP1 (f, ctx) -> Some (append_or ctx IsThere f)
  | _ -> None

let insert_maybe = function
  | AtP1 (Maybe f, ctx) -> Some (AtP1 (f,ctx))
  | AtP1 (f, ctx) -> Some (AtP1 (Maybe f, ctx))
  | _ -> None

let insert_not = function
  | AtP1 (Not f, ctx) -> Some (AtP1 (f,ctx))
  | AtP1 (f, ctx) -> Some (AtP1 (Not f, ctx))
  | _ -> None

let insert_modif_s2 modif = function
  | AtS1 (Det (An (modif0, head), rel_opt), ctx) ->
    let modif2 =
      if modif = modif0
      then Id
      else modif in
    let foc2 = AtS1 (Det (An (modif2, head), rel_opt), ctx) in
    ( match modif2 with
      | Aggreg _ -> up_focus foc2 (* to enforce visible aggregation *)
      | _ -> Some foc2 )
  | _ -> None

let insert_increment incr focus =
  match incr with
    | IncrTerm t -> insert_term t focus
    | IncrClass c -> insert_class c focus
    | IncrProp p -> insert_property p focus
    | IncrInvProp p -> insert_inverse_property p focus
    | IncrOr -> insert_or focus
    | IncrMaybe -> insert_maybe focus
    | IncrNot -> insert_not focus
    | IncrModifS2 modif -> insert_modif_s2 modif focus

let delete_array ar i =
  let n = Array.length ar in
  if n = 1 then `Empty
  else if n = 2 then `Single ar.(1-i)
  else
    let ar2 = Array.make (n-1) (Type "") in
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
and delete_ctx_s1 = function
  | HasX (p,ctx) -> delete_ctx_p1 ctx
  | IsOfX (p,ctx) -> delete_ctx_p1 ctx
  | ReturnX -> None

let delete_focus = function
  | AtP1 (_,ctx) -> delete_ctx_p1 ctx
  | AtS1 (f, ctx) ->
    if f = top_s1
    then delete_ctx_s1 ctx
    else Some (AtS1 (top_s1, ctx))
  | AtS _ -> Some (AtS (Return top_s1))


(* HTML of increment lists *)

let html_of_increment_frequency focus dico_incrs (incr,freq) =
  let key = dico_incrs#add incr in
  let at_s1, at_s1_top =
    match focus with
      | AtP1 _ -> false, false
      | AtS1 (f,ctx) -> true, f = top_s1
      | AtS _ -> false, false in
  let text =
    match incr with
      | IncrTerm t -> html_term t
      | IncrClass c -> (if at_s1_top then "" else if at_s1 then "that is " else "and is ") ^ "a " ^ html_class c
      | IncrProp p -> (if at_s1 then "that " else "and ") ^ "has a " ^ html_prop p
      | IncrInvProp p -> (if at_s1_top then "" else if at_s1 then "that is " else "and is ") ^ "a " ^ html_prop p ^ " of"
      | IncrOr -> html_modifier "or " ^ html_is_there (*html_or [|html_dummy_focus; html_is_there|]*)
      | IncrMaybe -> html_maybe html_dummy_focus
      | IncrNot -> html_not html_dummy_focus
      | IncrModifS2 modif -> html_of_np dico_incrs#dico_foci (head_of_modif `NoFocus `DummyFocus `Nil modif)
  in
  let text_freq =
    if freq = 1
    then ""
    else " [" ^ string_of_int freq ^ "]" in
  "<span class=\"increment\" id=\"" ^ key ^ "\">" ^ text ^ text_freq ^ "</span>"

let html_of_increment_frequency_list focus dico_incrs lif =
  let buf = Buffer.create 1000 in
  Buffer.add_string buf "<ul>";
  List.iter
    (fun incr_freq ->
      Buffer.add_string buf "<li>";
      Buffer.add_string buf (html_of_increment_frequency focus dico_incrs incr_freq);
      Buffer.add_string buf "</li>")
    lif;
  Buffer.add_string buf "</ul>";
  Buffer.contents buf

(* ------------------- *)

(* SPARQL results JSon <--> OCaml *)

type sparql_results =
    { dim : int;
      vars : (string * int) list; (* the int is the rank of the string in the list *)
      length : int;
      bindings : term option array list;
    }

let empty_results = { dim=0; vars=[]; length=0; bindings=[]; }

let page_of_results (offset : int) (limit : int) results : sparql_results =
  let rec aux offset limit = function
    | [] -> []
    | binding::l ->
      if offset > 0 then aux (offset-1) limit l
      else if limit > 0 then binding :: aux offset (limit-1) l
      else []
  in
  { results with bindings = aux offset limit results.bindings }

let list_of_results_column (var : var) results : term list =
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

let index_of_results_column (var : var) results : (term * int) list =
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

let index_of_results_2columns (var_x : var) (var_count : var) results : (term * int) list =
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
		    | Some (Number (f,s,dt)) -> (try int_of_string s with _ -> 0)
		    | Some (TypedLiteral (s,dt)) -> (try int_of_string s with _ -> 0)
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

module Xml =
struct
  let find (elt : Dom.element t) (tag : string) : Dom.element t =
    let nodelist = elt##getElementsByTagName(string tag) in
    Opt.get (nodelist##item(0))
      (fun () -> failwith ("Xml.find: unfound tag: " ^ tag))

  let find_all (elt : Dom.element t) (tag : string) : Dom.element t list =
    let nodelist = elt##getElementsByTagName(string tag) in
    let l = nodelist##length in
    let res = ref [] in
    for i = l-1 downto 0 do
      Opt.case (nodelist##item(i))
	(fun () -> ())
	(fun e -> res := e::!res)
    done;
    !res

  let get_text (elt : Dom.element t) : string =
    Opt.case (elt##firstChild)
      (fun () -> "")
      (fun node ->
	if node##nodeType = Dom.TEXT
	then
	  Opt.case (node##nodeValue)
	    (fun () -> "")
	    (fun s -> to_string s)
	else "")
end

let sparql_results_of_xml (doc_xml : Dom.element Dom.document t) =
  Firebug.console##log(string "Entering sparql_results_of_xml");
  try
    let elt_xml : Dom.element t = doc_xml##documentElement in
    (try
      let elt_boolean = Xml.find elt_xml "boolean" in
      match Xml.get_text elt_boolean with
	| "true" -> { dim=0; vars=[]; length=1; bindings=[ [||] ]; }
	| _ -> empty_results
    with _ ->
      let elt_head : Dom.element t = Xml.find elt_xml "head" in
      let elts_var = Xml.find_all elt_head "variable" in
      let dim, rev_vars =
	List.fold_left
	  (fun (i, vars as res) elt_var ->
	    Opt.case (elt_var##getAttribute(string "name"))
	      (fun _ -> res)
	      (fun v ->
		let v = to_string v in
		if v = "_star_fake"
		then res
		else (i+1, (v,i)::vars)))
	  (0,[]) elts_var in
      let vars = List.rev rev_vars in
      let elt_results = Xml.find elt_xml "results" in
      let elts_result = Xml.find_all elt_results "result" in
      let length, rev_bindings =
	List.fold_left
	  (fun (j,l) elt_result ->
	    let binding = Array.make dim None in
	    let elts_binding = Xml.find_all elt_result "binding" in
	    List.iter
	      (fun elt_binding ->
		Opt.case (elt_binding##getAttribute(string "name"))
		  (fun () -> ())
		  (fun v ->
		    let i = List.assoc (to_string v) vars in
		    let term_opt =
		      try
			let elt_uri = Xml.find elt_binding "uri" in
			let uri = Xml.get_text elt_uri in
			Some (URI uri)
		      with _ ->
			try
			  let elt_lit = Xml.find elt_binding "literal" in
			  let s = Xml.get_text elt_lit in
			  Opt.case (elt_lit##getAttribute(string "xml:lang"))
			    (fun () ->
			      Opt.case (elt_lit##getAttribute(string "datatype"))
				(fun () -> Some (PlainLiteral (s, "")))
				(fun dt ->
				  try Some (Number (float_of_string s, s, to_string dt))
				  with _ -> Some (TypedLiteral (s, to_string dt))))
			    (fun lang -> Some (PlainLiteral (s, to_string lang)))
			with _ ->
			  try
			    let elt_bnode = Xml.find elt_binding "bnode" in
			    let id = Xml.get_text elt_bnode in
			    Some (Bnode id)
			  with _ ->
			    None in
		    binding.(i) <- term_opt))
	      elts_binding;
	    (j+1, binding::l))
	  (0,[]) elts_result in
      let bindings = List.rev rev_bindings in
      { dim; vars; length; bindings; })
  with exn ->
    Firebug.console##log(string (Printexc.to_string exn));
    empty_results

let sparql_results_of_json s_json =
  try
    let ojson = Json.unsafe_input (string s_json) in
    let ohead = Unsafe.get ojson (string "head") in
    let ovars = Unsafe.get ohead (string "vars") in
    let m = truncate (to_float (Unsafe.get ovars (string "length"))) in
    let dim, vars =
      let dim = ref 0 in
      let vars = ref [] in
      for i = m-1 downto 0 do
	let ovar = Unsafe.get ovars (string (string_of_int i)) in
	let var = to_string (Unsafe.get ovar (string "fullBytes")) in
	if var <> "_star_fake"
	then begin incr dim; vars := (var,i)::!vars end
      done;
      !dim, !vars in
    let oresults = Unsafe.get ojson (string "results") in
    let obindings = Unsafe.get oresults (string "bindings") in
    let n = truncate (to_float (Unsafe.get obindings (string "length"))) in
    let length, bindings =
      let len = ref 0 in
      let res = ref [] in
      for j = n-1 downto 0 do
	let obinding = Unsafe.get obindings (string (string_of_int j)) in
	let binding = Array.make m None in
	List.iter
	  (fun (var,i) ->
	    try
	      let ocell = Unsafe.get obinding (string var) in
	      let otype = Unsafe.get ocell (string "type") in
	      let ovalue = Unsafe.get ocell (string "value") in
	      let term =
		let v = Unsafe.get ovalue (string "fullBytes") in
		match to_string (Unsafe.get otype (string "fullBytes")) with
		  | "uri" -> URI (to_string v (*decodeURI v*))
		  | "bnode" -> Bnode (to_string v)
		  | "typed-literal" ->
		    let odatatype = Unsafe.get ocell (string "datatype") in
		    let s = to_string v in
		    let dt = to_string (decodeURI (Unsafe.get odatatype (string "fullBytes"))) in
		    (try Number (float_of_string s, s, dt)
		     with _ -> TypedLiteral (s, dt))
		  | "plain-literal" ->
		    let olang = Unsafe.get ocell (string "xml:lang") in
		    PlainLiteral (to_string v, to_string (Unsafe.get olang (string "fullBytes")))
		  | "literal" ->
		    ( try
			let odatatype = Unsafe.get ocell (string "datatype") in
			let s = to_string v in
			let dt = to_string (decodeURI (Unsafe.get odatatype (string "fullBytes"))) in
			(try Number (float_of_string s, s, dt)
			 with _ -> TypedLiteral (s, dt))
		      with _ ->
			let olang = Unsafe.get ocell (string "xml:lang") in
			PlainLiteral (to_string v, to_string (Unsafe.get olang (string "fullBytes"))) )
		  | other ->
		    Firebug.console##log(string ("unexpected value type in SPARQL results: " ^ other));
		    assert false in
	      binding.(i) <- Some term
	    with _ ->
	      binding.(i) <- None)
	  vars;
	incr len;
	res := binding::!res
      done;
      !len, !res in
    { dim; vars; length; bindings; }
  with exn ->
    Firebug.console##log(s_json);
    Firebug.console##log(string (Printexc.to_string exn));
    empty_results

let html_video url mime =
  "<video width=\"320\" height=\"240\" controls>\
  <source src=\"" ^ url ^ "\" type=\"" ^ mime ^ "\">\
  Your browser does not support the video tag.\
  </video>"

let html_audio url mime =
  "<audio controls>\
  <source src=\"" ^ url ^ "\" type=\"" ^ mime ^ "\">\
  Your browser does not support this audio format.\
  </audio>"

let html_cell t =
  match t with
    | URI uri ->
      if uri_has_ext uri ["jpg"; "JPG"; "jpeg"; "JPEG"; "png"; "PNG"; "gif"; "GIF"] then
	html_a uri (html_img uri)
      else if uri_has_ext uri ["mp4"; "MP4"] then
	html_video uri "video/mp4"
      else if uri_has_ext uri ["ogg"; "OGG"] then
	html_video uri "video/ogg"
      else if uri_has_ext uri ["mp3"; "MP3"] then
	html_audio uri "audio/mpeg"
      else html_term ~link:true t
    | _ -> html_term ~link:true t

let html_table_of_results ~focus_var results =
  let buf = Buffer.create 1000 in
  Buffer.add_string buf "<table id=\"extension\"><tr>";
  List.iter
    (fun (var,i) ->
      Buffer.add_string buf
	(if var = focus_var
	 then "<th class=\"in-current-focus\">"
	 else "<th>");
      Buffer.add_string buf var;
      Buffer.add_string buf "</th>")
    results.vars;
  Buffer.add_string buf "</tr>";
  let li = List.map snd results.vars in
  List.iter
    (fun binding ->
      Buffer.add_string buf "<tr>";
      List.iter
	(fun i ->
	  Buffer.add_string buf "<td>";
	  ( match binding.(i) with
	    | None -> ()
	    | Some t -> Buffer.add_string buf (html_cell t) );
	  Buffer.add_string buf "</td>")
	li;
      Buffer.add_string buf "</tr>")
    results.bindings;
  Buffer.add_string buf "</table>";
  Buffer.contents buf

(* ------------------ *)

let alert msg = Dom_html.window##alert(string msg)

let jquery_from (root : #Dom_html.nodeSelector Js.t) s k =
  Opt.iter (root##querySelector(string s)) (fun elt ->
    k elt)
let jquery s k = jquery_from Dom_html.document s k

let jquery_input_from (root : #Dom_html.nodeSelector Js.t) s k =
  Opt.iter (root##querySelector(string s)) (fun elt ->
    Opt.iter (Dom_html.CoerceTo.input elt) (fun input ->
      k input))
let jquery_input s k = jquery_input_from Dom_html.document s k

let jquery_select_from (root : #Dom_html.nodeSelector Js.t) s k =
  Opt.iter (root##querySelector(string s)) (fun elt ->
    Opt.iter (Dom_html.CoerceTo.select elt) (fun select ->
      k select))
let jquery_select s k = jquery_select_from Dom_html.document s k

let jquery_all_from (root : #Dom_html.nodeSelector Js.t) s k =
  let nodelist = root##querySelectorAll(string s) in
  let n = nodelist##length in
  for i=0 to n-1 do
    Opt.iter nodelist##item(i) k
  done
let jquery_all s k = jquery_all_from Dom_html.document s k

let jquery_set_innerHTML sel html =
  jquery sel (fun elt -> elt##innerHTML <- string html)

let onclick k elt =
  elt##onclick <- Dom.handler (fun ev -> k elt ev; bool true)

let ondblclick k elt =
  elt##ondblclick <- Dom.handler (fun ev -> k elt ev; bool true)

let oninput k elt =
  elt##oninput <- Dom.handler (fun ev -> k elt ev; bool true)

let onchange k elt =
  elt##onchange <- Dom.handler (fun ev -> k elt ev; bool true)

class ajax_pool =
object
  val mutable l : xmlHttpRequest t list = []
  method add req = l <- req::l
  method remove req = l <- List.filter ((!=) req) l
  method abort_all =
    List.iter
      (fun req ->
	req##onreadystatechange <- (Js.wrap_callback (fun _ -> ()));
	req##abort())
      l;
    l <- []
end

let ajax_sparql (pool : ajax_pool) (endpoint : string) (sparql : string)
    (k1 : sparql_results -> unit) (k0 : int -> unit) =
  (*Firebug.console##log(string sparql);*)
  let fields : (string * Form.form_elt) list =
    [("query", `String (string sparql))] in
  let req = create () in
  pool#add req;
  req##_open (Js.string "POST", Js.string endpoint, Js._true);
  req##setRequestHeader (Js.string "Content-type", Js.string "application/x-www-form-urlencoded");
(*  req##setRequestHeader (Js.string "Content-type", Js.string "application/sparql-query"); *)
  req##setRequestHeader (Js.string "Accept", Js.string "application/sparql-results+xml");
(*
  let headers s =
    Opt.case
      (req##getResponseHeader (Js.bytestring s))
      (fun () -> None)
      (fun v -> Some (Js.to_string v)) in  
*)
  let do_check_headers () = () in
  req##onreadystatechange <- Js.wrap_callback
    (fun _ ->
       (match req##readyState with
          (* IE doesn't have the same semantics for HEADERS_RECEIVED.
             so we wait til LOADING to check headers. See:
             http://msdn.microsoft.com/en-us/library/ms534361(v=vs.85).aspx *)
        | HEADERS_RECEIVED when not Dom_html.onIE -> do_check_headers ()
        | LOADING when Dom_html.onIE -> do_check_headers ()
        | DONE ->
	  pool#remove req;
	  do_check_headers ();
	  let code = req##status in
	  Firebug.console##log(string ("HTTP code: " ^ string_of_int code));
	  Firebug.console##log(req##statusText);
	  ( match code / 100 with
	    | 2 ->
	     (*Firebug.console##log(req##responseText);*)
	     (*	let results = sparql_results_of_json xhr.content in *)
              let results_opt =
                match Js.Opt.to_option (req##responseXML) with
                  | None -> None
                  | Some doc ->
                    if (Js.some doc##documentElement) == Js.null
                    then None
                    else Some (sparql_results_of_xml doc) in
	      ( match results_opt with
		| None ->
		  Firebug.console##log(string "No XML content");
		  ()
		| Some results -> k1 results )
	    | 0 ->
	      alert "The SPARQL endpoint is not responsive. Check that the URL is correct, and that the server is running.";
	      k0 code
	    | 4 ->
	      alert "The query was not understood by the SPARQL endpoint. Check that the endpoint accepts SPARQL 1.1 queries, and if this is the case, report the error at <ferre@irisa.fr>.";
	      k0 code
	    | 5 ->
	      alert "There was an error at the SPARQL endpoint.";
	      k0 code
	    | _ ->
	      alert ("Error " ^ string_of_int code);
	      k0 code )
        | _ -> ()));
  let encode_fields l =
    String.concat "&"
      (List.map
	 (function
           | name,`String s -> ((Url.urlencode name) ^ "=" ^ (Url.urlencode (to_string s)))
           | name,`File s -> ((Url.urlencode name) ^ "=" ^ (Url.urlencode (to_string (s##name)))))
	 l) in
  req##send(Js.some (string (encode_fields fields)))
(*  req##send(Js.some (string sparql)) *)

let rec ajax_sparql_list pool endpoint sparql_list k1 k0 =
  match sparql_list with
    | [] -> k1 []
    | s::ls ->
      ajax_sparql pool endpoint s
	(fun r ->
	  ajax_sparql_list pool endpoint ls
	    (fun rs -> k1 (r::rs))
	    (fun code -> k0 code))
	(fun code -> k0 code)

let progress (elts : Dom_html.element t list) (main : ('a -> unit) -> ('b -> unit) -> unit) (k1 : 'a -> unit) (k0 : 'b -> unit) : unit =
  List.iter (* setting progress cursor *)
    (fun elt ->
      elt##style##cursor <- string "progress";
      elt##style##opacity <- def (string "0.5"))
    elts;
  main
    (fun x ->
      List.iter (* restoring default cursor *)
	(fun elt ->
	  elt##style##cursor <- string "default";
	  elt##style##opacity <- def (string "1"))
	elts;
      k1 x)
    (fun y ->
      List.iter (* restoring default cursor *)
	(fun elt ->
	  elt##style##cursor <- string "default";
	  elt##style##opacity <- def (string "1"))
	elts;
      k0 y)

let ajax_sparql_in elts pool endpoint sparql k1 k0 =
  progress elts (ajax_sparql pool endpoint sparql) k1 k0
let ajax_sparql_list_in elts pool endpoint sparql_list k1 k0 =
  progress elts (ajax_sparql_list pool endpoint sparql_list) k1 k0

(* -------------------- *)

class ['a] dico (prefix : string) =
object
  val mutable cpt = 0
  val ht : (string,'a) Hashtbl.t = Hashtbl.create 100

  method add (x : 'a) : string =
    cpt <- cpt + 1;
    let key = prefix ^ string_of_int cpt in
    Hashtbl.add ht key x;
    key

  method get (key : string) : 'a =
    try Hashtbl.find ht key
    with _ ->
      Firebug.console##log(string ("Missing element in dico: " ^ key));
      failwith "Osparqlis.dico#get"
end

class dico_foci =
object
  inherit [focus] dico "focus"
end

class dico_increments =
object
  inherit [increment] dico "incr"
  val dico_foci = new dico_foci
  method dico_foci = dico_foci
end

(* navigation place and history *)

class navigation =
object
  method change_endpoint (url : string) : unit = ()
  method update_focus ~(push_in_history : bool) (f : focus -> focus option) : unit = ()
end

class place =
object (self)
  (* constants *)

  val max_results = 200
  val max_classes = 200
  val max_properties = 1000

  (* essential state *)

(*  val endpoint = "http://dbpedia.org/sparql"*)
  val mutable endpoint = "http://localhost:3030/ds/sparql"
  method endpoint = endpoint

  val focus = home_focus
  method focus = focus

  val mutable offset = 0
  val mutable limit = 10

  val mutable term_constr = True
  val mutable class_constr = True
  val mutable property_constr = True

  (* utilities *)

  val ajax_pool = new ajax_pool
  method abort_all_ajax = ajax_pool#abort_all

  val mutable navigation = new navigation
  method set_navigation (navig : navigation) = navigation <- navig

  (* derived state *)

  val mutable focus_term_opt : term option = None
  val mutable query_opt : sparql_template option = None
  val mutable query_class_opt : sparql_template option = None
  val mutable query_prop_has_opt : sparql_template option = None
  val mutable query_prop_isof_opt : sparql_template option = None

  method init =
    begin
      let t_opt, q_opt, qc_opt, qph_opt, qpi_opt = sparql_of_focus focus in
      focus_term_opt <- t_opt;
      query_opt <- q_opt;
      query_class_opt <- qc_opt;
      query_prop_has_opt <- qph_opt;
      query_prop_isof_opt <- qpi_opt
    end

  initializer self#init

  val mutable dico_foci = new dico_foci
  val mutable results = empty_results
  val mutable focus_term_index : (term * int) list = []
  val mutable dico_incrs = new dico_increments

  method private define_focus_term_index = (* requires 'results' to be defined *)
    focus_term_index <-
      ( match focus_term_opt with
	| None -> []
	| Some (Var v) ->
	  List.filter
	    (function
	      | (URI uri, _) when String.contains uri ' ' -> false
	      (* URIs with spaces inside are not allowed in SPARQL queries *)
	      | _ -> true)
	    (index_of_results_column v results)
	| Some t -> [(t, results.length)] )

  method private refresh_lisql =
    jquery "#lisql" (fun elt ->
      elt##innerHTML <- string (html_of_focus dico_foci focus);
      jquery_all_from elt ".focus" (onclick (fun elt_foc ev ->
	Dom_html.stopPropagation ev;
	navigation#update_focus ~push_in_history:false (fun _ ->
	  let key = to_string (elt_foc##id) in
	  Firebug.console##log(string key);
	  Some (dico_foci#get key))));
      jquery_from elt "#delete-current-focus"
	(onclick (fun elt_button ev ->
	  Dom_html.stopPropagation ev;
	  navigation#update_focus ~push_in_history:true delete_focus)))

  method private refresh_constrs =
    List.iter
      (fun (sel_select, sel_input, constr) ->
	jquery_select sel_select (fun select ->
	  jquery_input sel_input (fun input ->
	    select##value <- string (operator_of_constr constr);
	    input##value <- string (pattern_of_constr constr))))
      [("#select-terms", "#pattern-terms", term_constr);
       ("#select-classes", "#pattern-classes", class_constr);
       ("#select-properties", "#pattern-properties", property_constr);
       ("#select-modifiers", "#pattern-modifiers", True)]

  method private refresh_extension =
    jquery "#results" (fun elt_results ->
      if results.dim = 0 then begin
	elt_results##style##display <- string "none" end
      else begin
	elt_results##style##display <- string "block";
	jquery_set_innerHTML "#list-results"
	  (html_table_of_results
	     ~focus_var:(match focus_term_opt with Some (Var v) -> v | _ -> "")
	     (page_of_results offset limit results));
	jquery_all ".count-results" (fun elt ->
	  elt##innerHTML <- string
	    (if results.length = 0
	     then "No results"
	     else
		let a, b = offset+1, min results.length (offset+limit) in
		if a = 1 && b = results.length && results.length < max_results then
		  string_of_int b ^ (if b=1 then " result" else " results")
		else
		  "Results " ^ string_of_int a ^ " - " ^ string_of_int b ^
		    " of " ^ string_of_int results.length ^ (if results.length < max_results then "" else "+")))
      end)

  method private refresh_term_increments =
    jquery "#list-terms" (fun elt ->
      elt##innerHTML <- string
	(html_of_increment_frequency_list focus dico_incrs
	   (List.rev_map (fun (t, freq) -> (IncrTerm t, freq)) focus_term_index));
      jquery_all_from elt ".increment" (onclick (fun elt ev ->
	navigation#update_focus ~push_in_history:true
	  (insert_increment (dico_incrs#get (to_string (elt##id)))))));
    jquery_set_innerHTML "#count-terms"
      (html_count_unit (List.length focus_term_index) max_results "term" "terms")

  method private refresh_class_increments_init =
    let process elt results =
      let class_list = list_of_results_column "class" results in
      elt##innerHTML <- string
	(html_of_increment_frequency_list focus dico_incrs
	   (List.fold_left
	      (fun res -> function
		| URI c -> (IncrClass c, 1) :: res
		| _ -> res)
	      [] class_list));
      jquery_all_from elt ".increment" (onclick (fun elt ev ->
	navigation#update_focus ~push_in_history:true
	  (insert_increment (dico_incrs#get (to_string (elt##id))))));
      jquery_set_innerHTML "#count-classes"
	(html_count_unit (List.length class_list) 1000 "class" "classes")
    in
    jquery "#list-classes" (fun elt ->
      let sparql =
	"PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> \
         SELECT DISTINCT ?class WHERE { { ?class a rdfs:Class } UNION { [] rdfs:domain ?class } UNION { [] rdfs:range ?class } " ^
	  sparql_constr (Var "class") class_constr ^
	  " } LIMIT 1000" in
      ajax_sparql_in [elt] ajax_pool endpoint sparql
	(fun results ->
	  if results.length > 0
	  then process elt results
	  else
	    let sparql = "SELECT DISTINCT ?class WHERE { [] a ?class " ^ sparql_constr (Var "class") class_constr ^ " } LIMIT 200" in
	    ajax_sparql_in [elt] ajax_pool endpoint sparql
	      (fun results -> process elt results)
	      (fun code -> process elt empty_results))
	(fun code -> process elt empty_results))

  method private refresh_property_increments_init =
    let process elt results =
      let prop_list = list_of_results_column "prop" results in
      elt##innerHTML <- string
	(html_of_increment_frequency_list focus dico_incrs
	   (List.fold_left
	      (fun res -> function
		| URI c -> (IncrProp c, 1) :: (IncrInvProp c, 1) :: res
		| _ -> res)
	      [] prop_list));
      jquery_all_from elt ".increment" (onclick (fun elt ev ->
	navigation#update_focus ~push_in_history:true
	  (insert_increment (dico_incrs#get (to_string (elt##id))))));
      jquery_set_innerHTML "#count-properties"
	(html_count_unit (List.length prop_list) 1000 "property" "properties")
    in
    jquery "#list-properties" (fun elt ->
      let sparql =
	"PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> \
         PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> \
         SELECT DISTINCT ?prop WHERE { { ?prop a rdf:Property } UNION { ?prop rdfs:domain [] } UNION { ?prop rdfs:range [] } " ^
	  sparql_constr (Var "prop") property_constr ^
	  " } LIMIT 1000" in
      ajax_sparql_in [elt] ajax_pool endpoint sparql
	(fun results ->
	  if results.length > 0
	  then process elt results
	  else
	    let sparql = "SELECT DISTINCT ?prop WHERE { [] ?prop [] " ^ sparql_constr (Var "prop") property_constr ^ " } LIMIT 200" in
	    ajax_sparql_in [elt] ajax_pool endpoint sparql
	      (fun results -> process elt results)
	      (fun code -> process elt empty_results))
	(fun code -> process elt empty_results))

  method private refresh_class_increments =
    let process elt results =
      let class_index = index_of_results_column "class" results in
      elt##innerHTML <- string
	(html_of_increment_frequency_list focus dico_incrs
	   (List.fold_left
	      (fun res -> function
		| (URI c, freq) -> (IncrClass c, freq) :: res
		| _ -> res)
	      [] class_index));
      jquery_all_from elt ".increment" (onclick (fun elt ev ->
	navigation#update_focus ~push_in_history:true
	  (insert_increment (dico_incrs#get (to_string (elt##id))))));
      jquery_set_innerHTML "#count-classes"
	(html_count_unit (List.length class_index) max_classes "class" "classes")
    in
    jquery "#list-classes" (fun elt ->
(*
	  let sparql =
	    let vals = String.concat " " (List.map (fun (t,_) -> sparql_term t) focus_term_index) in
	    "SELECT DISTINCT ?class (COUNT(DISTINCT ?focus) AS ?freq) WHERE { VALUES ?focus { " ^ vals ^ " } ?focus a ?class } GROUP BY ?class ORDER BY DESC(?freq) ?class LIMIT " ^ string_of_int max_classes in
*)
      let sparql =
	let lgp = List.map (fun (t,_) -> sparql_triple t (URI "a") (Var "class")) focus_term_index in
	sparql_select ~dimensions:["class"] ~limit:max_classes (sparql_join [sparql_union lgp; sparql_constr (Var "class") class_constr]) in
      ajax_sparql_in [elt] ajax_pool endpoint sparql
	(fun results ->
	  if results.length > 0
	  then process elt results
	  else
	    match query_class_opt with
	      | None -> process elt empty_results
	      | Some query ->
		let sparql = query ~constr:class_constr ~limit:max_classes in
		ajax_sparql_in [elt] ajax_pool endpoint sparql
		  (fun results -> process elt results)
		  (fun code -> process elt empty_results))
	(fun code -> process elt empty_results))
      
  method private refresh_property_increments =
    let process elt results_has results_isof =
      let index_has = index_of_results_column "prop" results_has in (* increasing *)
      let index_isof = index_of_results_column "prop" results_isof in (* increasing *)
      let index =
	let rec aux acc l1 l2 =
	  match l1, l2 with
	    | (URI c1, freq1)::r1, (_, freq2)::r2 when freq1 <= freq2 -> aux ((IncrProp c1, freq1)::acc) r1 l2
	    | (_, freq1)::r1, (URI c2, freq2)::r2 when freq1 > freq2 -> aux ((IncrInvProp c2, freq2)::acc) l1 r2
	    | (URI c1, freq1)::r1, [] -> aux ((IncrProp c1, freq1)::acc) r1 []
	    | [], (URI c2, freq2)::r2 -> aux ((IncrInvProp c2, freq2)::acc) [] r2
	    | [], [] -> acc
	    | _ -> acc (* assert false *) in
	aux [] index_has index_isof in
      elt##innerHTML <- string
	(html_of_increment_frequency_list focus dico_incrs
	   index);
      jquery_all_from elt ".increment" (onclick (fun elt ev ->
	navigation#update_focus ~push_in_history:true
	  (insert_increment (dico_incrs#get (to_string (elt##id))))));
      jquery_set_innerHTML "#count-properties"
	(html_count_unit (List.length index_has + List.length index_isof) max_properties "property" "properties")
    in	
    jquery "#list-properties" (fun elt ->
(*
      let vals = String.concat " " (List.map (fun (t,_) -> sparql_term t) focus_term_index) in
      let sparql_has = "SELECT DISTINCT ?prop (COUNT (DISTINCT ?focus) AS ?freq) WHERE { VALUES ?focus { " ^ vals ^ " } ?focus ?prop [] } GROUP BY ?prop ORDER BY DESC(?freq) ?prop LIMIT " ^ string_of_int max_properties in
      let sparql_isof = "SELECT DISTINCT ?prop (COUNT(DISTINCT ?focus) AS ?freq) WHERE { VALUES ?focus { " ^ vals ^ " } [] ?prop ?focus } GROUP BY ?prop ORDER BY DESC(?freq) ?prop LIMIT " ^ string_of_int max_properties in
*)
      let sparql_has =
	let lgp = List.map (fun (t,_) -> sparql_triple t (Var "prop") (Bnode "")) focus_term_index in
	sparql_select ~dimensions:["prop"] ~limit:max_properties (sparql_join [sparql_union lgp; sparql_constr (Var "prop") property_constr]) in
      let sparql_isof =
	let lgp = List.map (fun (t,_) -> sparql_triple (Bnode "") (Var "prop") t) focus_term_index in
	sparql_select ~dimensions:["prop"] ~limit:max_properties (sparql_join [sparql_union lgp; sparql_constr (Var "prop") property_constr]) in
      ajax_sparql_list_in [elt] ajax_pool endpoint [sparql_has; sparql_isof]
	(function
	  | [results_has; results_isof] ->
	    if results_has.length > 0 || results_isof.length > 0
	    then process elt results_has results_isof
	    else
	      ( match query_prop_has_opt, query_prop_isof_opt with
	      | None, None -> process elt empty_results empty_results
	      | Some query_has, Some query_isof ->
		let sparql_has = query_has ~constr:property_constr ~limit:max_properties in
		let sparql_isof = query_isof ~constr:property_constr ~limit:max_properties in
		ajax_sparql_list_in [elt] ajax_pool endpoint [sparql_has; sparql_isof]
		  (function
		    | [results_has; results_isof] -> process elt results_has results_isof
		    | _ -> assert false)
		  (fun code -> process elt empty_results empty_results)
	      | _ -> assert false )
	  | _ -> assert false)
	(fun code -> process elt empty_results empty_results))

  method private refresh_modifier_increments =
    jquery "#list-modifiers" (fun elt ->
      let modif_list = (*focus_modifier_increments focus in*)
	match focus with
	  | AtP1 _ -> [IncrOr; IncrMaybe; IncrNot]
	  | AtS1 (Det (An (modif, head), _), _) ->
	    let modifs =
	      if List.exists (function (Number _, _) -> true | _ -> false) focus_term_index
	      then List.map (fun g -> IncrModifS2 (Aggreg (None,g))) [Total; Average; Maximum; Minimum]
	      else [] in
	    let modifs =
	      if List.exists (function (Number _, _) | (PlainLiteral _, _) | (TypedLiteral _, _) -> true | _ -> false) focus_term_index
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
      elt##innerHTML <- string
	(html_of_increment_frequency_list focus dico_incrs
	   (List.map (fun incr -> (incr,1)) modif_list));
      jquery_all_from elt ".increment" (onclick (fun elt ev ->
	navigation#update_focus ~push_in_history:true
	  (insert_increment (dico_incrs#get (to_string (elt##id))))));
      jquery_set_innerHTML "#count-modifiers"
	(html_count_unit (List.length modif_list) max_int "modifier" "modifiers"))

  method refresh =
    jquery_input "#sparql-endpoint-input" (fun input -> input##value <- string endpoint);
    self#refresh_constrs;
    dico_foci <- new dico_foci;
    dico_incrs <- new dico_increments;
    self#refresh_lisql;
    ( match focus_term_opt with
      | None -> jquery "#increments" (fun elt -> elt##style##display <- string "none")
      | Some _ -> jquery "#increments" (fun elt -> elt##style##display <- string "block") );
    ( match query_opt with
      | None ->
	jquery_set_innerHTML "#sparql" "";
	jquery "#results" (fun elt -> elt##style##display <- string "none");
	jquery_input "#pattern-terms" (fun input -> input##disabled <- bool true);
	jquery_all ".list-incrs" (fun elt -> elt##innerHTML <- string "");
	jquery_all ".count-incrs" (fun elt -> elt##innerHTML <- string "---");
	( match focus_term_opt with
	  | None -> ()
	  | Some (Var v) ->
	    self#refresh_class_increments_init;
	    self#refresh_property_increments_init
	  | Some term ->
	    focus_term_index <- [(term,1)];
	    self#refresh_term_increments;
	    self#refresh_class_increments;
	    self#refresh_property_increments;
	    self#refresh_modifier_increments )
      | Some query ->
	let sparql = query ~constr:term_constr ~limit:max_results in
	jquery_set_innerHTML "#sparql" (html_pre sparql);
	jquery "#results" (fun elt -> elt##style##display <- string "block");
	jquery_input "#pattern-terms" (fun input -> input##disabled <- bool false);
	jquery "#increments" (fun elt_incrs ->
	  jquery "#results" (fun elt_res ->
	    ajax_sparql_in [elt_incrs; elt_res] ajax_pool endpoint sparql
	      (fun res ->
		results <- res;
		self#refresh_extension;
		( match focus_term_opt with
		  | None -> ()
		  | Some t ->
		    self#define_focus_term_index;
		    self#refresh_term_increments;
		    self#refresh_class_increments;
		    self#refresh_property_increments;
		    self#refresh_modifier_increments ))
	      (fun code ->
		results <- empty_results;
		self#refresh_extension);
	    () )))

  method is_home =
    focus = home_focus

  method set_term_constr constr =
    if not self#is_home
    then begin
      Firebug.console##log(string "set_term_constr!");
      term_constr <- constr;
      self#refresh
    end

  method set_class_constr constr =
    if self#is_home
    then begin
      class_constr <- constr;
      self#refresh_class_increments_init end
    else begin
      class_constr <- constr;
      self#refresh_class_increments
    end

  method set_property_constr constr =
    if self#is_home
    then begin
      property_constr <- constr;
      self#refresh_property_increments_init end
    else begin
      property_constr <- constr;
      self#refresh_property_increments
    end

  method pattern_changed
    ~(select : Dom_html.selectElement t)
    ~(input : Dom_html.inputElement t)
    ~(elt_list : Dom_html.element t)
    (k : constr -> unit)
    =
    let op = to_string (select##value) in
    let pat = to_string (input##value) in
    Firebug.console##log(string pat);
    try
      let constr = make_constr op pat in
      let matcher = compile_constr constr in
      let there_is_match = ref false in
      jquery_all_from elt_list "li" (fun elt_li ->
	jquery_from elt_li ".increment" (fun elt_incr ->
	  let incr = dico_incrs#get (to_string (elt_incr##id)) in
	  let t =
	    match term_of_increment incr with
	      | Some t -> t
	      | None ->
		let s = Opt.case (elt_incr##querySelector(string ".modifier"))
		  (fun () -> to_string (elt_incr##innerHTML))
		  (fun elt -> to_string (elt##innerHTML)) in
		PlainLiteral (s, "") in
	  if matcher t
	  then begin elt_li##style##display <- string "list-item"; there_is_match := true end
	  else elt_li##style##display <- string "none"));
      let n = String.length pat in
      if (not !there_is_match && (pat = "" || pat.[n - 1] = ' ')) || (n >= 2 && pat.[n-1] = ' ' && pat.[n-2] = ' ')
      then begin
	Firebug.console##log(string "pattern: no match, call k");
	k constr
      end
    with Invalid_argument msg -> ()

  method set_limit n =
    limit <- n;
    self#refresh_extension

  method give_more =
    if offset + limit < results.length
    then self#set_limit (limit+10)

  method give_less =
    if limit > 10
    then self#set_limit (limit-10)

  method page_down =
    let offset' = offset + limit in
    if offset' < results.length
    then begin
      offset <- offset';
      self#refresh_extension
    end

  method page_up =
    let offset' = offset - limit in
    if offset' >= 0
    then begin
      offset <- offset';
      self#refresh_extension end
    else begin
      offset <- 0;
      self#refresh_extension
    end

  method new_place endpoint focus =
    let p =
      {< endpoint = endpoint;
	 focus = focus;
	 offset = 0;
	 term_constr = True;
	 class_constr = True;
	 property_constr = True; >} in
    p#init;
    p

end

let history =
object (self)
  val mutable past : place list = []
  val mutable present : place = new place
  val mutable future : place list = []

(*  initializer present#set_update_focus self#update_focus *)
  initializer present#set_navigation (self :> navigation)

  method present : place = present

  method push (p : place) : unit =
    past <- present::past;
    present <- p;
    future <- []

  method change_endpoint url =
    present#abort_all_ajax;
    let p = present#new_place url home_focus in
    p#set_navigation (self :> navigation);
    self#push p;
    p#refresh

  method update_focus ~push_in_history f =
    match f present#focus with
      | None -> ()
      | Some foc ->
	present#abort_all_ajax;
	let p = present#new_place present#endpoint foc in
	p#set_navigation (self :> navigation);
	if push_in_history then self#push p else present <- p;
	p#refresh

  method home =
    self#update_focus ~push_in_history:true
      (fun _ -> Some home_focus)

  method back : unit =
    match past with
      | [] -> ()
      | p::lp ->
	present#abort_all_ajax;
	future <- present::future;
	present <- p;
	past <- lp;
	p#refresh

  method forward : unit =
    match future with
      | [] -> ()
      | p::lp ->
	present#abort_all_ajax;
	past <- present::past;
	present <- p;
	future <- lp;
	p#refresh

end

let _ =
  Firebug.console##log(string "Starting Sparklis");
  Dom_html.window##onload <- Dom.handler (fun ev ->
    jquery "#home" (onclick (fun elt ev -> history#home));
    jquery "#back" (onclick (fun elt ev -> history#back));
    jquery "#forward" (onclick (fun elt ev -> history#forward));
    jquery "#sparql-endpoint-button" (onclick (fun elt ev ->
      jquery_input "#sparql-endpoint-input" (fun input ->
	let url = to_string (input##value) in
	history#change_endpoint url)));

    jquery "#button-terms" (onclick (fun elt ev ->
      jquery_select "#select-terms" (fun select ->
	jquery_input "#pattern-terms" (fun input ->
	  let op = to_string (select##value) in
	  let pat = to_string (input##value) in
	  try
	    let constr = make_constr op pat in
	    if constr = True
	    then
	      Dom_html.window##alert(string "Invalid filter")
	    else
	      history#update_focus ~push_in_history:true
		(insert_elt_p1 (Constr constr))
	  with Invalid_argument msg ->
	    Dom_html.window##alert(string ("Invalid filter: " ^ msg))))));
    List.iter
      (fun (sel_select, sel_input, sel_list, k) ->
	jquery_select sel_select (fun select ->
	  jquery_input sel_input (fun input ->
	    jquery sel_list (fun elt_list ->
	      (oninput
		 (fun input ev -> history#present#pattern_changed ~select ~input ~elt_list k)
		 input)))))
      [("#select-terms", "#pattern-terms", "#list-terms", (fun constr -> history#present#set_term_constr constr));
       ("#select-classes", "#pattern-classes", "#list-classes", (fun constr -> history#present#set_class_constr constr));
       ("#select-properties", "#pattern-properties", "#list-properties", (fun constr -> history#present#set_property_constr constr));
       ("#select-modifiers", "#pattern-modifiers", "#list-modifiers", (fun constr -> ()))];
    
    jquery_all ".previous-results" (onclick (fun elt ev -> history#present#page_up));
    jquery_all ".next-results" (onclick (fun elt ev -> history#present#page_down));
    jquery_all ".limit-results" (fun elt ->
      Opt.iter (Dom_html.CoerceTo.select elt) (onchange (fun select ev ->
	Firebug.console##log(select##value);
	let limit = int_of_string (to_string (select##value)) in
	history#present#set_limit limit)));

    history#present#refresh;
    bool true)
