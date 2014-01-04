
open Js
open XmlHttpRequest

(* ------------------------ *)

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

type uri = string
type var = string

type term =
  | URI of uri
  | PlainLiteral of string * string
  | TypedLiteral of string * uri
  | Bnode of string
  | Var of var

type order = Highest | Lowest
type aggreg = NumberOf | ListOf | Total | Average | Maximum | Minimum
type modif_s2 = Id | Any | Aggreg of aggreg | Order of order

(* LISQL elts *)
type elt_p1 =
  | Type of uri
  | Has of uri * elt_s1
  | IsOf of uri * elt_s1
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

  val mutable focus_term : term = Var ""
  method set_focus_term t = focus_term <- t
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

let sparql_term = function
  | URI uri -> sparql_uri uri
  | PlainLiteral (s,lang) -> "\"" ^ s ^ "\"" ^ (if lang = "" then "" else "@" ^ lang)
  | TypedLiteral (s,dt) -> "\"" ^ s ^ "\"^^" ^ sparql_uri dt
  | Bnode name -> "_:" ^ name
  | Var v -> sparql_var v

let sparql_empty = ""

let sparql_triple s p o = sparql_term s ^ " " ^ sparql_uri p ^ " " ^ sparql_term o ^ " . "

let sparql_pattern t lpat =
  if lpat = []
  then ""
  else
    let lfilter =
      List.map
	(fun pat -> "REGEX(str(" ^ sparql_term t ^ "), \"" ^ pat ^ "\",'i')")
	lpat in
    "FILTER (" ^ String.concat " && " lfilter ^ ")"

let sparql_join lgp =
  String.concat "\n"
    (List.filter ((<>) "") lgp)
let sparql_union lgp =
  String.concat " UNION "
    (List.map
       (fun gp -> "{ " ^ gp ^ " }")
       (List.filter ((<>) "") lgp))
let sparql_optional gp = "OPTIONAL { " ^ gp ^ " }"
let sparql_not_exists gp = "FILTER NOT EXISTS { " ^ gp ^ " }"

let sparql_ask gp =
  "ASK WHERE {\n" ^ gp ^ "\n}"
let sparql_select ~dimensions ~aggregations ~ordering ?limit gp =
  let sparql_aggreg prefix_g v suffix_g prefix_v = "(" ^ prefix_g ^ sparql_var v ^ suffix_g ^ " AS " ^ sparql_var (prefix_v ^ v) ^ ")" in
  let sel =
    String.concat " " (List.map sparql_var dimensions) ^ " " ^
      String.concat " "
      (List.map
	 (function
	   | `COUNT v -> sparql_aggreg "COUNT(DISTINCT " v ")" "number_of_"
	   | `SUM v -> sparql_aggreg "SUM(" v ")" "total_"
	   | `AVG v -> sparql_aggreg "AVG(" v ")" "average_"
	   | `MAX v -> sparql_aggreg "MAX(" v ")" "maximum_"
	   | `MIN v -> sparql_aggreg "MIN(" v ")" "minimum_"
	   | `GROUP_CONCAT (v,sep) -> sparql_aggreg "GROUP_CONCAT(" v (" ; separator='" ^ sep ^ "')") "list_of_")
	 aggregations) in
  let s = "SELECT DISTINCT " ^ sel ^ " WHERE {\n" ^ gp ^ "\n}" in
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
  | Type c -> (fun x -> sparql_triple x "a" (URI c))
  | Has (p,np) -> (fun x -> sparql_of_elt_s1 state ~prefix:(prefix_of_uri p) np (fun y -> sparql_triple x p y))
  | IsOf (p,np) -> (fun x -> sparql_of_elt_s1 state ~prefix:"" np (fun y -> sparql_triple y p x))
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
    state#new_var prefix, (fun t -> sparql_triple t "a" (URI c))
(*
  | Aggreg (g, head2, rel2_opt) ->
    let v2, dhead2 = sparql_of_elt_head state ~prefix head2 in
    let v = match g with Count -> "number_of_" ^ v in
    let drel2 = match rel2_opt with None -> (fun t2 -> sparql_empty) | Some rel2 -> sparql_of_elt_p1 state rel2 in
    v, (fun t -> sparql_aggreg g t v2 (fun t2 -> sparql_join [dhead2 t2; drel2 t2]))
*)
(*
and sparql_of_elt_s state : elt_s -> string = function
  | Return np ->
    let gp = sparql_of_elt_s1 state ~prefix:"Result" np (fun t -> "") in
    sparql_select state#vars gp
*)

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
      (fun x -> q (fun y -> sparql_triple x p y))
      ctx
  | IsOfX (p,ctx) ->
    sparql_of_ctx_p1 state ~prefix:(prefix_of_uri p)
      (fun x -> q (fun y -> sparql_triple y p x))
      ctx
  | ReturnX ->
    q (fun t -> "")

let sparql_of_focus ~(lpat : string list) ~(limit : int) (focus : focus) : term * string option =
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
	    state#set_focus_term t;
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
	      state#set_focus_term t;
	      d t))
	  ctx in
  let t = state#focus_term in
  let query_opt =
    if gp = sparql_empty
    then None
    else
      let lv = state#vars in
      let gp = sparql_join [gp; sparql_pattern t lpat] in
      if lv = []
      then Some (sparql_ask gp)
      else
	let dimensions, aggregations, ordering =
	  List.fold_right
	    (fun v (dims,aggregs,ordering) ->
	      match state#modif v with
		| Any when t <> Var v -> dims, aggregs, ordering
		| Aggreg g when t <> Var v ->
		  let aggreg =
		    match g with
		      | NumberOf -> `COUNT v
		      | ListOf -> `GROUP_CONCAT (v, ", ")
		      | Total -> `SUM v
		      | Average -> `AVG v
		      | Maximum -> `MAX v
		      | Minimum -> `MIN v in
		  dims, aggreg::aggregs, ordering
		| Order o ->
		  let order =
		    match o with
		      | Lowest -> `ASC v
		      | Highest -> `DESC v in
		  dims, aggregs, order::ordering
		| _ -> v::dims, aggregs, ordering)
	    lv ([],[],[]) in
	Some (sparql_select ~dimensions ~aggregations ~ordering ~limit gp) in
  t, query_opt

(* pretty-printing of focus as HTML *)

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

let html_term ?(link = false) = function
  | URI uri ->
    (*if uri_is_image uri (* too heavy loading *)
    then
      if link
      then html_a uri (html_img uri)
      else html_img ~height:60 uri
    else*)
      let name = name_of_uri uri in
      if link
      then html_a uri name
      else html_span ~classe:"URI" ~title:uri name
  | PlainLiteral (s,lang) -> html_span ~classe:"Literal" (s ^ (if lang="" then "" else "@" ^ lang))
  | TypedLiteral (s,dt) -> html_span ~classe:"Literal" (s ^ " (" ^ name_of_uri dt ^ ")")
  | Bnode id -> "_:" ^ id
  | Var v -> "?" ^ v
let html_class c =
  html_span ~classe:"classURI" ~title:c (name_of_uri c)
let html_prop p =
  html_span ~classe:"propURI" ~title:p (name_of_uri p)

let html_is_a c = "is a " ^ html_class c
let html_has p np = "has " ^ html_prop p ^ " " ^ np
let html_is_of p np = "is the " ^ html_prop p ^ " of " ^ np

let html_and ar_html =
  let html = ref ("<ul class=\"list-and\"><li>" ^ ar_html.(0) ^ "</li>") in
  for i=1 to Array.length ar_html - 1 do
    html := !html ^ " <li>and " ^ ar_html.(i) ^ "</li>"
  done;
  !html ^ "</ul>"
let html_or ar_html =
  let html = ref ("<ul class=\"list-or\"><li>" ^ ar_html.(0) ^ "</li>") in
  for i=1 to Array.length ar_html - 1 do
    html := !html ^ " <li>" ^ html_span ~classe:"modifier" "or" ^ " " ^ ar_html.(i) ^ "</li>"
  done;
  !html ^ "</ul>"
let html_maybe html = html_span ~classe:"modifier" "optionally" ^ " " ^ html
let html_not html = html_span ~classe:"modifier" "not" ^ " " ^ html
let html_is_there = "..."

let html_det det rel_opt = det ^ (match rel_opt with None -> "" | Some rel -> " that " ^ rel)
(*let html_the_of p np = "the " ^ html_prop p ^ " of " ^ np*)
let html_of modif_p np = modif_p ^ " of " ^ np
let html_return np = "Give me " ^ np

let html_focus dico foc hl (* highlight *) html =
  let id = dico#add foc in
  "<span id=\"" ^ id ^ "\" class=\"focus" ^ (if hl then " in-current-focus" else "") ^ "\">" ^ html ^ "</span>"
let html_focus_dummy =
  "<span class=\"in-current-focus\">___</span>"

let rec html_of_elt_p1 dico ctx hl f =
  let html =
    match f with
      | Type c -> html_is_a c
      | Has (p,np) -> html_has p (html_of_elt_s1 dico (HasX (p,ctx)) hl np)
      | IsOf (p,np) -> html_is_of p (html_of_elt_s1 dico (IsOfX (p,ctx)) hl np) 
      | And ar -> html_and (Array.mapi (fun i elt -> html_of_elt_p1 dico (AndX (i,ar,ctx)) hl elt) ar)
      | Or ar -> html_or (Array.mapi (fun i elt -> html_of_elt_p1 dico (OrX (i,ar,ctx)) hl elt) ar)
      | Maybe elt -> html_maybe (html_of_elt_p1 dico (MaybeX ctx) hl elt)
      | Not elt -> html_not (html_of_elt_p1 dico (NotX ctx) hl elt)
      | IsThere -> html_is_there
  in
  html_focus dico (AtP1 (f,ctx)) hl html
and html_of_elt_s1 dico ctx hl f =
  let html =
    match f with
      | Det (det, None) -> html_det (html_of_elt_s2 det) None
      | Det (An (modif, Thing), Some (IsOf (p,np))) ->
	html_of
	  (html_of_modif_s2_noun modif (html_prop p))
	  (html_of_elt_s1 dico (IsOfX (p, DetThatX (An (modif, Thing), ctx))) hl np)
      | Det (det, Some rel) ->
	html_det
	  (html_of_elt_s2 det)
	  (Some (html_of_elt_p1 dico (DetThatX (det,ctx)) hl rel)) in
  html_focus dico (AtS1 (f,ctx)) hl html
and html_of_elt_s2 = function
  | Term t -> html_term t
  | An (Id, Thing) -> "something"
  | An (modif, head) -> html_of_modif_s2_noun modif (match head with Thing -> "thing" | Class c -> html_class c)
and html_of_modif_s2_noun modif noun =
  match modif with
    | Id -> "a " ^ noun
(* (if noun <> "" && List.mem noun.[0] ['a';'e';'i';'o';'u';'A';'E';'I';'O';'U'] then "an " else "a ") ^ noun *)
    | Any -> html_span ~classe:"modifier" "any" ^ " " ^ noun
    | Aggreg NumberOf -> "a " ^ html_span ~classe:"modifier" "number" ^ " of " ^ noun
    | Aggreg ListOf -> "a " ^ html_span ~classe:"modifier" "list" ^ " of " ^ noun
    | Aggreg Total -> "a " ^ html_span ~classe:"modifier" "total" ^ " " ^ noun
    | Aggreg Average -> "an " ^ html_span ~classe:"modifier" "average" ^ " " ^ noun
    | Aggreg Maximum -> "a " ^ html_span ~classe:"modifier" "maximum" ^ " " ^ noun
    | Aggreg Minimum -> "a " ^ html_span ~classe:"modifier" "minimum" ^ " " ^ noun
    | Order Highest -> "the " ^ html_span ~classe:"modifier" "highest" ^ " " ^ noun
    | Order Lowest -> "the " ^ html_span ~classe:"modifier" "lowest" ^ " " ^ noun

let rec html_of_ctx_p1 dico f html ctx =
  match ctx with
    | DetThatX (det,ctx2) ->
      let f2 = Det (det, Some f) in
      let html2 =
	html_focus dico (AtS1 (f2, ctx2)) false
	  (html_det (html_of_elt_s2 det) (Some html)) in
      html_of_ctx_s1 dico f2 html2 ctx2
    | AndX (i,ar,ctx2) ->
      let f2 = ar.(i) <- f; And ar in
      let html2 =
	html_focus dico (AtP1 (f2,ctx2)) false
	  (html_and
	     (Array.mapi
		(fun j elt -> if j=i then html else html_of_elt_p1 dico (AndX (j,ar,ctx2)) false elt)
		ar)) in
      html_of_ctx_p1 dico f2 html2 ctx2
    | OrX (i,ar,ctx2) ->
      let f2 = ar.(i) <- f; Or ar in
      let html2 =
	html_focus dico (AtP1 (f2,ctx2)) false
	  (html_or
	     (Array.mapi
		(fun j elt -> if j=i then html else html_of_elt_p1 dico (OrX (j,ar,ctx2)) false elt)
		ar)) in
      html_of_ctx_p1 dico f2 html2 ctx2
    | MaybeX ctx2 ->
      let f2 = Maybe f in
      let html2 = html_focus dico (AtP1 (f2,ctx2)) false (html_maybe html) in
      html_of_ctx_p1 dico f2 html2 ctx2
    | NotX ctx2 ->
      let f2 = Not f in
      let html2 = html_focus dico (AtP1 (f2,ctx2)) false (html_not html) in
      html_of_ctx_p1 dico f2 html2 ctx2
and html_of_ctx_s1 dico f html ctx =
  match ctx with
    | HasX (p,ctx2) ->
      let f2 = Has (p,f) in
      let html2 =
	html_focus dico (AtP1 (f2,ctx2)) false
	  (html_has p html) in
      html_of_ctx_p1 dico f2 html2 ctx2
    | IsOfX (p, DetThatX (An (modif, Thing), ctx2)) ->
      let f2 = Det (An (modif, Thing), Some (IsOf (p,f))) in
      let html2 =
	html_focus dico (AtS1 (f2,ctx2)) false
	  (html_of
	     (html_of_modif_s2_noun modif (html_prop p))
	     html) in
      html_of_ctx_s1 dico f2 html2 ctx2
    | IsOfX (p,ctx2) ->
      let f2 = IsOf (p,f) in
      let html2 =
	html_focus dico (AtP1 (f2,ctx2)) false
	  (html_is_of p html) in
      html_of_ctx_p1 dico f2 html2 ctx2
    | ReturnX -> html_return html

let html_current_focus html =
  html_span ~id:"current-focus" ~classe:"in-current-focus"
      (html ^ " <img src=\"icon-delete.png\" height=\"16\" alt=\"Delete\" id=\"delete-current-focus\" title=\"Click on this red cross to delete the current focus\">")

let html_of_focus dico focus =
  match focus with
    | AtP1 (IsOf (p,np), DetThatX (An (modif, Thing), ctx))
    | AtS1 (Det (An (modif, Thing), Some (IsOf (p,np))), ctx) ->
      let f = Det (An (modif, Thing), Some (IsOf (p,np))) in
      html_of_ctx_s1 dico f
	(html_current_focus
	   (html_focus dico (AtS1 (f,ctx)) true
	      (html_of
		 (html_of_modif_s2_noun modif (html_prop p))
		 (html_of_elt_s1 dico (IsOfX (p, DetThatX (An (modif, Thing), ctx))) true np))))
	ctx
    | AtP1 (f,ctx) ->
      html_of_ctx_p1 dico f
	(html_current_focus
	   (html_of_elt_p1 dico ctx true f))
	ctx
    | AtS1 (f,ctx) ->
      html_of_ctx_s1 dico f
	(html_current_focus
	   (html_of_elt_s1 dico ctx true f))
	ctx

(* focus moves *)

let home_focus = AtS1 (top_s1, ReturnX)

let down_p1 (ctx : ctx_p1) : elt_p1 -> focus option = function
  | Type _ -> None
  | Has (p,np) -> Some (AtS1 (np, HasX (p,ctx)))
  | IsOf (p,np) -> Some (AtS1 (np, IsOfX (p,ctx)))
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
let down_focus = function
  | AtP1 (f,ctx) -> down_p1 ctx f
  | AtS1 (f,ctx) -> down_s1 ctx f

let rec up_p1 f = function
  | DetThatX (det,ctx) -> Some (AtS1 (Det (det, Some f), ctx))
  | AndX (i,ar,ctx) -> ar.(i) <- f; up_p1 (And ar) ctx (* Some (AtP1 (And ar, ctx)) *)
  | OrX (i,ar,ctx) -> ar.(i) <- f; Some (AtP1 (Or ar, ctx))
  | MaybeX ctx -> Some (AtP1 (Maybe f, ctx))
  | NotX ctx -> Some (AtP1 (Not f, ctx))
let up_s1 f = function
  | HasX (p, DetThatX (An (modif, Thing), ctx)) -> Some (AtS1 (Det (An (modif, Thing), Some (Has (p,f))), ctx))
  | IsOfX (p, DetThatX (An (modif, Thing), ctx)) -> Some (AtS1 (Det (An (modif, Thing), Some (IsOf (p,f))), ctx))
  | HasX (p,ctx) -> Some (AtP1 (Has (p,f), ctx))
  | IsOfX (p,ctx) -> Some (AtP1 (IsOf (p,f), ctx))
  | ReturnX -> None
let up_focus = function
  | AtP1 (f,ctx) -> up_p1 f ctx
  | AtS1 (f,ctx) -> up_s1 f ctx

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
  | AtS1 _ -> None

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
    Some (AtS1 (Det (An (modif2, head), rel_opt), ctx))
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

let delete_focus = function
  | AtP1 (_,ctx) -> delete_ctx_p1 ctx
  | AtS1 (Det _, ctx) -> Some (AtS1 (top_s1, ctx))


(* HTML of increment lists *)

let html_of_increment_frequency dico_incrs (incr,freq) =
  let key = dico_incrs#add incr in
  let text =
    match incr with
      | IncrTerm t -> html_term t
      | IncrClass c -> "a " ^ html_class c
      | IncrProp p -> "has " ^ html_prop p
      | IncrInvProp p -> "is the " ^ html_prop p ^ " of"
      | IncrOr -> html_or [|html_focus_dummy; html_is_there|]
      | IncrMaybe -> html_maybe html_focus_dummy
      | IncrNot -> html_not html_focus_dummy
      | IncrModifS2 modif -> html_of_modif_s2_noun modif html_focus_dummy
  in
  let text_freq =
    if freq = 1
    then ""
    else " [" ^ string_of_int freq ^ "]" in
  "<span class=\"increment\" id=\"" ^ key ^ "\">" ^ text ^ text_freq ^ "</span>"

let html_of_increment_frequency_list dico_incrs lif =
  let buf = Buffer.create 1000 in
  Buffer.add_string buf "<ul>";
  List.iter
    (fun incr_freq ->
      Buffer.add_string buf "<li>";
      Buffer.add_string buf (html_of_increment_frequency dico_incrs incr_freq);
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
    let i_count = List.assoc var_count results.vars in
    let index =
      List.fold_left
	(fun res binding ->
	  match binding.(i_x) with
	    | None -> res
	    | Some x ->
	      let count =
		match binding.(i_count) with
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
				(fun dt -> Some (TypedLiteral (s, to_string dt))))
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
		    TypedLiteral (to_string v, to_string (decodeURI (Unsafe.get odatatype (string "fullBytes"))))
		  | "plain-literal" ->
		    let olang = Unsafe.get ocell (string "xml:lang") in
		    PlainLiteral (to_string v, to_string (Unsafe.get olang (string "fullBytes")))
		  | "literal" ->
		    ( try
			let odatatype = Unsafe.get ocell (string "datatype") in
			TypedLiteral (to_string v, to_string (decodeURI (Unsafe.get odatatype (string "fullBytes"))))
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

let jquery_from (root : #Dom_html.nodeSelector Js.t) s k =
  Opt.iter (root##querySelector(string s)) (fun elt ->
    k elt)
let jquery s k = jquery_from Dom_html.document s k

let jquery_input_from (root : #Dom_html.nodeSelector Js.t) s k =
  Opt.iter (root##querySelector(string s)) (fun elt ->
    Opt.iter (Dom_html.CoerceTo.input elt) (fun input ->
      k input))
let jquery_input s k = jquery_input_from Dom_html.document s k

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

let direct_ajax_sparql (endpoint : string) (sparql : string) (k : sparql_results -> unit) =
  let fields : (string * Form.form_elt) list =
    [("query", `String (string sparql))] in
  let req = create () in
  req##_open (Js.string "POST", Js.string endpoint, Js._true);
  req##setRequestHeader (Js.string "Content-type", Js.string "application/x-www-form-urlencoded");
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
	  do_check_headers ();
	  let code = req##status in
	  ( match code / 100 with
	    | 2 ->
	     (*Firebug.console##log(string req##responseText);*)
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
		| Some results -> k results )
	    | _ ->
	      Firebug.console##log(string ("SPARQL request unsuccessful: code " ^ string_of_int code)))
        | _ -> ()));
  let encode_fields l =
    String.concat "&"
      (List.map
	 (function
           | name,`String s -> ((Url.urlencode name) ^ "=" ^ (Url.urlencode (to_string s)))
           | name,`File s -> ((Url.urlencode name) ^ "=" ^ (Url.urlencode (to_string (s##name)))))
	 l) in
  req##send(Js.some (string (encode_fields fields)))

let lwt_ajax_sparql (endpoint : string) (sparql : string) (k : sparql_results -> unit) =
  (*Firebug.console##log(string sparql);*)
  Lwt.ignore_result
    (Lwt.bind
       (perform_raw_url
(*	  ~headers:[("Accept","application/json")] (* OK on Virtuoso, KO on Fuseki *) *)
	  ~headers:[("Accept","application/sparql-results+xml")] (* OK on Virtuoso *)
(*	  ~get_args:[("query", sparql)] (* OK on Fuseki *) *)
	  ~post_args:[("query", sparql)] (* OK on Virtuoso, KO on Fuseki *)
	  endpoint)
       (fun xhr ->
	 Firebug.console##log(string (string_of_int xhr.code));
	 ( match xhr.code / 100 with
	   | 2 ->
	     (*Firebug.console##log(string xhr.content);*)
	     (*	let results = sparql_results_of_json xhr.content in *)
	     let results =
	       match xhr.content_xml () with
		 | None ->
		   Firebug.console##log(string "No XML content");
		   empty_results
		 | Some doc -> sparql_results_of_xml doc in
	     k results
	   | _ ->
	     Firebug.console##log(string ("SPARQL request unsuccessful: code " ^ string_of_int xhr.code)));
	 Lwt.return_unit))

let ajax_sparql endpoint sparql k =
  direct_ajax_sparql endpoint sparql k

let rec ajax_sparql_list endpoint sparql_list k =
  match sparql_list with
    | [] -> k []
    | s::ls ->
      ajax_sparql endpoint s (fun r ->
	ajax_sparql_list endpoint ls (fun rs ->
	  k (r::rs)))

let progress (elts : Dom_html.element t list) (main : ('a -> unit) -> unit) (k : 'a -> unit) : unit =
  List.iter (* setting progress cursor *)
    (fun elt -> elt##style##cursor <- string "progress")
    elts;
  main (fun x ->
    k x;
    List.iter (* restoring default cursor *)
      (fun elt -> elt##style##cursor <- string "default")
      elts)

let ajax_sparql_in elts endpoint sparql k =
  progress elts (ajax_sparql endpoint sparql) k
let ajax_sparql_list_in elts endpoint sparql_list k =
  progress elts (ajax_sparql_list endpoint sparql_list) k

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
  val max_classes = 1000
  val max_properties = 1000

  (* essential state *)

(*  val mutable endpoint = "http://dbpedia.org/sparql"*)
  val mutable endpoint = "http://localhost:3030/ds/sparql"
  method endpoint = endpoint

  val mutable focus = home_focus
  method focus = focus

  val mutable navigation = new navigation
  method set_navigation (navig : navigation) = navigation <- navig

  val mutable offset = 0
  val mutable limit = 10

  val mutable term_patterns = []
  val mutable class_patterns = []
  val mutable property_patterns = []

  (* derived state *)

  val mutable dico_foci = new dico_foci

  val mutable focus_term = Var "thing"
  val mutable sparql_opt = None
  method private define_sparql =
    let t, s_opt = sparql_of_focus ~lpat:term_patterns ~limit:max_results focus in
    focus_term <- t;
    sparql_opt <- s_opt

  val mutable results = empty_results
  val mutable focus_term_index : (term * int) list = []
  val mutable dico_incrs = new dico_increments

  method private define_focus_term_index =
    focus_term_index <-
      ( match focus_term with
	| Var v ->
	  List.filter
	    (function
	      | (URI uri, _) when String.contains uri ' ' -> false
		(* URIs with spaces inside are not allowed in SPARQL queries *)
	      | _ -> true)
	    (index_of_results_column v results)
	| t -> [(t, results.length)] )

  method refresh_lisql =
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

  method private refresh_extension =
    jquery "#results" (fun elt_results ->
      if results.dim = 0 then begin
	elt_results##style##display <- string "none" end
      else begin
	elt_results##style##display <- string "block";
	jquery_set_innerHTML "#list-results"
	  (html_table_of_results
	     ~focus_var:(match focus_term with Var v -> v | _ -> "")
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
	(html_of_increment_frequency_list dico_incrs
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
	(html_of_increment_frequency_list dico_incrs
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
(*      let sparql = "SELECT DISTINCT ?class (COUNT(DISTINCT ?focus) AS ?freq) WHERE { ?focus a ?class } LIMIT 100" in *)
      let sparql =
	"PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> \
         SELECT DISTINCT ?class WHERE { { [] rdfs:domain ?class } UNION { [] rdfs:range ?class } UNION { ?class a rdfs:Class } " ^
	  sparql_pattern (Var "class") class_patterns ^
	  " } LIMIT 1000" in
      ajax_sparql_in [elt] endpoint sparql (fun results ->
	if results.length > 0
	then process elt results
	else
(*	  let sparql = "SELECT DISTINCT ?class WHERE { ?x a ?class } GROUP BY ?class ORDER BY DESC(COUNT(DISTINCT ?x)) LIMIT 1000" in *)
	  let sparql = "SELECT DISTINCT ?class WHERE { [] a ?class } LIMIT 1000" in
	  ajax_sparql_in [elt] endpoint sparql (fun results ->
	    process elt results)))

  method private refresh_property_increments_init =
    let process elt results =
      let prop_list = list_of_results_column "prop" results in
      elt##innerHTML <- string
	(html_of_increment_frequency_list dico_incrs
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
(*      let sparql = "SELECT DISTINCT ?prop WHERE { { ?prop rdfs:domain [] } UNION { ?prop rdfs:range [] } " ^ sparql_pattern (Var "prop") property_patterns ^ " } LIMIT 1000" in *)
      let sparql =
	"PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> \
         PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> \
         SELECT DISTINCT ?prop WHERE { { ?prop rdfs:domain [] } UNION { ?prop rdfs:range [] } UNION { ?prop a rdf:Property } " ^
	  sparql_pattern (Var "prop") property_patterns ^
	  " } LIMIT 1000" in
      ajax_sparql_in [elt] endpoint sparql (fun results ->
	if results.length > 0
	then process elt results
	else
	  let sparql = "SELECT DISTINCT ?prop WHERE { [] ?prop [] } LIMIT 1000" in
	  ajax_sparql_in [elt] endpoint sparql (fun results ->
	    process elt results)))

  method private refresh_class_increments =
    jquery "#list-classes" (fun elt ->
      let vals = String.concat " " (List.map (fun (t,_) -> sparql_term t) focus_term_index) in
      let sparql = "SELECT DISTINCT ?class (COUNT(DISTINCT ?focus) AS ?freq) WHERE { VALUES ?focus { " ^ vals ^ " } ?focus a ?class } GROUP BY ?class ORDER BY DESC(?freq) ?class LIMIT " ^ string_of_int max_classes in
      ajax_sparql_in [elt] endpoint sparql (fun results ->
	let class_index = index_of_results_2columns "class" "freq" results in
	elt##innerHTML <- string
	  (html_of_increment_frequency_list dico_incrs
	     (List.fold_left
		(fun res -> function
		  | (URI c, freq) -> (IncrClass c, freq) :: res
		  | _ -> res)
		[] class_index));
	jquery_all_from elt ".increment" (onclick (fun elt ev ->
	  navigation#update_focus ~push_in_history:true
	    (insert_increment (dico_incrs#get (to_string (elt##id))))));
	jquery_set_innerHTML "#count-classes"
	  (html_count_unit (List.length class_index) max_classes "class" "classes")))
 
  method private refresh_property_increments =
    jquery "#list-properties" (fun elt ->
      let vals = String.concat " " (List.map (fun (t,_) -> sparql_term t) focus_term_index) in
      let sparql_has = "SELECT DISTINCT ?prop (COUNT (DISTINCT ?focus) AS ?freq) WHERE { VALUES ?focus { " ^ vals ^ " } ?focus ?prop [] } GROUP BY ?prop ORDER BY DESC(?freq) ?prop LIMIT " ^ string_of_int max_properties in
      let sparql_isof = "SELECT DISTINCT ?prop (COUNT(DISTINCT ?focus) AS ?freq) WHERE { VALUES ?focus { " ^ vals ^ " } [] ?prop ?focus } GROUP BY ?prop ORDER BY DESC(?freq) ?prop LIMIT " ^ string_of_int max_properties in
      ajax_sparql_list_in [elt] endpoint [sparql_has; sparql_isof] (function
	| [results_has; results_isof] -> (* decreasing *)
	  let index_has = index_of_results_2columns "prop" "freq" results_has in (* increasing *)
	  let index_isof = index_of_results_2columns "prop" "freq" results_isof in (* increasing *)
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
	    (html_of_increment_frequency_list dico_incrs
	       index);
	  jquery_all_from elt ".increment" (onclick (fun elt ev ->
	    navigation#update_focus ~push_in_history:true
	      (insert_increment (dico_incrs#get (to_string (elt##id))))));
	  jquery_set_innerHTML "#count-properties"
	    (html_count_unit (List.length index_has + List.length index_isof) max_properties "property" "properties")
	| _ -> assert false))

  method private refresh_modifier_increments =
    jquery "#list-modifiers" (fun elt ->
      let modif_list = (*focus_modifier_increments focus in*)
	match focus with
	  | AtP1 _ -> [IncrOr; IncrMaybe; IncrNot]
	  | AtS1 (Det (An _, _), _) ->
	    let modifs =
	      if List.exists (function
		| (TypedLiteral (s,_), _) -> (try ignore (float_of_string s); true with _ -> false)
		| _ -> false)
		focus_term_index
	      then List.map (fun g -> IncrModifS2 (Aggreg g)) [Total; Average; Maximum; Minimum]
	      else [] in
	    let modifs =
	      if List.exists (function (PlainLiteral _, _) | (TypedLiteral _, _) -> true | _ -> false) focus_term_index
	      then IncrModifS2 (Aggreg ListOf) :: modifs
	      else modifs in
	    IncrModifS2 (Order Highest) :: IncrModifS2 (Order Lowest) ::
	      IncrModifS2 Any :: IncrModifS2 (Aggreg NumberOf) ::
	      modifs
	  | _ -> [] in
      elt##innerHTML <- string
	(html_of_increment_frequency_list dico_incrs
	   (List.map (fun incr -> (incr,1)) modif_list));
      jquery_all_from elt ".increment" (onclick (fun elt ev ->
	navigation#update_focus ~push_in_history:true
	  (insert_increment (dico_incrs#get (to_string (elt##id))))));
      jquery_set_innerHTML "#count-modifiers"
	(html_count_unit (List.length modif_list) max_int "modifier" "modifiers"))

  method refresh =
    jquery_input "#sparql-endpoint-input" (fun input -> input##value <- string endpoint);
    jquery_input "#pattern-terms" (fun input -> input##value <- string (String.concat " " term_patterns));
    jquery_input "#pattern-classes" (fun input -> input##value <- string (String.concat " " class_patterns));
    jquery_input "#pattern-properties" (fun input -> input##value <- string (String.concat " " property_patterns));
    dico_foci <- new dico_foci;
    self#refresh_lisql;
    self#define_sparql;
    dico_incrs <- new dico_increments;
    match sparql_opt with
      | None ->
	jquery_set_innerHTML "#sparql" "";
	jquery_input "#pattern-terms" (fun input -> input##disabled <- bool true);
	( match focus_term with
	  | Var v ->
	    jquery "#results" (fun elt -> elt##style##display <- string "none");
	    jquery_set_innerHTML "#list-results" "";
	    jquery_set_innerHTML "#count-results" "";
	    jquery_set_innerHTML "#list-terms" "";
	    jquery_set_innerHTML "#count-terms" "---";
	    jquery_set_innerHTML "#list-modifiers" "";
	    jquery_set_innerHTML "#count-modifiers" "---";
	    self#refresh_class_increments_init;
	    self#refresh_property_increments_init;
	  | term ->
	    results <- { dim=1; vars=[("thing",0)]; length=1; bindings=[ [| Some term |] ]; };
	    self#refresh_extension;
	    focus_term_index <- [(term,1)];
	    self#refresh_term_increments;
	    self#refresh_class_increments;
	    self#refresh_property_increments;
	    self#refresh_modifier_increments )
      | Some sparql ->
	jquery_set_innerHTML "#sparql" (html_pre sparql);
	jquery_input "#pattern-terms" (fun input -> input##disabled <- bool false);
	ajax_sparql_in [Dom_html.document##documentElement] endpoint sparql (fun res ->
	  results <- res;
	  self#refresh_extension;
	  self#define_focus_term_index;
	  self#refresh_term_increments;
	  self#refresh_class_increments;
	  self#refresh_property_increments;
	  self#refresh_modifier_increments);
	()

  method is_home =
    focus = home_focus

  method set_term_patterns lpat =
    if not self#is_home
    then begin
      term_patterns <- lpat;
      self#refresh
    end

  method set_class_patterns lpat =
    if self#is_home
    then begin
      class_patterns <- lpat;
      self#refresh_class_increments_init
    end

  method set_property_patterns lpat =
    if self#is_home
    then begin
      property_patterns <- lpat;
      self#refresh_property_increments_init
    end

  method pattern_changed ~(input : Dom_html.inputElement t) ~(elt_list : Dom_html.element t) (k : string list -> unit) =
    let pat = to_string (input##value) in
    Firebug.console##log(string pat);
    let lpat = List.filter ((<>) "") (Regexp.split (Regexp.regexp "[ ]+") pat) in
    let lre = List.map (fun pat -> Regexp.regexp_with_flag (Regexp.quote pat) "i") lpat in
    let matcher s = List.for_all (fun re -> Regexp.search re s 0 <> None) lre in
    let there_is_match = ref false in
    jquery_all_from elt_list "li" (fun elt_li ->
      jquery_from elt_li ".URI, .Literal, .classURI, .propURI, .modifier" (fun elt_incr ->
	if matcher (to_string elt_incr##innerHTML)
	then begin elt_li##style##display <- string "list-item"; there_is_match := true end
	else elt_li##style##display <- string "none"));
    let n = String.length pat in
    if (not !there_is_match && (pat = "" || pat.[n - 1] = ' ')) || (n >= 3 && pat.[n-1] = ' ' && pat.[n-2] = ' ')
    then k lpat

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
    {< endpoint = endpoint;
       focus = focus;
       offset = 0;
       term_patterns = [];
       class_patterns = [];
       property_patterns = []; >}

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
    let p = present#new_place url home_focus in
    p#set_navigation (self :> navigation);
    self#push p;
    p#refresh

  method update_focus ~push_in_history f =
    match f present#focus with
      | None -> ()
      | Some foc -> 
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
	future <- present::future;
	present <- p;
	past <- lp;
	p#refresh

  method forward : unit =
    match future with
      | [] -> ()
      | p::lp ->
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

    List.iter
      (fun (sel_input, sel_list, k) ->
	jquery_input sel_input (fun input ->
	  jquery sel_list (fun elt_list ->
	    (oninput
	       (fun input ev -> history#present#pattern_changed ~input ~elt_list k)
	       input))))
      [("#pattern-terms", "#list-terms", (fun lpat -> history#present#set_term_patterns lpat));
       ("#pattern-classes", "#list-classes", (fun lpat -> history#present#set_class_patterns lpat));
       ("#pattern-properties", "#list-properties", (fun lpat -> history#present#set_property_patterns lpat));
       ("#pattern-modifiers", "#list-modifiers", (fun lpat -> ()))];
    
    jquery_all ".previous-results" (onclick (fun elt ev -> history#present#page_up));
    jquery_all ".next-results" (onclick (fun elt ev -> history#present#page_down));
    jquery_all ".limit-results" (fun elt ->
      Opt.iter (Dom_html.CoerceTo.select elt) (onchange (fun select ev ->
	Firebug.console##log(select##value);
	let limit = int_of_string (to_string (select##value)) in
	history#present#set_limit limit)));

    history#present#refresh;
    bool true)
