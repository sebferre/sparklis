
open Js
open XmlHttpRequest

(* ------------------------ *)

(* SPARQL variable generator *)
let genvar =
object
  val mutable prefix_cpt = []
  val mutable vars = []
  method reset =
    prefix_cpt <- [];
    vars <- []
  method get prefix =
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
end

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

(* ------------------------- *)

type uri = string
type var = string

type term =
  | URI of uri
  | PlainLiteral of string * string
  | TypedLiteral of string * uri
  | Bnode of string
  | Var of var

(* LISQL elts *)
type elt_p1 =
  | Type of uri
  | Has of uri * elt_s1
  | IsOf of uri * elt_s1
  | And of elt_p1 array
and elt_s1 =
  | Det of elt_s2 * elt_p1 option
and elt_s2 =
  | Term of term
  | Something
  | Class of uri
and elt_s =
  | Return of elt_s1

(* LISQL contexts *)
type ctx_p1 =
  | DetThatX of elt_s2 * ctx_s1
  | AndX of int * elt_p1 array * ctx_p1
and ctx_s1 =
  | HasX of uri * ctx_p1
  | IsOfX of uri * ctx_p1
  | ReturnX

(* LISQL focus *)
type focus =
  | AtP1 of elt_p1 * ctx_p1
  | AtS1 of elt_s1 * ctx_s1

(* extraction of LISQL s element from focus *)
let rec elt_s_of_ctx_p1 (f : elt_p1) = function
  | DetThatX (det,ctx) -> elt_s_of_ctx_s1 (Det (det, Some f)) ctx
  | AndX (i,ar,ctx) -> ar.(i) <- f; elt_s_of_ctx_p1 (And ar) ctx
and elt_s_of_ctx_s1 (f : elt_s1) = function
  | HasX (p,ctx) -> elt_s_of_ctx_p1 (Has (p,f)) ctx
  | IsOfX (p,ctx) -> elt_s_of_ctx_p1 (IsOf (p,f)) ctx
  | ReturnX -> Return f

let elt_s_of_focus = function
  | AtP1 (f,ctx) -> elt_s_of_ctx_p1 f ctx
  | AtS1 (f,ctx) -> elt_s_of_ctx_s1 f ctx


(* translation from LISQL elts to SPARQL queries *)

type sparql = string

let sparql_uri uri = 
  if uri = "a" || uri = "bif:contains"
  then uri
  else "<" ^ uri ^ ">"

let sparql_term = function
  | URI uri -> sparql_uri uri
  | PlainLiteral (s,lang) -> "\"" ^ s ^ "\"" ^ (if lang = "" then "" else "@" ^ lang)
  | TypedLiteral (s,dt) -> "\"" ^ s ^ "\"^^" ^ sparql_uri dt
  | Bnode name -> "_:" ^ name
  | Var v -> "?" ^ v

let sparql_triple s p o = sparql_term s ^ " " ^ sparql_uri p ^ " " ^ sparql_term o ^ " . "

let sparql_pattern t pat =
  let lpat = Regexp.split (Regexp.regexp "[ ]+") pat in
  let lfilter =
    List.map
      (fun pat -> "REGEX(str(" ^ sparql_term t ^ "), \"" ^ pat ^ "\",'i')")
      lpat in
  "FILTER (" ^ String.concat " && " lfilter ^ ")"

let sparql_join lgp = String.concat "\n" (List.filter ((<>) "") lgp)

let sparql_select lv gp =
  "SELECT DISTINCT " ^ String.concat " " (List.map (fun v -> "?" ^ v) lv) ^ "\nWHERE {\n" ^ gp ^ "\n}"

let rec sparql_of_elt_p1 : elt_p1 -> (term -> sparql) = function
  | Type c -> (fun x -> sparql_triple x "a" (URI c))
  | Has (p,np) -> (fun x -> sparql_of_elt_s1 ~prefix:(prefix_of_uri p) np (fun y -> sparql_triple x p y))
  | IsOf (p,np) -> (fun x -> sparql_of_elt_s1 ~prefix:"" np (fun y -> sparql_triple y p x))
  | And ar ->
    (fun x ->
      sparql_join
	(Array.to_list
	   (Array.map
	      (fun elt -> sparql_of_elt_p1 elt x)
	      ar)))
and sparql_of_elt_s1 ~prefix : elt_s1 -> ((term -> sparql) -> sparql) = function
  | Det (det,rel_opt) ->
    let d1 = match rel_opt with None -> (fun x -> "") | Some rel -> sparql_of_elt_p1 rel in
    (fun d -> sparql_of_elt_s2 ~prefix det d1 d)
and sparql_of_elt_s2 ~prefix : elt_s2 -> ((term -> sparql) -> (term -> sparql) -> sparql) = function
  | Term t -> (fun d1 d2 -> sparql_join [d1 t; d2 t])
  | Something ->
    let prefix = if prefix = "" then "thing" else prefix in
    (fun d1 d2 -> let t = Var (genvar#get prefix) in sparql_join [d2 t; d1 t])
  | Class c ->
    let prefix = prefix_of_uri c in
    (fun d1 d2 -> let t = Var (genvar#get prefix) in sparql_join [d2 t; sparql_triple t "a" (URI c); d1 t])
and sparql_of_elt_s : elt_s -> sparql = function
  | Return np ->
    let gp = sparql_of_elt_s1 ~prefix:"Result" np (fun t -> "") in
    sparql_select genvar#vars gp

let rec sparql_of_ctx_p1 (d : term -> sparql) : ctx_p1 -> sparql = function
  | DetThatX (det,ctx) ->
    let prefix =
      match ctx with
	| HasX (p,_) -> prefix_of_uri p
	| _ -> "" in
    sparql_of_ctx_s1
      (fun d2 -> sparql_of_elt_s2 ~prefix det d d2) 
      ctx
  | AndX (i,ar,ctx) ->
    sparql_of_ctx_p1
      (fun x ->
	sparql_join
	  (Array.to_list
	     (Array.mapi
		(fun j elt ->
		  if j=i
		  then d x
		  else sparql_of_elt_p1 elt x)
		ar)))
      ctx
and sparql_of_ctx_s1 (q : (term -> sparql) -> sparql) : ctx_s1 -> sparql = function
  | HasX (p,ctx) ->
    sparql_of_ctx_p1
      (fun x -> q (fun y -> sparql_triple x p y))
      ctx
  | IsOfX (p,ctx) ->
    sparql_of_ctx_p1
      (fun x -> q (fun y -> sparql_triple y p x))
      ctx
  | ReturnX ->
    q (fun t -> "")

let sparql_of_focus : focus -> term * (var list * sparql) option = function
  | AtP1 (f,ctx) ->
    let focus = ref (Var "") in
    let gp = sparql_of_ctx_p1
      (fun t ->
	focus := t;
	sparql_of_elt_p1 f t)
      ctx in
    !focus, (if gp = "" then None else Some (genvar#vars, gp))
  | AtS1 (f,ctx) ->
    let prefix =
      match ctx with
	| HasX (p,_) -> prefix_of_uri p
	| _ -> "" in
    let focus = ref (Var "") in
    let gp = sparql_of_ctx_s1 (fun d ->
      sparql_of_elt_s1 ~prefix f
	(fun t ->
	  focus := t;
	  d t))
      ctx in
    !focus, (if gp="" then None else Some (genvar#vars, gp))

(* pretty-printing of focus as HTML *)

let html_pre text =
  let text = Regexp.global_replace (Regexp.regexp "<") text "&lt;" in
  let text = Regexp.global_replace (Regexp.regexp ">") text "&gt;" in  
  "<pre>" ^ text ^ "</pre>"

(* let html_span cl text = "<span class=\"" ^ cl ^ "\">" ^ text ^ "</span>" *)

let html_span ?classe ?title text =
  "<span" ^
    (match classe with None -> "" | Some cl -> " class=\"" ^ cl ^ "\"") ^
    (match title with None -> "" | Some tit -> " title=\"" ^ tit ^ "\"") ^
    ">" ^ text ^ "</span>"

let html_div ?classe ?title text =
  "<div" ^
    (match classe with None -> "" | Some cl -> " class=\"" ^ cl ^ "\"") ^
    (match title with None -> "" | Some tit -> " title=\"" ^ tit ^ "\"") ^
    ">" ^ text ^ "</div>"

let html_term ?(link = false) = function
  | URI uri ->
    let name = name_of_uri uri in
    if link
    then "<a target=\"_blank\" href=\"" ^ uri ^ "\">" ^ name ^ "</a>"
    else html_span ~classe:"URI" ~title:uri name
  | PlainLiteral (s,lang) -> html_span ~classe:"Literal" (s ^ "@" ^ lang)
  | TypedLiteral (s,dt) -> html_span ~classe:"Literal" (s ^ " (" ^ name_of_uri dt ^ ")")
  | Bnode id -> "_:" ^ id
  | Var v -> "?" ^ v
let html_class c =
  html_span ~classe:"classURI" ~title:c (name_of_uri c)
let html_prop p =
  html_span ~classe:"propURI" ~title:p (name_of_uri p)

let html_is_a c = "is a " ^ html_class c
let html_has p np = "has " ^ html_prop p ^ " " ^ np
let html_is_of p np = "is " ^ html_prop p ^ " of " ^ np
let html_and ar =
  let html = ref ("<ul class=\"list-and\"><li>" ^ ar.(0) ^ "</li>") in
  for i=1 to Array.length ar - 1 do
    html := !html ^ " <li> and " ^ ar.(i) ^ "</li>"
  done;
  !html ^ "</ul>"
let html_det det rel_opt = det ^ (match rel_opt with None -> "" | Some rel -> " that " ^ rel)
let html_return np = "Give me " ^ np

let rec html_of_elt_p1 = function
  | Type c -> html_is_a c
  | Has (p,np) -> html_has p (html_of_elt_s1 np)
  | IsOf (p,np) -> html_is_of p (html_of_elt_s1 np) 
  | And ar -> html_and (Array.map html_of_elt_p1 ar)
and html_of_elt_s1 = function
  | Det (det, None) -> html_det (html_of_elt_s2 det) None
  | Det (det, Some rel) -> html_det (html_of_elt_s2 det) (Some (html_of_elt_p1 rel))
and html_of_elt_s2 = function
  | Term t -> html_term t
  | Something -> "something"
  | Class c -> "a " ^ html_class c
and html_of_elt_s = function
  | Return np -> html_return (html_of_elt_s1 np)

let rec html_of_ctx_p1 html = function
  | DetThatX (det,ctx) -> html_of_ctx_s1 (html_det (html_of_elt_s2 det) (Some html)) ctx
  | AndX (i,ar,ctx) ->
    let ar_html = Array.map html_of_elt_p1 ar in
    ar_html.(i) <- html;
    html_of_ctx_p1 (html_and ar_html) ctx
and html_of_ctx_s1 html = function
  | HasX (p,ctx) -> html_of_ctx_p1 (html_has p html) ctx
  | IsOfX (p,ctx) -> html_of_ctx_p1 (html_is_of p html) ctx
  | ReturnX -> html_return html

let html_of_focus = function
  | AtP1 (f,ctx) -> html_of_ctx_p1 (html_span ~classe:"focus" (html_of_elt_p1 f)) ctx
  | AtS1 (f,ctx) -> html_of_ctx_s1 (html_span ~classe:"focus" (html_of_elt_s1 f)) ctx

(* focus moves *)

let down_p1 (ctx : ctx_p1) : elt_p1 -> focus option = function
  | Type _ -> None
  | Has (p,np) -> Some (AtS1 (np, HasX (p,ctx)))
  | IsOf (p,np) -> Some (AtS1 (np, IsOfX (p,ctx)))
  | And ar -> Some (AtP1 (ar.(0), AndX (0,ar,ctx)))
let down_s1 (ctx : ctx_s1) : elt_s1 -> focus option = function
  | Det (det,None) -> None
  | Det (det, Some rel) -> Some (AtP1 (rel, DetThatX (det,ctx)))
let down_focus = function
  | AtP1 (f,ctx) -> down_p1 ctx f
  | AtS1 (f,ctx) -> down_s1 ctx f

let up_p1 f = function
  | DetThatX (det,ctx) -> Some (AtS1 (Det (det, Some f), ctx))
  | AndX (i,ar,ctx) -> ar.(i) <- f; Some (AtP1 (And ar, ctx))
let up_s1 f = function
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

let insert_term t focus =
  let focus2_opt =
    match focus with
      | AtP1 (f, DetThatX (_,ctx)) -> Some (AtP1 (f, DetThatX (Term t, ctx)))
      | AtS1 (Det (_,rel_opt), ctx) -> Some (AtS1 (Det (Term t, rel_opt), ctx))
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

let insert_elt_p1 elt = function
  | AtP1 (f, AndX (i,ar,ctx)) -> ar.(i) <- f; Some (append_and ctx elt (And ar))
  | AtP1 (f, ctx) -> Some (append_and ctx elt f)
  | AtS1 (Det (det, None), ctx) -> Some (AtP1 (elt, DetThatX (det,ctx)))
  | AtS1 (Det (det, Some rel), ctx) -> Some (append_and (DetThatX (det,ctx)) elt rel)

let insert_class c = function
  | AtP1 (f, DetThatX (_,ctx)) -> Some (AtP1 (f, DetThatX (Class c, ctx)))
  | AtS1 (Det (_,rel_opt), ctx) -> Some (AtS1 (Det (Class c, rel_opt), ctx)) 
  | focus -> insert_elt_p1 (Type c) focus

let insert_property p focus =
  match insert_elt_p1 (Has (p, Det (Something, None))) focus with
    | Some foc -> down_focus foc
    | None -> None

let insert_inverse_property p focus =
  match insert_elt_p1 (IsOf (p, Det (Something, None))) focus with
    | Some foc -> down_focus foc
    | None -> None

let insert_increment incr focus =
  match incr with
    | IncrTerm t -> insert_term t focus
    | IncrClass c -> insert_class c focus
    | IncrProp p -> insert_property p focus
    | IncrInvProp p -> insert_inverse_property p focus

let rec delete_and ctx ar i =
  let n = Array.length ar in
  if n = 1
  then
    match ctx with
      | DetThatX (det, ctx2) -> AtS1 (Det (det, None), ctx2)
      | AndX (i2, ar2, ctx2) -> delete_and ctx2 ar2 i2
  else
    if n = 2
    then
      AtP1 (ar.(1-i), ctx)
    else
      let ar2 = Array.make (n-1) (Type "") in
      Array.blit ar 0 ar2 0 i;
      Array.blit ar (i+1) ar2 i (n-i-1);
      if i = n-1 && i > 0 (* last elt is deleted *)
      then AtP1 (ar2.(i-1), AndX (i-1, ar2, ctx))
      else AtP1 (ar2.(i+1), AndX (i+1, ar2, ctx))

let delete_focus = function
  | AtP1 (f, DetThatX (det,ctx)) -> Some (AtS1 (Det (det,None), ctx))
  | AtP1 (f, AndX (i,ar,ctx)) -> Some (delete_and ctx ar i)
  | AtS1 (Det _, ctx) -> Some (AtS1 (Det (Something, None), ctx))

(* HTML of increment lists *)

let html_of_increment_frequency dico_incrs (incr,freq) =
  let key = dico_incrs#add incr in
  let text =
    match incr with
      | IncrTerm t -> html_term t
      | IncrClass c -> "a " ^ html_class c
      | IncrProp p -> "has " ^ html_prop p
      | IncrInvProp p -> "is " ^ html_prop p ^ " of" in
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
      bindings : term array list;
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
    List.rev_map (fun binding -> binding.(i)) results.bindings
  with Not_found ->
    Firebug.console##log(string ("list_of_results_column: missing variable " ^ var));
    []

let index_of_results_column (var : var) results : (term * int) list =
  try
    let i = List.assoc var results.vars in
    let ht = Hashtbl.create 1000 in
    List.iter
      (fun binding ->
	let term = binding.(i) in
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
	  let x = binding.(i_x) in
	  let count =
	    match binding.(i_count) with
	      | TypedLiteral (s,dt) -> (try int_of_string s with _ -> 0)
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

let sparql_results_of_json s_json =
  try
    let ojson = Json.unsafe_input s_json in
    let ohead = Unsafe.get ojson (string "head") in
    let ovars = Unsafe.get ohead (string "vars") in
    let dim = truncate (to_float (Unsafe.get ovars (string "length"))) in
    let vars =
      let res = ref [] in
      for i = dim-1 downto 0 do
	let ovar = Unsafe.get ovars (string (string_of_int i)) in
	let var = to_string (Unsafe.get ovar (string "fullBytes")) in
	res := (var,i)::!res
      done;
      !res in
    let oresults = Unsafe.get ojson (string "results") in
    let obindings = Unsafe.get oresults (string "bindings") in
    let n = truncate (to_float (Unsafe.get obindings (string "length"))) in
    let length, bindings =
      let len = ref 0 in
      let res = ref [] in
      for j = n-1 downto 0 do
	let obinding = Unsafe.get obindings (string (string_of_int j)) in
	let binding = Array.make dim (PlainLiteral ("","")) in
	List.iter
	  (fun (var,i) ->
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
	    binding.(i) <- term)
	  vars;
	incr len;
	res := binding::!res
      done;
      !len, !res in
    { dim; vars; length; bindings; }
  with exn ->
    Firebug.console##log(string (Printexc.to_string exn));
    empty_results

let html_table_of_results results =
  let buf = Buffer.create 1000 in
  Buffer.add_string buf "<table id=\"extension\"><tr>";
  List.iter
    (fun (var,i) ->
      Buffer.add_string buf "<th>";
      Buffer.add_string buf var;
      Buffer.add_string buf "</th>")
    results.vars;
  Buffer.add_string buf "</tr>";
  List.iter
    (fun binding ->
      Buffer.add_string buf "<tr>";
      for i = 0 to results.dim - 1 do
	let t = binding.(i) in
	Buffer.add_string buf "<td>";
	Buffer.add_string buf (html_term ~link:true t);
	Buffer.add_string buf "</td>"
      done;
      Buffer.add_string buf "</tr>")
    results.bindings;
  Buffer.add_string buf "</table>";
  Buffer.contents buf

(* ------------------ *)

let jquery_from (root : Dom_html.nodeSelector Js.t (*= Dom_html.document*)) s k =
  Opt.iter (root##querySelector(string s)) (fun elt ->
    k elt)
let jquery s k = jquery_from (Dom_html.document :> Dom_html.nodeSelector t) s k

let jquery_input_from (root : Dom_html.nodeSelector Js.t) s k =
  Opt.iter (root##querySelector(string s)) (fun elt ->
    Opt.iter (Dom_html.CoerceTo.input elt) (fun input ->
      k input))
let jquery_input s k = jquery_input_from (Dom_html.document :> Dom_html.nodeSelector t) s k

let jquery_all_from (root : Dom_html.nodeSelector Js.t (*= Dom_html.document*)) s k =
  let nodelist = root##querySelectorAll(string s) in
  let n = nodelist##length in
  for i=0 to n-1 do
    Opt.iter nodelist##item(i) k
  done
let jquery_all s k = jquery_all_from (Dom_html.document :> Dom_html.nodeSelector t) s k

let jquery_set_innerHTML sel html =
  jquery sel (fun elt -> elt##innerHTML <- string html)

let onclick k elt =
  elt##onclick <- Dom.handler (fun ev -> k elt ev; bool true)

let ondblclick k elt =
  elt##ondblclick <- Dom.handler (fun ev -> k elt ev; bool true)

let oninput k elt =
  elt##oninput <- Dom.handler (fun ev -> k elt ev; bool true)

let ajax_sparql_in (elt : Dom_html.element t) (sparql : sparql) (k : sparql_results -> unit) =
  Firebug.console##log(string sparql);
  elt##style##cursor <- string "progress";
  Lwt.ignore_result
    (Lwt.bind
       (perform_raw_url
	  ~headers:[("Accept","application/json")]
	  ~post_args:[("query", sparql)]
	  "http://dbpedia.org/sparql")
       (fun xhr ->
	 ( match xhr.code / 100 with
	   | 2 ->
	     let content = string xhr.content in
	     let results = sparql_results_of_json content in
	     k results;
	     elt##style##cursor <- string "default"
	   | _ ->
	     Firebug.console##log(string ("SPARQL request unsuccessful: code " ^ string_of_int xhr.code)));
	 Lwt.return_unit))
let ajax_sparql sparql k =
  ajax_sparql_in (Dom_html.document##documentElement) sparql k

(* -------------------- *)

class dico_increments =
object
  val mutable cpt = 0
  val ht : (string,increment) Hashtbl.t = Hashtbl.create 100

  method add (incr : increment) : string =
    cpt <- cpt + 1;
    let key = "incr" ^ string_of_int cpt in
    Hashtbl.add ht key incr;
    key

  method get (key : string) : increment =
    try Hashtbl.find ht key
    with _ ->
      Firebug.console##log(string ("Missing increment: " ^ key));
      failwith "Osparqlis.dico_increments#get"
end


(* navigation place *)
class place =
object (self)
  val mutable offset = 0
  val mutable limit = 10

  val mutable focus = AtS1 (Det (Something, None), ReturnX)
  val mutable pattern = ""

  val mutable focus_term = Var "thing"
  val mutable sparql_opt = None
  method private define_sparql =
    let t, s_opt = sparql_of_focus focus in
    focus_term <- t;
    sparql_opt <-
      ( match s_opt with
	| None -> None
	| Some (lv,gp) ->
	  let gp =
	    if pattern = ""
	    then gp
	    else sparql_join [gp; sparql_pattern t pattern] in
	  Some (sparql_select lv gp ^ "\nLIMIT 200") )

  val mutable results = empty_results

  method private refresh_extension =
    jquery_set_innerHTML "#result"
      (html_table_of_results
	 (page_of_results offset limit results))

  method private focus_term_index focus_term results : (term * int) list =
    match focus_term with
      | Var v -> index_of_results_column v results
      | t -> [(t, results.length)]

  method private refresh_term_increments focus_term_index dico_incrs =
    jquery "#terms" (fun elt ->
      elt##innerHTML <- string
	(html_of_increment_frequency_list dico_incrs
	   (List.rev_map (fun (t, freq) -> (IncrTerm t, freq)) focus_term_index));
      jquery_all_from (elt :> Dom_html.nodeSelector t) ".increment" (onclick (fun elt ev ->
	self#focus_update (insert_increment (dico_incrs#get (to_string (elt##id)))))))

  method private refresh_class_increments_init dico_incrs =
    jquery "#classes" (fun elt ->
(*      let sparql = "SELECT DISTINCT ?class (COUNT(DISTINCT ?focus) AS ?freq) WHERE { ?focus a ?class } LIMIT 100" in *)
      let sparql = "SELECT DISTINCT ?class WHERE { { [] rdfs:domain ?class } UNION { [] rdfs:range ?class } } LIMIT 1000" in
      ajax_sparql_in elt sparql (fun results ->
	let class_list = list_of_results_column "class" results in
	elt##innerHTML <- string
	  (html_of_increment_frequency_list dico_incrs
	     (List.fold_left
		(fun res -> function
		  | URI c -> (IncrClass c, 1) :: res
		  | _ -> res)
		[] class_list));
	jquery_all_from (elt :> Dom_html.nodeSelector t) ".increment" (onclick (fun elt ev ->
	  self#focus_update (insert_increment (dico_incrs#get (to_string (elt##id))))))))

  method private refresh_class_increments focus_term_index dico_incrs =
    jquery "#classes" (fun elt ->
      let sparql =
	let vals = String.concat " " (List.map (fun (t,_) -> sparql_term t) focus_term_index) in
	"SELECT DISTINCT ?class (COUNT(DISTINCT ?focus) AS ?freq) WHERE { VALUES ?focus { " ^ vals ^ " } ?focus a ?class } ORDER BY DESC(?freq) ?class LIMIT 100" in
      ajax_sparql_in elt sparql (fun results ->
	let class_index = index_of_results_2columns "class" "freq" results in
	elt##innerHTML <- string
	  (html_of_increment_frequency_list dico_incrs
	     (List.fold_left
		(fun res -> function
		  | (URI c, freq) -> (IncrClass c, freq) :: res
		  | _ -> res)
		[] class_index));
	jquery_all_from (elt :> Dom_html.nodeSelector t) ".increment" (onclick (fun elt ev ->
	  self#focus_update (insert_increment (dico_incrs#get (to_string (elt##id))))))))
 
  method private refresh_property_increments focus_term_index dico_incrs =
    jquery "#properties" (fun elt ->
      let vals = String.concat " " (List.map (fun (t,_) -> sparql_term t) focus_term_index) in
      let sparql = "SELECT DISTINCT ?prop (COUNT (DISTINCT ?focus) AS ?freq) WHERE { VALUES ?focus { " ^ vals ^ " } ?focus ?prop [] } ORDER BY DESC(?freq) ?prop LIMIT 100" in
      ajax_sparql_in elt sparql (fun results ->
	let index = index_of_results_2columns "prop" "freq" results in
	elt##innerHTML <- string
	  (html_of_increment_frequency_list dico_incrs
	     (List.fold_left
		(fun res -> function
		  | (URI c, freq) -> (IncrProp c, freq) :: res
		  | _ -> res)
		[] index));
	jquery_all_from (elt :> Dom_html.nodeSelector t) ".increment" (onclick (fun elt ev ->
	  self#focus_update (insert_increment (dico_incrs#get (to_string (elt##id))))))))

  method private refresh_inverse_property_increments focus_term_index dico_incrs =
    jquery "#inverse-properties" (fun elt ->
      let vals = String.concat " " (List.map (fun (t,_) -> sparql_term t) focus_term_index) in
      let sparql = "SELECT DISTINCT ?prop (COUNT(DISTINCT ?focus) AS ?freq) WHERE { VALUES ?focus { " ^ vals ^ " } [] ?prop ?focus } ORDER BY DESC(?freq) ?prop LIMIT 100" in
      ajax_sparql_in elt sparql (fun results ->
	let index = index_of_results_2columns "prop" "freq" results in
	elt##innerHTML <- string
	  (html_of_increment_frequency_list dico_incrs
	     (List.fold_left
		(fun res -> function
		  | (URI c, freq) -> (IncrInvProp c, freq) :: res
		  | _ -> res)
		[] index));
	jquery_all_from (elt :> Dom_html.nodeSelector t) ".increment" (onclick (fun elt ev ->
	  self#focus_update (insert_increment (dico_incrs#get (to_string (elt##id))))))))

  method refresh =
    jquery_set_innerHTML "#lisql" (html_of_focus focus);
    genvar#reset;
    self#define_sparql;
    match sparql_opt with
      | None ->
	jquery_set_innerHTML "#sparql" "";
	( match focus_term with
	  | Var v ->
	    jquery_set_innerHTML "#result" "";
	    let dico_incrs = new dico_increments in
	    jquery_set_innerHTML "#terms" "";
	    jquery_set_innerHTML "#classes" "";
	    jquery_set_innerHTML "#properties" "";
	    jquery_set_innerHTML "#inverse-properties" "";
	    self#refresh_class_increments_init dico_incrs
	  | term ->
	    results <- { dim=1; vars=[("thing",0)]; length=1; bindings=[ [|term|] ]; };
	    self#refresh_extension;
	    let focus_term_index = [(term,1)] in
	    let dico_incrs = new dico_increments in
	    self#refresh_term_increments focus_term_index dico_incrs;
	    self#refresh_class_increments focus_term_index dico_incrs;
	    self#refresh_property_increments focus_term_index dico_incrs;
	    self#refresh_inverse_property_increments focus_term_index dico_incrs )
      | Some sparql ->
	jquery_set_innerHTML "#sparql" (html_pre sparql);
	ajax_sparql sparql (fun res ->
	  results <- res;
	  self#refresh_extension;
	  let focus_term_index = self#focus_term_index focus_term results in
	  let dico_incrs = new dico_increments in
	  self#refresh_term_increments focus_term_index dico_incrs;
	  self#refresh_class_increments focus_term_index dico_incrs;
	  self#refresh_property_increments focus_term_index dico_incrs;
	  self#refresh_inverse_property_increments focus_term_index dico_incrs);
	()

  method home =
    focus <- AtS1 (Det (Something, None), ReturnX);
    offset <- 0;
    self#refresh

  method give_more =
    if offset + limit < results.length
    then begin
      limit <- limit + 10;
      self#refresh_extension
    end

  method give_less =
    if limit > 10
    then begin
      limit <- limit - 10;
      self#refresh_extension
    end

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
      self#refresh_extension
    end

  method focus_update f =
    match f focus with
      | Some foc ->
	focus <- foc;
	pattern <- "";
	jquery_input "#pattern" (fun elt -> elt##value <- string "");
	self#refresh
      | None -> ()

  method pattern_changed pat =
    let n = String.length pat in
    if pat = "" || pat.[n-1] = ' '
    then begin
      Firebug.console##log(string pat);
      pattern <- String.sub pat 0 (max 0 (n-1));
      self#refresh
    end

end
  
let myplace = new place

let _ =
  Firebug.console##log(string "Starting Sparklis");
  Dom_html.window##onload <- Dom.handler (fun ev ->
    jquery "#home" (onclick (fun elt ev -> myplace#home));

    jquery_input "#pattern" (oninput (fun input ev -> myplace#pattern_changed (to_string input##value)));
    jquery "#down" (onclick (fun elt ev -> myplace#focus_update down_focus));
    jquery "#up" (onclick (fun elt ev -> myplace#focus_update up_focus));
    jquery "#right" (onclick (fun elt ev -> myplace#focus_update right_focus));
    jquery "#left" (onclick (fun elt ev -> myplace#focus_update left_focus));
    jquery "#delete" (onclick (fun elt ev -> myplace#focus_update delete_focus));

    jquery "#more" (onclick (fun elt ev -> myplace#give_more));
    jquery "#less" (onclick (fun elt ev -> myplace#give_less));
    jquery "#page-down" (onclick (fun elt ev -> myplace#page_down));
    jquery "#page-up" (onclick (fun elt ev -> myplace#page_up));

    myplace#refresh;
    bool true)
