
open Js
open XmlHttpRequest

(* ------------------------ *)

(* SPARQL variable generator *)
let genvar =
object
  val mutable cpt = 0
  method reset = cpt <- 0
  method get = cpt <- cpt+1; "?x" ^ string_of_int cpt
end

(* ------------------------- *)

type uri = string
type var = string

(* LISQL elts *)
type elt_p1 =
  | Type of uri
  | Has of uri * elt_s1
  | IsOf of uri * elt_s1
  | And of elt_p1 array
and elt_s1 =
  | Det of elt_s2 * elt_p1 option
and elt_s2 =
  | Term of string
  | Something
  | Class of uri
and elt_s =
  | What of var * elt_p1

(* LISQL contexts *)
type ctx_p1 =
  | DetThatX of elt_s2 * ctx_s1
  | AndX of int * elt_p1 array * ctx_p1
  | WhatX of var
and ctx_s1 =
  | HasX of uri * ctx_p1
  | IsOfX of uri * ctx_p1

(* LISQL focus *)
type focus =
  | AtP1 of elt_p1 * ctx_p1
  | AtS1 of elt_s1 * ctx_s1

(* extraction of LISQL s element from focus *)
let rec elt_s_of_ctx_p1 (f : elt_p1) = function
  | DetThatX (det,ctx) -> elt_s_of_ctx_s1 (Det (det, Some f)) ctx
  | AndX (i,ar,ctx) -> ar.(i) <- f; elt_s_of_ctx_p1 (And ar) ctx
  | WhatX (x) -> What (x,f)
and elt_s_of_ctx_s1 (f : elt_s1) = function
  | HasX (p,ctx) -> elt_s_of_ctx_p1 (Has (p,f)) ctx
  | IsOfX (p,ctx) -> elt_s_of_ctx_p1 (IsOf (p,f)) ctx

let elt_s_of_focus = function
  | AtP1 (f,ctx) -> elt_s_of_ctx_p1 f ctx
  | AtS1 (f,ctx) -> elt_s_of_ctx_s1 f ctx


(* translation from LISQL elts to SPARQL queries *)
let rec sparql_of_elt_p1 = function
  | Type c -> (fun x -> x ^ " a " ^ c ^ " . ")
  | Has (p,np) -> (fun x -> sparql_of_elt_s1 np (fun y -> x ^ " " ^ p ^ " " ^ y ^ " . "))
  | IsOf (p,np) -> (fun x -> sparql_of_elt_s1 np (fun y -> y ^ " " ^ p ^ " " ^ x ^ " . "))
  | And ar ->
    (fun x ->
      let res = ref (sparql_of_elt_p1 ar.(0) x) in
      for i=1 to Array.length ar - 1 do
	res := !res ^ sparql_of_elt_p1 ar.(i) x
      done;
      !res)
and sparql_of_elt_s1 = function
  | Det (det,rel_opt) ->
    let d1 = match rel_opt with None -> (fun x -> "") | Some rel -> sparql_of_elt_p1 rel in
    (fun d -> sparql_of_elt_s2 det d1 d)
and sparql_of_elt_s2 = function
  | Term t -> (fun d1 d2 -> d1 t ^ d2 t)
  | Something -> (fun d1 d2 -> let x = genvar#get in d1 x ^ d2 x)
  | Class c -> (fun d1 d2 -> let x = genvar#get in x ^ " a " ^ c ^ " . " ^ d1 x ^ d2 x)
and sparql_of_elt_s = function
  | What (x,vp) -> "SELECT " ^ x ^ " WHERE { " ^ sparql_of_elt_p1 vp x ^ "}"

(* pretty-printing of focus as HTML *)

let html_span cl text = "<span class=\"" ^ cl ^ "\">" ^ text ^ "</span>"
let html_term t = html_span "RDFTerm" t
let html_class c = html_span "classURI" c
let html_prop p = html_span "propURI" p

let html_is_a c = "is a " ^ html_class c
let html_has p np = "has " ^ html_prop p ^ " " ^ np
let html_is_of p np = "is " ^ html_prop p ^ " of " ^ np
let html_and ar =
  let html = ref ar.(0) in
  for i=1 to Array.length ar - 1 do
    html := !html ^ " and " ^ ar.(i)
  done;
  !html
let html_det det rel_opt = det ^ (match rel_opt with None -> "" | Some rel -> " that " ^ rel)
let html_what vp = "What " ^ vp ^ " ?"

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
  | Class c -> html_class c
and html_of_elt_s = function
  | What (x,vp) -> html_what (html_of_elt_p1 vp)

let rec html_of_ctx_p1 html = function
  | DetThatX (det,ctx) -> html_of_ctx_s1 (html_det (html_of_elt_s2 det) (Some html)) ctx
  | AndX (i,ar,ctx) ->
    let ar_html = Array.map html_of_elt_p1 ar in
    ar_html.(i) <- html;
    html_of_ctx_p1 (html_and ar_html) ctx
  | WhatX (x) -> html_what html
and html_of_ctx_s1 html = function
  | HasX (p,ctx) -> html_of_ctx_p1 (html_has p html) ctx
  | IsOfX (p,ctx) -> html_of_ctx_p1 (html_is_of p html) ctx

let html_of_focus = function
  | AtP1 (f,ctx) -> html_of_ctx_p1 (html_span "focus" (html_of_elt_p1 f)) ctx
  | AtS1 (f,ctx) -> html_of_ctx_s1 (html_span "focus" (html_of_elt_s1 f)) ctx

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
  | WhatX (x) -> None
let up_s1 f = function
  | HasX (p,ctx) -> Some (AtP1 (Has (p,f), ctx))
  | IsOfX (p,ctx) -> Some (AtP1 (IsOf (p,f), ctx))
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
  | WhatX (x) -> None
let right_s1 (f : elt_s1) : ctx_s1 -> focus option = function
  | HasX _ -> None
  | IsOfX _ -> None
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
  | WhatX (x) -> None
let left_s1 (f : elt_s1) : ctx_s1 -> focus option = function
  | HasX _ -> None
  | IsOfX _ -> None
let left_focus = function
  | AtP1 (f,ctx) -> left_p1 f ctx
  | AtS1 (f,ctx) -> left_s1 f ctx

(* ------------------ *)

let jquery s k =
  Opt.iter (Dom_html.document##querySelector(string s)) (fun elt ->
    k elt)

let onclick k elt =
  elt##onclick <- Dom.handler (fun ev -> k ev; bool true)


(* -------------------- *)

(* navigation place *)
class place =
object (self)
  val mutable limit = 10
  val mutable focus =
    AtP1 (And [| Type "dbpedia-owl:Film";
		 Has ("dbpedia-owl:director",
		      Det (Class "dbpedia-owl:Person",
			   Some (IsOf ("dbpedia-owl:director",
				       Det (Term "dbpedia:The_Terminal",
					    None)))))
	      |],
	  WhatX "?what")
	  
  method elt_s = elt_s_of_focus focus
  method sparql = sparql_of_elt_s self#elt_s ^ " LIMIT " ^ string_of_int limit
  method html = html_of_focus focus

  method refresh =
    let sparql = self#sparql in
    jquery "#sparql" (fun elt ->
      elt##innerHTML <- string sparql);
    jquery "#lisql" (fun elt ->
      elt##innerHTML <- string self#html);
    Lwt.ignore_result
      (Lwt.bind
	 (perform_raw_url
	    ~post_args:[("query", sparql)]
	    "http://dbpedia.org/sparql")
	 (fun xhr ->
	   jquery "#result" (fun elt ->
	     elt##innerHTML <- string xhr.content);
	   Lwt.return_unit));
    ()

  method give_more =
    limit <- limit + 10;
    self#refresh

  method give_less =
    if limit > 10
    then begin
      limit <- limit - 10;
      self#refresh
    end

  method focus_move f =
    match f focus with
      | Some foc ->
	focus <- foc;
	self#refresh
      | None -> ()
end
  
let myplace = new place

let _ =
  Firebug.console##log(string "Starting Sparklis");
  Dom_html.window##onload <- Dom.handler (fun ev ->
    jquery "#more" (onclick (fun ev -> myplace#give_more));
    jquery "#less" (onclick (fun ev -> myplace#give_less));

    jquery "#down" (onclick (fun ev -> myplace#focus_move down_focus));
    jquery "#up" (onclick (fun ev -> myplace#focus_move up_focus));
    jquery "#right" (onclick (fun ev -> myplace#focus_move right_focus));
    jquery "#left" (onclick (fun ev -> myplace#focus_move left_focus));

    myplace#refresh;
    bool true)
