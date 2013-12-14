
open Js
open XmlHttpRequest

(* ------------------------ *)

(* SPARQL variable generator *)
let genvar =
object
  val mutable cpt = 0
  method reset = cpt <- 0
  method get = cpt <- cpt+1; "?x" ^ string_of_int cpt

  val mutable var_what = ""
  method set_what v = var_what <- v
  method get_what = var_what

  val mutable var_focus = ""
  method set_focus v = var_focus <- v
  method get_focus = var_focus

  method vars =
    if var_focus = var_what || var_focus = "" || var_focus.[0] <> '?'
    then [var_what]
    else [var_what; var_focus]
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

let sparql_triple s p o = s ^ " " ^ p ^ " " ^ o ^ " . "
let sparql_select lv gp =
  "SELECT DISTINCT " ^ String.concat " " lv ^ " WHERE { " ^ gp ^ "}"

let rec sparql_of_elt_p1 : elt_p1 -> (var -> sparql) = function
  | Type c -> (fun x -> sparql_triple x "a" c)
  | Has (p,np) -> (fun x -> sparql_of_elt_s1 np (fun y -> sparql_triple x p y))
  | IsOf (p,np) -> (fun x -> sparql_of_elt_s1 np (fun y -> sparql_triple y p x))
  | And ar ->
    (fun x ->
      let res = ref (sparql_of_elt_p1 ar.(0) x) in
      for i=1 to Array.length ar - 1 do
	res := !res ^ sparql_of_elt_p1 ar.(i) x
      done;
      !res)
and sparql_of_elt_s1 : elt_s1 -> ((var -> sparql) -> sparql) = function
  | Det (det,rel_opt) ->
    let d1 = match rel_opt with None -> (fun x -> "") | Some rel -> sparql_of_elt_p1 rel in
    (fun d -> sparql_of_elt_s2 det d1 d)
and sparql_of_elt_s2 : elt_s2 -> ((var -> sparql) -> (var -> sparql) -> sparql) = function
  | Term t -> (fun d1 d2 -> d1 t ^ d2 t)
  | Something -> (fun d1 d2 -> let x = genvar#get in d2 x ^ d1 x)
  | Class c -> (fun d1 d2 -> let x = genvar#get in d2 x ^ sparql_triple x "a" c ^ d1 x)
and sparql_of_elt_s : elt_s -> sparql = function
  | Return np ->
    let gp = sparql_of_elt_s1 np (fun x -> genvar#set_what x; "") in
    sparql_select genvar#vars gp

let rec sparql_of_ctx_p1 (d : var -> sparql) : ctx_p1 -> sparql = function
  | DetThatX (det,ctx) ->
    sparql_of_ctx_s1
      (fun d2 -> sparql_of_elt_s2 det d d2) 
      ctx
  | AndX (i,ar,ctx) ->
    sparql_of_ctx_p1
      (fun x ->
	let sparql = ref "" in
	for j=0 to Array.length ar - 1 do
	  if j=i
	  then sparql := !sparql ^ d x
	  else sparql := !sparql ^ sparql_of_elt_p1 ar.(j) x
	done;
	!sparql)
      ctx
and sparql_of_ctx_s1 (q : (var -> sparql) -> sparql) : ctx_s1 -> sparql = function
  | HasX (p,ctx) ->
    sparql_of_ctx_p1
      (fun x -> q (fun y -> sparql_triple x p y))
      ctx
  | IsOfX (p,ctx) ->
    sparql_of_ctx_p1
      (fun x -> q (fun y -> sparql_triple y p x))
      ctx
  | ReturnX ->
    q (fun x -> genvar#set_what x; "")

let sparql_of_focus = function
  | AtP1 (f,ctx) ->
    let gp = sparql_of_ctx_p1 (fun x -> genvar#set_focus x; sparql_of_elt_p1 f x) ctx in
    sparql_select genvar#vars gp
  | AtS1 (f,ctx) ->
    let gp = sparql_of_ctx_s1 (fun d -> sparql_of_elt_s1 f (fun x -> genvar#set_focus x; d x)) ctx in
    sparql_select genvar#vars gp

(* pretty-printing of focus as HTML *)

let html_pre text =
  let text = Regexp.global_replace (Regexp.regexp "<") text "&lt;" in
  let text = Regexp.global_replace (Regexp.regexp ">") text "&gt;" in  
  "<pre>" ^ text ^ "</pre>"
let html_span cl text = "<span class=\"" ^ cl ^ "\">" ^ text ^ "</span>"
let html_term t = html_span "RDFTerm" t
let html_class c = html_span "classURI" c
let html_prop p = html_span "propURI" p

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
let html_return np = "Give me " ^ np ^ "."

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

let insert_term t = function
  | AtP1 (f, DetThatX (_,ctx)) -> Some (AtP1 (f, DetThatX (Term t, ctx)))
  | AtS1 (Det (_,rel_opt), ctx) -> Some (AtS1 (Det (Term t, rel_opt), ctx))
  | _ -> None

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

let delete_and ctx ar i =
  let n = Array.length ar in
  let ar2 = Array.make (n-1) (Type "") in
  Array.blit ar 0 ar2 0 i;
  Array.blit ar (i+1) ar2 i (n-i-1);
  AtP1 (And ar2, ctx)

let delete_focus = function
  | AtP1 (f, DetThatX (det,ctx)) -> Some (AtS1 (Det (det,None), ctx))
  | AtP1 (f, AndX (i,ar,ctx)) -> Some (delete_and ctx ar i)
  | AtS1 (Det _, ctx) -> Some (AtS1 (Det (Something, None), ctx))

(* ------------------ *)

let jquery s k =
  Opt.iter (Dom_html.document##querySelector(string s)) (fun elt ->
    k elt)

let jquery_all s k =
  let nodelist = Dom_html.document##querySelectorAll(string s) in
  let n = nodelist##length in
  for i=0 to n-1 do
    Opt.iter nodelist##item(i) k
  done

let onclick k elt =
  elt##onclick <- Dom.handler (fun ev -> k elt ev; bool true)

let ondblclick k elt =
  elt##ondblclick <- Dom.handler (fun ev -> k elt ev; bool true)


(* -------------------- *)

(* navigation place *)
class place =
object (self)
  val mutable prologue =
    "PREFIX res: <http://dbpedia.org/resource/>\n" ^
      "PREFIX dbo: <http://dbpedia.org/ontology/>\n" ^
      "PREFIX dbp: <http://dbpedia.org/property/>\n" ^
      "PREFIX : <http://dbpedia.org/ontology/>\n"

  val mutable limit = 10

  val mutable focus = AtS1 (Det (Class ":Film", None), ReturnX)
	  
(*  method elt_s = elt_s_of_focus focus*)

  method sparql = prologue ^ sparql_of_focus focus ^ "\nLIMIT " ^ string_of_int limit
  method html = html_of_focus focus

  method refresh =
    genvar#reset;
    let sparql = self#sparql in
    jquery "#sparql" (fun elt ->
      elt##innerHTML <- string (html_pre sparql));
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

  method focus_update f =
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
    jquery "#more" (onclick (fun elt ev -> myplace#give_more));
    jquery "#less" (onclick (fun elt ev -> myplace#give_less));

    jquery "#down" (onclick (fun elt ev -> myplace#focus_update down_focus));
    jquery "#up" (onclick (fun elt ev -> myplace#focus_update up_focus));
    jquery "#right" (onclick (fun elt ev -> myplace#focus_update right_focus));
    jquery "#left" (onclick (fun elt ev -> myplace#focus_update left_focus));
    jquery "#delete" (onclick (fun elt ev -> myplace#focus_update delete_focus));

    jquery_all ".incr-term" (ondblclick (fun elt ev ->
      let t = to_string elt##innerHTML in
      myplace#focus_update (insert_term t)));
    jquery_all ".incr-class" (ondblclick (fun elt ev ->
      let c = to_string elt##innerHTML in
      myplace#focus_update (insert_class c)));
    jquery_all ".incr-property" (ondblclick (fun elt ev ->
      let p = to_string elt##innerHTML in
      myplace#focus_update (insert_property p)));
    jquery_all ".incr-inverse-property" (ondblclick (fun elt ev ->
      let p = to_string elt##innerHTML in
      myplace#focus_update (insert_inverse_property p)));

    myplace#refresh;
    bool true)
