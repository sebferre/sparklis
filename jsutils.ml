
open Js
open XmlHttpRequest

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

(* prepare a string for safe insertion in HTML code *)
let escapeHTML (str : string) : string =
  let div = Dom_html.createDiv Dom_html.document in
  ignore (div##appendChild((Dom_html.document##createTextNode(string str) :> Dom.node t)));
  to_string (div##innerHTML)
