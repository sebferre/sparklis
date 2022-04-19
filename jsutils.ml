(*
   Copyright 2013 Sébastien Ferré, IRISA, Université de Rennes 1, ferre@irisa.fr

   This file is part of Sparklis.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

open Js_of_ocaml
open Js_of_ocaml_lwt
       
open Js
open XmlHttpRequest

let raise_error msg = raise_js_error (new%js error_constr (string msg))
   
let alert msg = Dom_html.window##alert (string msg)

let confirm msg = to_bool (Dom_html.window##confirm (string msg))
              
let prompt msg text = Dom_html.window##prompt (string msg) (string text)

let firebug msg = Firebug.console##log (string msg)

let make_data_url mime contents =
  "data:" ^ mime ^ "," ^ Url.urlencode contents				       
let trigger_download ~mime contents : unit =
  let data_url = make_data_url mime contents in
  let _w_opt = Dom_html.window##open_ (string data_url) (string "_blank") null in
  ()
  
let timeout (dur : float) (k : unit -> unit) : unit =
  ignore (Dom_html.window##setTimeout (wrap_callback k) dur)

let set_innerHTML elt s = elt##.innerHTML := string s
						   
let set_innerHTML_fadeInOut_then elt (s : string) (k : unit -> unit) : unit =
  if not (to_bool (elt##hasAttribute (string "transition"))) then
    elt##setAttribute (string "transition") (string "opacity .2s linear");
  elt##.style##.opacity := def (string "0.3");
  timeout 200. (* 200ms should match the transition-duration on [elt] *)
	  (fun () ->
	   elt##.innerHTML := string s;
	   elt##.style##.opacity := def (string "1");
	   k ())
let set_innerHTML_fadeInOut elt s =
  set_innerHTML_fadeInOut_then elt s (fun () -> ())

						  
let jquery_from (root : #Dom_html.nodeSelector Js.t) s k =
  Opt.iter (root##querySelector (string s)) (fun elt ->
    k elt)
let jquery s k = jquery_from Dom_html.document s k

let jquery_input_from (root : #Dom_html.nodeSelector Js.t) s k =
  Opt.iter (root##querySelector (string s)) (fun elt ->
    Opt.iter (Dom_html.CoerceTo.input elt) (fun input ->
      k input))
let jquery_input s k = jquery_input_from Dom_html.document s k

let jquery_select_from (root : #Dom_html.nodeSelector Js.t) s k =
  Opt.iter (root##querySelector (string s)) (fun elt ->
    Opt.iter (Dom_html.CoerceTo.select elt) (fun select ->
      k select))
let jquery_select s k = jquery_select_from Dom_html.document s k

let jquery_all_from (root : #Dom_html.nodeSelector Js.t) s k =
  let nodelist = root##querySelectorAll (string s) in
  let n = nodelist##.length in
  for i=0 to n-1 do
    Opt.iter (nodelist##item i) k
  done
let jquery_all s k = jquery_all_from Dom_html.document s k

let jquery_get_innerHTML sel =
  let res = ref "" in
  jquery sel (fun elt -> res := to_string elt##.innerHTML);
  !res
let jquery_set_innerHTML sel html =
  jquery sel (fun elt -> elt##.innerHTML := string html)
let jquery_set_innerHTML_fadeInOut sel html =
  jquery sel (fun elt -> set_innerHTML_fadeInOut elt html)
let jquery_set_innerHTML_fadeInOut_then sel html k =
  jquery sel (fun elt -> set_innerHTML_fadeInOut_then elt html k)
let jquery_toggle_innerHTML sel (s1 : string) (s2 : string) : string =
  let new_s = ref "" in
  jquery sel (fun elt ->
    new_s := (if to_string elt##.innerHTML = s1 then s2 else s1);
    elt##.innerHTML := string !new_s);
  !new_s

let jquery_shown sel =
  let res = ref false in
  jquery sel (fun elt -> res := (to_string elt##.style##.display = "block"));
  !res
let jquery_show sel = jquery sel (fun elt -> elt##.style##.display := string "block")
let jquery_hide sel = jquery sel (fun elt -> elt##.style##.display := string "none")
let jquery_toggle sel = jquery sel (fun elt ->
  if to_string elt##.style##.display = "none"
  then elt##.style##.display := string "block"
  else elt##.style##.display := string "none")    

let jquery_disable_all sel =
  jquery_all
    sel
    (fun elt ->
     let classes = elt##.classList in
     classes##add (string "disabled");
     classes##add (string "disabledClick"))
let jquery_enable_all sel =
  jquery_all
    sel
    (fun elt ->
     let classes = elt##.classList in
     classes##remove (string "disabled");
     classes##remove (string "disabledClick"))

let jquery_click_from elt sel = jquery_from elt sel (fun elt -> Unsafe.(meth_call elt "click" [||]))
let jquery_click sel = jquery_click_from Dom_html.document sel

let onclick k elt =
  elt##.onclick := Dom.handler (fun ev -> k elt ev; bool true)

let ondblclick k elt =
  elt##.ondblclick := Dom.handler (fun ev -> k elt ev; bool true)

let onhover k elt =
  elt##.onmouseover := Dom.handler (fun ev -> k elt ev; bool true)

let onhover_out k elt =
  elt##.onmouseout := Dom.handler (fun ev -> k elt ev; bool true)

let oninput k elt =
  elt##.oninput := Dom.handler (fun ev -> k elt ev; bool true)

let onchange k elt =
  elt##.onchange := Dom.handler (fun ev -> k elt ev; bool true)

let onkeypress k elt =
  elt##.onkeypress := Dom.handler (fun ev -> k elt ev; bool true)
let onkeydown k elt =
  elt##.onkeydown := Dom.handler (fun ev -> k elt ev; bool true)

let onenter k elt =
  onkeypress
    (fun elt ev -> if ev##.keyCode = 13 then begin k elt ev; bool true end else bool false)
    elt

let stop_propagation_from elt sel =
  jquery_all_from elt sel
    (onclick (fun elt ev -> Dom_html.stopPropagation ev))
let stop_links_propagation_from elt = stop_propagation_from elt "a"

let toggle_class (elt : Dom_html.element t) (cl : string) : bool =
  let clList = elt##.classList in
  to_bool (clList##toggle (string cl))
							    
(* prepare a string for safe insertion in HTML code *)
let escapeHTML (str : string) : string =
  let div = Dom_html.createDiv Dom_html.document in
  ignore (div##appendChild (Dom_html.document##createTextNode (string str) :> Dom.node t));
  to_string div##.innerHTML

let integer_of_input ?(min = min_int) ?(max = max_int) input : int option =
  try
    let n = int_of_string (to_string input##.value) in
    if n < min then None
    else if n > max then None
    else Some n
  with _ -> None

(* DOM utilities *)

let getElementsByTagNameNS (elt : Dom.element t) (ns : js_string t) (name : js_string t) : Dom.element Dom.nodeList t =
(*elt##getElementsByTagName(name)*)
  Unsafe.coerce (Unsafe.meth_call elt "getElementsByTagNameNS" [|Unsafe.inject ns; Unsafe.inject name|])

let lookupPrefix (elt : Dom.element t) (ns : js_string t) : js_string t opt =
  (* not working in Internet Explorer *)
  some (Unsafe.coerce (Unsafe.meth_call elt "lookupPrefix" [|Unsafe.inject ns|]))

(* local storage utilities *)

type 'a storage_key = string
  
let get_localStorage (key : 'a storage_key) : 'a option =
  Optdef.case
    Dom_html.window##.localStorage
    (fun () -> firebug "Your browser has no local storage"; None)
    (fun storage ->
      let jkey = string key in
      try
        Opt.to_option
          (Opt.map
             (storage##getItem jkey)
             Json.unsafe_input)
      with _ -> None)
  
let update_localStorage (key : 'a storage_key) (f : 'a option -> 'a option) (ferr : error t -> unit) : unit =
  Optdef.case
    Dom_html.window##.localStorage
    (fun () -> firebug "Your browser has no local storage")
    (fun storage ->
      let jkey = string key in
      let arg_opt =
        try
          Opt.to_option
            (Opt.map
               (storage##getItem jkey)
               Json.unsafe_input)
        with _ -> None in
      let res_opt = f arg_opt in
      try
        match res_opt with
        | Some res ->
           storage##setItem jkey (Json.output res)
        | None -> storage##removeItem jkey
      with Error err ->
        firebug (string_of_error err);
        ferr err)
  

(* helping injection of OCaml values to JSON values *)

let string_of_js (js : _ t) : string =
  to_string (_JSON##stringify js)
  
module Inject =
struct
  let null : Unsafe.any = Unsafe.inject Js.null
  let undefined : Unsafe.any = Unsafe.inject Js.undefined
  let bool (b : bool) : Unsafe.any = Unsafe.inject (bool b)
  let int (i : int) : Unsafe.any = Unsafe.inject i
  let float (f : float) : Unsafe.any = Unsafe.inject f
  let string (s : string) : Unsafe.any = Unsafe.inject (string s)
  let array (ar : Unsafe.any array) : Unsafe.any = Unsafe.inject (array ar)
  let obj (ar : (string * Unsafe.any) array) : Unsafe.any = Unsafe.obj ar
end

module Extract =
  struct
    let str_boolean = string "boolean"
    let str_number = string "number"
    let str_string = string "string"
    
    let raise_error_wrong_type expected js =
      raise_error ("Expected a " ^ expected ^ " but found: " ^ string_of_js js)
    let raise_error_null_property name js =
      raise_error ("Property " ^ name ^ " is undefined or null in: " ^ string_of_js js)
    let raise_error_invalid_index pos js =
      raise_error ("Index " ^ string_of_int pos ^ " is undefined or null in: " ^ string_of_js js)

    let as_bool (js : Unsafe.any) : bool (* unsafe *) =
      if Js.typeof js = str_boolean
      then Js.to_bool (Unsafe.coerce js)
      else raise_error_wrong_type "boolean" js
    let as_int (js : Unsafe.any) : int (* unsafe *) =
      if Js.typeof js = str_number
      then
        try int_of_float (Js.float_of_number (Unsafe.coerce js))
        with _ -> raise_error_wrong_type "integer" js
      else raise_error_wrong_type "number" js
    let as_float (js : Unsafe.any) : float (* unsafe *) =
      if Js.typeof js = str_number
      then Js.float_of_number (Unsafe.coerce js)
      else raise_error_wrong_type "number" js
    let as_string (js : Unsafe.any) : string (* unsafe *) =
      if Js.typeof js = str_string
      then Js.to_string (Unsafe.coerce js)
      else raise_error_wrong_type "string" js
    let as_object (js : Unsafe.any) : _ t (* unsafe *) =
      if Js.instanceof js Unsafe.global##.Object
      then js
      else raise_error_wrong_type "object" js
    let as_array (js : Unsafe.any) : _ array (* unsafe *) =
      if Js.instanceof js Unsafe.global##.Array
      then Js.to_array (Unsafe.coerce js)
      else raise_error_wrong_type "array" js
    let as_option (js : Unsafe.any) : _ option (* unsafe *) =
      if some js = null
      then None
      else Some js

    let get (js : Unsafe.any) (name : string) : _ t (* unsafe *) =
      let v = Unsafe.get js (string name) in
      if v = Js.null then raise_error_null_property name js
      else v
    let get_index (js : Unsafe.any) (pos : int) : _ t (* unsafe *) =
      let v = Unsafe.get js pos in
      if v = Js.null then raise_error_invalid_index pos js
      else v
  end

type 'a js_map =
  { spec : js_map_spec;
    inject : 'a -> Unsafe.any;
    extract : Unsafe.any -> 'a }  
and js_map_spec = (* fields and constructors to be specified in declaration order *)
  [ `Bool
  | `Int
  | `Float
  | `String
  | `List of js_map_spec
  | `Array of js_map_spec
  | `Tuple of js_map_spec array (* can be used for records, and singleton sum *)
  | `Record of (string * js_map_spec) array (* can be used for tuples, and singleton sum *)
  | `Sum of (* WARNING: not for variants! *)
      string array (* constant constructors, "null" encoded as Js.null *)
      * (string * (string * js_map_spec) array) array (* non-constant constructors *)
  | `Enum of string array (* special case of Sum, only constant constructors *)
  | `Option of js_map_spec
  | `Custom of Obj.t js_map
  | `Rec of string
  | `Abstract ]

let sum_spec_of_enum constr_names =
  `Sum (constr_names, [| |])
  
let rec string_of_js_map_spec = function
  | `Bool -> "bool"
  | `Int -> "int"
  | `Float -> "float"
  | `String -> "string"
  | `List spec -> string_of_js_map_spec spec ^ " list"
  | `Array spec -> string_of_js_map_spec spec ^ " array"
  | `Tuple fields ->
     "(" ^ String.concat " * "
             (Array.to_list (Array.map string_of_js_map_spec fields)) ^ ")"
  | `Record fields ->
     "{" ^ String.concat "; "
             (Array.to_list
                (Array.map
                   (fun (name,spec) ->
                     name ^ ": " ^ string_of_js_map_spec spec)
                   fields)) ^ "}"
  | `Sum (constructors_cst, constructors_non_cst) ->
     "["
     ^ String.concat " | "
         (Array.to_list constructors_cst
          @ Array.to_list
              (Array.map
                 (fun (constr,fields) ->
                   constr ^ (if fields = [| |] then ""
                             else " {" ^ string_of_js_map_spec (`Record fields) ^ "}"))
                 constructors_non_cst))
     ^ "]"
  | `Enum constr_names -> 
     string_of_js_map_spec (sum_spec_of_enum constr_names)
  | `Option spec -> string_of_js_map_spec spec ^ " option"
  | `Custom { spec } -> string_of_js_map_spec spec
  | `Rec name -> "<rec:" ^ name ^ ">"
  | `Abstract -> "<abstract>"

exception InconsistentMapSpec

let raise_inconsistent_map_spec spec r =
  Firebug.console##log_4 (string "inconsistent js_map_spec") (string (string_of_js_map_spec spec)) (string "on") r;
  raise InconsistentMapSpec
                               
let rec js_inject (rec_specs : (string * js_map_spec) list) (spec : js_map_spec) : Obj.t -> Unsafe.any =
  match spec with
  | `Bool ->
     (fun r ->
       if Obj.is_int r then
         Inject.bool (Obj.obj r : bool)
       else raise_inconsistent_map_spec spec r)
  | `Int ->
     (fun r ->
       if Obj.is_int r then
         Inject.int (Obj.obj r : int)
       else raise_inconsistent_map_spec spec r)
  | `Float ->
     (fun r ->
       if Obj.is_int r then (* surprising but tested, probably means is_number in js_of_ocaml *)
         Inject.float (Obj.obj r : float)
       else raise_inconsistent_map_spec spec r)
  | `String ->
     (fun r ->
       if Obj.is_block r && Obj.tag r = Obj.string_tag then Inject.string (Obj.obj r : string)
       else raise_inconsistent_map_spec spec r)
  | `List spec_elt ->
     let inject_elt = js_inject rec_specs spec_elt in
     (fun r ->
       if Obj.is_int r (* [] *) then
         Inject.array [| |]
       else if Obj.is_block r (* _::_ *) then
         let l = (Obj.obj r : _ list) in
         let ar = Array.of_list l in
         let ar_r = Array.map (fun elt -> inject_elt (Obj.repr elt)) ar in
         Inject.array ar_r
       else raise_inconsistent_map_spec spec r)
  | `Array spec_elt ->
     let inject_elt = js_inject rec_specs spec_elt in
     (fun r ->
       if Obj.is_block r && Obj.tag r = 0 then
         let ar = (Obj.obj r : _ array) in
         let ar_r = Array.map (fun elt -> inject_elt (Obj.repr elt)) ar in
         Inject.array ar_r
       else raise_inconsistent_map_spec spec r)
  | `Tuple fields ->
     let fields_inject =
       Array.map
         (fun spec_field -> js_inject rec_specs spec_field)
         fields in
     (fun r ->
       if Obj.is_block r && Obj.size r = Array.length fields then
         let fields_js =
           Array.mapi
             (fun i inject_field ->
               inject_field (Obj.field r i))
             fields_inject in
         Inject.array fields_js
       else raise_inconsistent_map_spec spec r)
  | `Record fields ->
     let fields_inject =
       Array.map
         (fun (name,spec_field) -> name, js_inject rec_specs spec_field)
         fields in
     (fun r ->
       if Obj.is_block r && Obj.size r = Array.length fields then
         let fields_js =
           Array.mapi
             (fun i (name,inject_field) ->
               name, inject_field (Obj.field r i))
             fields_inject in
         Inject.obj fields_js
       else raise_inconsistent_map_spec spec r)
  | `Sum (constructors_cst, constructors_non_cst) ->
     let constructors_non_cst_inject =
       Array.map
         (fun (constr, fields) ->
           constr,
           Array.map
             (fun (name, spec_field) -> name, js_inject rec_specs spec_field)
             fields)
         constructors_non_cst in
     (fun r ->
       if Obj.is_int r then
         let constr = constructors_cst.((Obj.obj r : int)) in
         if constr = "null"
         then Inject.null
         else Inject.string constr
       else if Obj.is_block r && Obj.tag r < Array.length constructors_non_cst then
         let constr, fields_inject = constructors_non_cst_inject.(Obj.tag r) in
         let fields_js =
           Array.init (1 + Array.length fields_inject)
             (fun i ->
               if i = 0
               then "type", Inject.string constr
               else
                 let name, inject_field = fields_inject.(i-1) in
                 name, inject_field (Obj.field r (i-1))) in
         Inject.obj fields_js
       else raise_inconsistent_map_spec spec r)
  | `Enum constr_names ->
     js_inject rec_specs (sum_spec_of_enum constr_names)
  | `Option spec_contents ->
     let inject_contents = js_inject rec_specs spec_contents in
     (fun r ->
       match Obj.obj r with
       | None -> Inject.null
       | Some x -> inject_contents (Obj.repr x))
  | `Custom { inject } -> inject
  | `Rec name ->
     let rec_spec = try List.assoc name rec_specs with _ -> assert false in
     (fun r -> js_inject rec_specs rec_spec r)
  | `Abstract -> invalid_arg "Jsutils.js_inject: abstract"
             
let rec js_extract (rec_specs : (string * js_map_spec) list) (spec : js_map_spec) : Unsafe.any -> Obj.t =
  match spec with
  | `Bool ->
     (fun js -> Obj.repr (Extract.as_bool js))
  | `Int ->
     (fun js -> Obj.repr (Extract.as_int js))
  | `Float ->
     (fun js -> Obj.repr (Extract.as_float js))
  | `String ->
     (fun js -> Obj.repr (Extract.as_string js))
  | `List spec_elt ->
     let extract_elt = js_extract rec_specs spec_elt in
     (fun js ->
       let ar_js = Extract.as_array js in
       let ar = Array.map extract_elt ar_js in
       let l = Array.to_list ar in
       Obj.repr l)
  | `Array spec_elt ->
     let extract_elt = js_extract rec_specs spec_elt in
     (fun js ->
       let ar_js = Extract.as_array js in
       let ar = Array.map extract_elt ar_js in
       Obj.repr ar)
  | `Tuple fields ->
     let tag = 0 in
     let fields_extract =
       Array.map
         (fun spec_field -> js_extract rec_specs spec_field)
         fields in
     (fun js ->
       let bl = Obj.new_block tag (Array.length fields) in
       Array.iteri
         (fun i extract_field ->
           Obj.set_field bl i (extract_field (Extract.get_index js i)))
         fields_extract;
       bl)
  | `Record fields ->
     let tag = 0 in
     let fields_extract =
       Array.map
         (fun (name,spec_field) -> name, js_extract rec_specs spec_field)
         fields in
     (fun js ->
       let bl = Obj.new_block tag (Array.length fields) in
       Array.iteri
         (fun i (name,extract_field) ->
           Obj.set_field bl i (extract_field (Extract.get js name)))
         fields_extract;
       bl)
  | `Sum (constructors_cst, constructors_non_cst) ->
     let constructors_non_cst_extract =
       Array.map
         (fun (constr, fields) ->
           constr,
           Array.map
             (fun (name, spec_field) -> name, js_extract rec_specs spec_field)
             fields)
         constructors_non_cst in
     (fun js ->
       if some js = null || typeof js = Extract.str_string then (
         let c =
           match Extract.as_option js with
           | None -> "null"
           | Some js -> Extract.as_string js in
         let i_ref = ref 0 in
         Array.iteri (* TODO: compute hashtable for this *)
           (fun i constr ->
             if constr = c then i_ref := i)
           constructors_cst;
         Obj.repr !i_ref
       ) else (
         let c = Extract.(as_string (get js "type")) in
         let tag, fields_extract =
           let i_ref = ref 0 in
           let f_ref = ref [| |] in
           Array.iteri
             (fun i (constr,fields_extract) ->
               if constr = c then (
                 i_ref := i; f_ref := fields_extract
             ))
             constructors_non_cst_extract;
           !i_ref, !f_ref in
         let bl = Obj.new_block tag (Array.length fields_extract) in
         Array.iteri
           (fun i (name,extract_field) ->
             Obj.set_field bl i (extract_field (Extract.get js name)))
           fields_extract;
         bl
     ))
  | `Enum constr_names ->
     js_extract rec_specs (sum_spec_of_enum constr_names)
  | `Option spec_contents ->
     let extract_contents = js_extract rec_specs spec_contents in
     (fun js ->
       let opt =
         match Extract.as_option js with
         | None -> None
         | Some js_c -> Some (extract_contents js_c) in
       Obj.repr opt)
  | `Custom { extract } -> extract
  | `Rec name ->
     let rec_spec = try List.assoc name rec_specs with _ -> assert false in
     (fun js -> js_extract rec_specs rec_spec js)
  | `Abstract -> invalid_arg "Jsutils.js_extract: abstract"

let js_map ?(rec_specs : (string * js_map_spec) list = []) (spec : js_map_spec) : 'a js_map =
  let rec_specs = ("self",spec)::rec_specs in
  let inject = js_inject rec_specs spec in
  let extract = js_extract rec_specs spec in
  { spec;
    inject = (fun x -> inject (Obj.repr x));
    extract = (fun r -> Obj.obj (extract r)) }

let js_custom_map (map : 'a js_map) : Obj.t js_map =
  { spec = map.spec;
    inject = (fun r -> map.inject (Obj.obj r));
    extract = (fun js -> Obj.repr (map.extract js)) }
let js_custom_spec map = `Custom (js_custom_map map)

let js_map_log (prefix : string) (map : 'a js_map) (l : 'a list) : unit =
  List.iter
    (fun x ->
      Firebug.console##log_2 (string prefix) (map.inject x))
    l
                       
(* YASGUI bindings *)

let opt_iter (opt : 'a option) (k : 'a -> unit) : unit =
  match opt with
  | Some x -> k x
  | None -> ()
    
let yasgui =
object (self)
  val mutable this_opt = None

  method init =
    let constr_YASGUI = Unsafe.global##.YASGUI in
    try this_opt <- Some (new%js constr_YASGUI (Dom_html.getElementById "sparklis-yasgui"))
    with exn ->
      firebug ("yasgui#init: " ^ Printexc.to_string exn);
      alert ("Warning: YASGUI could not be initialized for some reason. SPARQL queries will be displayed only as text.");
      this_opt <- None

  method set_corsProxy (url_opt : string option) : unit =
    match this_opt with
    | None -> ()
    | Some yasgui ->
       yasgui##.options##.api##.corsProxy :=
	 (match url_opt with None -> null | Some url -> some (string url))

  method private yasqe yasgui = yasgui##current##.yasqe
  method private yasr yasgui = yasgui##current##.yasr

  method set_endpoint (endpoint : string) : unit =
    match this_opt with
    | None -> ()
    | Some yasgui ->
      let yasqe = self#yasqe yasgui in
      yasqe##.options##.sparql##.endpoint := string endpoint;
      jquery_set_innerHTML ".yasgui .endpointText .item" endpoint

  method set_requestMethod (meth : [`GET | `POST]) : unit =
    match this_opt with
    | None -> ()
    | Some yasgui ->
      let yasqe = self#yasqe yasgui in
      yasqe##.options##.sparql##.requestMethod := string (match meth with `GET -> "GET" | `POST -> "POST")

  method set_query (sparql : string) : unit =
    match this_opt with
    | None ->
      let html = "<xmp>" ^ sparql ^ "</xmp>" in
      jquery_set_innerHTML "#sparql-query" html
    | Some yasgui ->
      let yasqe = self#yasqe yasgui in
      yasqe##setValue (string sparql)

  method set_response (resp : string) : unit =
    match this_opt with
    | None -> ()
    | Some yasgui ->
      let yasr = self#yasr yasgui in
      yasr##setResponse (string resp)

  method refresh : unit =
    match this_opt with
    | None -> ()
    | Some yasgui ->
      let yasqe = self#yasqe yasgui in
      let yasr = self#yasr yasgui in
      yasqe##setValue (yasqe##getValue);
      yasr##draw
end

(* Google charts bindings *)
  
let google =
object
  method set_on_load_callback : 'a. (unit -> 'a) -> 'a = fun k ->
    let g = Unsafe.global##.google in
    if g = Js.undefined
    then k ()
    else (
      let k () =
	firebug "Loaded document and google charts";
	k () in
      g##.charts##setOnLoadCallback (wrap_callback k)
    )
      
  method draw_map (points : (float * float * string) list) (elt_map : Dom_html.element t) : unit =
    let g = Unsafe.global##.google in
    if g = Js.undefined
    then ()
    else (
    firebug "Drawing map";
    let constr_Map = Unsafe.global##.google##.visualization##.Map in  
    let map = new%js constr_Map elt_map in
    let table =
      let data =
	let col t = Inject.(obj [| "type", string t |]) in
	let row lat long name =
	  let cell v = Inject.(obj [| "v", v |]) in
	  Inject.(obj [| "c", array [| cell (float lat); cell (float long); cell (string name) |] |]) in
	Inject.(obj [| 
	  "cols", array [| col "number"; col "number"; col "string" |];
	  "rows", array (Array.of_list (List.map (fun (lat,long,name) -> row lat long name) points)) |]) in
      let constr_DataTable = Unsafe.global##.google##.visualization##.DataTable in
      new%js constr_DataTable data in
    let options = Inject.(obj [|
      "showTooltip", bool true;
      "showInfoWindow", bool true;
      "useMapTypeControl", bool true;
      "icons",
      obj [| "default",
	     obj [| "normal",
		    string "http://maps.google.com/mapfiles/ms/icons/red-dot.png";

		    "selected",
		    string "http://maps.google.com/mapfiles/ms/icons/blue-dot.png" |] |] |]) in
    let _ = map##draw table options in
    firebug "Drawed the map"
    )

end

(* Wikidata services *)
module Wikidata =
  struct
    let entities_of_json ojson : string list option =
      try
	let oquery = Unsafe.get ojson (string "query") in
	let osearch = Unsafe.get oquery (string "search") in
	let n = truncate (to_float (Unsafe.get osearch (string "length"))) in
	let le = ref [] in
	for i = n-1 downto 0 do
	  let oresult = Unsafe.get osearch (string (string_of_int i)) in
	  let otitle = Unsafe.get oresult (string "title") in
	  le := (Js.to_string otitle)::!le
	done;
	firebug (string_of_int n ^ " wikidata entities found");
	Some !le
      with _ ->
	None

    let ajax_entity_search (query : string) (limit : int) (k : string list option -> unit) : unit =
      if String.length query < 3
      then k None
      else
	let _ = firebug ("Wikidata search: " ^ query) in
	let query_url =
	  Printf.sprintf
	    "https://www.wikidata.org/w/api.php?action=query&list=search&format=json&srlimit=%d&srsearch=%s"
	    (*"https://www.wikidata.org/w/api.php?action=wbsearchentities&format=json&language=en&limit=%d&search=%s" (* type=item|property *) NOTE: less flexible search *)
	    limit
	    (Url.urlencode query) in
	Lwt.ignore_result
	  (Lwt.bind
	     (Jsonp.call_custom_url (*~timeout:0.5*)
		(fun name -> query_url ^ "&callback=" ^ name))
	     (fun json ->
	      k (entities_of_json json);
	      Lwt.return ()))
	
  end


(* Fuseki services *)

let lucene_query_of_kwds ?(op = `All) kwds =
  let terms =
    Common.mapfilter
      (fun kwd ->
       let n = String.length kwd in
       if n < 3 then None
       else if kwd.[n-1] = '~' then Some kwd
       else Some (kwd ^ "*"))
      kwds in
  let lucene_query =
    let sep = match op with `All -> " AND " | `Any -> " OR " in
    match terms with
    | [] -> ""
    | [term] -> term
    | _ -> "(" ^ String.concat sep terms ^ ")" in
  let _ = firebug ("Lucene query: " ^ lucene_query) in
  lucene_query
