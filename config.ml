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
       
open Js
open Jsutils

(* templates *)

class virtual input =
object
  val mutable endpoint : string = ""
  val mutable has_changed : bool = false
  val mutable callbacks : (unit -> unit) list = []
  method set_endpoint (url : string) : unit = endpoint <- url
  method on_change callback = callbacks <- callback::callbacks
  method private changed = has_changed <- true; List.iter (fun callback -> callback ()) callbacks
  method has_changed : bool = has_changed
  method reset_changed : unit = has_changed <- false
  method virtual init : unit
  method virtual reset : unit
  method virtual get_permalink : (string * string) list
  method virtual set_permalink : (string * string) list -> unit
end

class boolean_input ~(key : string) ~(input_selector : string) ~default () =
object (self)
  inherit input
  val mutable init_v : bool = default
  val mutable current_v : bool = default

  method set_value (v : bool) : unit =
    if v <> current_v then begin
      jquery_input input_selector (fun input -> input##.checked := bool v);
      current_v <- v;
      self#changed
    end

  method value : bool = current_v

  method get_permalink =
    if current_v <> default
    then [(key, string_of_bool current_v)]
    else []
  method set_permalink args =
    self#set_value (try bool_of_string (List.assoc key args) with _ -> default)

  method init =
    jquery_input input_selector (fun input ->
      init_v <- to_bool input##.checked; (* default value from HTML *)
      current_v <- init_v;
      onclick
	(fun input ev ->
	  let v = to_bool input##.checked in
	  if v <> current_v then begin
	    current_v <- v;
	    self#changed
	  end)
	input)
  method reset = self#set_value init_v
end

class integer_input ~(key : string) ~(input_selector : string) ?min ?max ~default () =
object (self)
  inherit input
  val mutable init_v : int = default (* default value for reset *)
  val mutable current_v : int = default (* current value *)

  method private set_input (v : int) : unit =
    if v <> current_v then begin
      jquery_input input_selector (fun input -> input##.value := string (string_of_int v));
      current_v <- v;
      self#changed
    end

  method value : int = current_v

  method get_permalink =
    if current_v <> default
    then [(key, string_of_int current_v)]
    else []
  method set_permalink args =
    self#set_input (try int_of_string (List.assoc key args) with _ -> default)

  method init =
    jquery_input input_selector (fun input ->
      init_v <- (match integer_of_input ?min ?max input with Some v -> v | None -> default); (* default value from HTML *)
      current_v <- init_v;
      oninput
	(fun input ev ->
	  match integer_of_input ?min ?max input with
	    | Some v ->
	      input##.style##.color := string "black";
	      if current_v <> v then begin
		current_v <- v;
		self#changed
	      end
	    | None ->
	      input##.style##.color := string "red")
	input;
      onchange
	(fun input ev ->
	  input##.value := string (string_of_int current_v);
	  input##.style##.color := string "black")
	input)
  method reset = self#set_input init_v
end


class string_input ~(key : string) ~(input_selector : string) ~default () =
(* only requires a ##value property at [input_selector] *)
object (self)
  inherit input
  val mutable init_v : string = default (* default value for reset *)
  val mutable current_v : string = default (* current value *)

  method private set_input (v : string) : unit =
    if v <> current_v then begin
      jquery_input input_selector (fun input -> input##.value := string v);
      current_v <- v;
      self#changed
    end

  method value : string = current_v

  method get_permalink =
    if current_v <> default
    then [(key, current_v)]
    else []
  method set_permalink args =
    self#set_input (try List.assoc key args with _ -> default)

  method init =
    jquery_input input_selector (fun input ->
      init_v <- to_string input##.value; (* default value from HTML *)
      current_v <- init_v;
      oninput
	(fun input ev ->
	  let v = to_string input##.value in
	  if current_v <> v then begin
	    current_v <- v;
	    self#changed
	  end)
	input)
  method reset = self#set_input init_v
end

class select_input ~(key : string) ~(select_selector : string) ~default () =
object (self)
  inherit input
  val mutable init_v : string = default (* default value for reset *)
  val mutable current_v : string = default (* current value *)

  method private set_select (v : string) : unit =
    if v <> current_v then begin
      jquery_select select_selector
		    (fun select -> select##.value := string v);
      current_v <- v;
      self#changed
    end

  method value : string = current_v

  method get_permalink =
    if current_v <> default
    then [(key, current_v)]
    else []
  method set_permalink args =
    self#set_select (try List.assoc key args with _ -> default)

  method init =
    jquery_select select_selector (fun select ->
      init_v <- to_string select##.value; (* default value from HTML *)
      current_v <- init_v;
      onchange
	(fun select ev ->
	  let v = to_string select##.value in
	  if current_v <> v then begin
	    current_v <- v;
	    self#changed
	  end)
	select)
  method reset = self#set_select init_v
end

  
(* JS object for Sparklis extension *)

type hook = Unsafe.top optdef (* optionally defined ('a -> Promise('a or undefined, error)) functions on JS objects, which can be used to add side effects and to modify the data back into Sparklis *)

let apply_hook_opt (what : string) (hook : hook) (js_args : Unsafe.any array) (k : Unsafe.any option -> unit) : unit =
  Optdef.case hook
    (fun () -> k None) (* if hook undefined *)
    (fun callback ->
      Jsutils.firebug ("applying hook for " ^ what);
      Jsutils.promise_then
        (Unsafe.fun_call callback js_args)
        (fun js_res ->
          if js_res = Jsutils.Inject.undefined
          then k None (* undefined result (side-effect only extension) *)
          else k (Some js_res))
        (fun js_error -> (* catching any error thrown by callback *)
          Firebug.console##log js_error; (* logging the error *)
          k None)) (* and falling back to default behavior *)

(* apply a hook, if defined, to some Sparklis data [x], given functions for injection to and extraction from JS objects. *)
let apply_hook_data (what : string) (hook : hook) (map : 'a js_map) (x : 'a) (k : 'a -> unit) : unit =
  Optdef.case hook
    (fun () -> k x) (* identity if hook undefined *)
    (fun callback ->
      Jsutils.firebug ("applying hook on " ^ what);
      let js_x = map.inject x in
      (* Firebug.console##log_2 (string "BEFORE hook: ") js_x; *)
      Jsutils.promise_then
        (Unsafe.fun_call callback [|js_x|])
        (fun js_y ->
          if js_y = Jsutils.Inject.undefined
          then (
            (* Jsutils.firebug "AFTER hook: undefined"; *)
            k x) (* use original result if undefined result (side-effect only extension) *)
          else (
            (* Firebug.console##log_2 (string "AFTER hook: ") js_y; *)
            let y = map.extract js_y in
            k y))
        (fun js_error -> (* catching any error thrown by callback *)
          Firebug.console##log js_error; (* logging the error *)
          k x)) (* and falling back to default data *)

let sparklis_extension =
  object%js (self)
    val mutable hookSparql : hook = undefined (* data: string (SPARQL query) *)
    val mutable hookResults : hook = undefined (* data : Sparql_endpoint.results *)
    val mutable hookSuggestions : hook = undefined (* data: Lis.freq_unit * Lis.suggestions *)
    val mutable hookApplySuggestion : hook = undefined (* place -> increment -> place *)
  end
let () = Js.export "sparklis_extension" sparklis_extension
