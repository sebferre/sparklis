
open Js
open Jsutils

(* templates *)

class virtual input =
object
  val mutable endpoint : string = ""
  val mutable has_changed : bool = false
  method set_endpoint (url : string) : unit = endpoint <- url
  method virtual get_permalink : (string * string) list
  method virtual set_permalink : (string * string) list -> unit
  method has_changed : bool = has_changed
  method reset_changed : unit = has_changed <- false
  method virtual init : unit
  method virtual reset : unit
end

class boolean_input ~(key : string) ~(input_selector : string) ~default () =
object (self)
  inherit input
  val mutable init_v : bool = default
  val mutable current_v : bool = default

  method set_value (v : bool) : unit =
    if v <> current_v then begin
      jquery_input input_selector (fun input -> input##checked <- bool v);
      current_v <- v;
      has_changed <- true
    end

  method value : bool = current_v

  method get_permalink =
    if current_v <> init_v
    then [(key, string_of_bool current_v)]
    else []
  method set_permalink args =
    try self#set_value (bool_of_string (List.assoc key args))
    with _ -> ()

  method init =
    jquery_input input_selector (fun input ->
      init_v <- to_bool input##checked; (* default value from HTML *)
      current_v <- init_v;
      onclick
	(fun input ev ->
	  let v = to_bool input##checked in
	  if v <> current_v then begin
	    current_v <- v;
	    has_changed <- true
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
      jquery_input input_selector (fun input -> input##value <- string (string_of_int v));
      current_v <- v;
      has_changed <- true
    end

  method value : int = current_v

  method get_permalink =
    if current_v <> init_v
    then [(key, string_of_int current_v)]
    else []
  method set_permalink args =
    try self#set_input (int_of_string (List.assoc key args))
    with _ -> ()

  method init =
    jquery_input input_selector (fun input ->
      init_v <- (match integer_of_input ?min ?max input with Some v -> v | None -> default); (* default value from HTML *)
      current_v <- init_v;
      oninput
	(fun input ev ->
	  match integer_of_input ?min ?max input with
	    | Some v ->
	      input##style##color <- string "black";
	      if current_v <> v then begin
		current_v <- v;
		has_changed <- true
	      end
	    | None ->
	      input##style##color <- string "red")
	input;
      onchange
	(fun input ev ->
	  input##value <- string (string_of_int current_v);
	  input##style##color <- string "black")
	input)
  method reset = self#set_input init_v
end


class string_input ~(key : string) ~(input_selector : string) ~default () =
object (self)
  inherit input
  val mutable init_v : string = default (* default value for reset *)
  val mutable current_v : string = default (* current value *)

  method private set_input (v : string) : unit =
    if v <> current_v then begin
      jquery_input input_selector (fun input -> input##value <- string v);
      current_v <- v;
      has_changed <- true
    end

  method value : string = current_v

  method get_permalink =
    if current_v <> init_v
    then [(key, current_v)]
    else []
  method set_permalink args =
    try self#set_input (List.assoc key args)
    with _ -> ()

  method init =
    jquery_input input_selector (fun input ->
      init_v <- to_string input##value; (* default value from HTML *)
      current_v <- init_v;
      oninput
	(fun input ev ->
	  let v = to_string input##value in
	  if current_v <> v then begin
	    current_v <- v;
	    has_changed <- true
	  end)
	input)
  method reset = self#set_input init_v
end
