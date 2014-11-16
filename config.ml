
open Js
open Jsutils

(* templates *)

class virtual config_input =
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
  inherit config_input
  val mutable init_v : bool = default
  val mutable current_v : bool = default

  method private set_input (v : bool) : unit =
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
    try self#set_input (bool_of_string (List.assoc key args))
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
  method reset = self#set_input init_v
end

class integer_input ~(key : string) ~(input_selector : string) ?min ?max ~default () =
object (self)
  inherit config_input
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

class ['lexicon] lexicon_input ~(key : string)
  ~select_selector ~input_selector ~lang_input_selector
  ~default_lexicon ~custom_lexicon () =
  let other = "other" in
  let key_select = key ^ "_select" in
  let key_property = key ^ "_property" in
  let key_lang = key ^ "_lang" in
object (self)
  inherit config_input as super
  val mutable init_select = ""
  val mutable init_property = ""
  val mutable init_lang = ""
  val mutable current_select = ""
  val mutable current_property = ""
  val mutable current_lang = ""
  val mutable current_lexicon = default_lexicon

  method private get_select_property_lang select input lang_input =
    let sel = to_string select##value in
    let property = if sel = other then to_string (input##value) else sel in
    let lang = to_string (lang_input##value) in
    sel, property, lang

  method private set_select_property_lang s p l =
    if current_property <> p || current_lang <> l then begin
      jquery_select select_selector (fun select -> select##value <- string s);
      jquery_input input_selector (fun input -> input##value <- string (if s = other then p else ""));
      jquery_input lang_input_selector (fun input -> input##value <- string l);
      current_select <- s;
      current_property <- p;
      current_lang <- l;
      has_changed <- true;
      self#define_lexicon
    end

  method private define_lexicon : unit =
    current_lexicon <-
      if current_property = ""
      then default_lexicon
      else custom_lexicon ~endpoint
	~property:current_property
	?language:(if current_lang = "" then None else Some current_lang) ()

  method private change_lexicon select input lang_input : unit =
    let s, p, l = self#get_select_property_lang select input lang_input in
    if p <> current_property || l <> current_lang then begin
      current_select <- s;
      current_property <- p;
      current_lang <- l;
      has_changed <- true;
      self#define_lexicon
    end

  method set_endpoint url =
    super#set_endpoint url;
    self#define_lexicon

  method get_permalink =
    if current_property <> init_property || current_lang <> init_lang
    then
      let args = if current_lang = "" then [] else [(key_lang, current_lang)] in
      if current_select = other
      then (key_property, current_property) :: args
      else (key_select, current_select) :: args
    else []
  method set_permalink args =
    try
      let s = try List.assoc key_select args with _ -> other in
      let p = if s = other then List.assoc key_property args else s in
      let l = try List.assoc key_lang args with _ -> "" in
      self#set_select_property_lang s p l
    with _ -> ()

  method value : 'lexicon = current_lexicon

  method init =
    jquery_select select_selector (fun select ->
      jquery_input input_selector (fun input ->
	jquery_input lang_input_selector (fun lang_input ->
	  (* default values from HTML *)
	  let s, p, l = self#get_select_property_lang select input lang_input in
	  if s <> other then input##style##display <- string "none";
	  init_select <- s;
	  init_property <- p;
	  init_lang <- l;
	  (* definition of current values *)
	  current_select <- init_select;
	  current_property <- init_property;
	  current_lang <- init_lang;
	  self#define_lexicon;
	  (* callbacks on changes/inputs *)
	  onchange
	    (fun _ ev ->
	      if to_string select##value <> other
	      then begin
		input##style##display <- string "none";
		self#change_lexicon select input lang_input end
	      else
		input##style##display <- string "inline")
	    select;
	  oninput (fun _ ev -> self#change_lexicon select input lang_input) input;
	  oninput (fun _ ev -> self#change_lexicon select input lang_input) lang_input)))
  method reset = self#set_select_property_lang init_select init_property init_lang
end

(* configuration *)

let logging = new boolean_input ~key:"logging" ~input_selector:"#input-logging" ~default:true ()

let max_results = new integer_input ~key:"max_results" ~input_selector:"#input-max-results" ~min:1 ~default:200 ()
let max_classes = new integer_input ~key:"max_classes" ~input_selector:"#input-max-classes" ~min:0 ~default:200 ()
let max_properties = new integer_input ~key:"max_properties" ~input_selector:"#input-max-properties" ~min:0 ~default:200 ()

let entity_lexicon =
  new lexicon_input
    ~key:"entity_lexicon"
    ~select_selector:"#config-label-entity-select"
    ~input_selector:"#config-label-entity-input"
    ~lang_input_selector:"#config-label-entity-input-lang"
    ~default_lexicon:Lexicon.default_entity_lexicon
    ~custom_lexicon:Lexicon.sparql_entity_lexicon
    ()
let class_lexicon =
  new lexicon_input
    ~key:"class_lexicon"
    ~select_selector:"#config-label-class-select"
    ~input_selector:"#config-label-class-input"
    ~lang_input_selector:"#config-label-class-input-lang"
    ~default_lexicon:Lexicon.default_class_lexicon
    ~custom_lexicon:Lexicon.sparql_class_lexicon
    ()
let property_lexicon =
  new lexicon_input
    ~key:"property_lexicon"
    ~select_selector:"#config-label-property-select"
    ~input_selector:"#config-label-property-input"
    ~lang_input_selector:"#config-label-property-input-lang"
    ~default_lexicon:Lexicon.default_property_lexicon
    ~custom_lexicon:Lexicon.sparql_property_lexicon
    ()


let config =
  let config_inputs : config_input list =
    [ (logging :> config_input);
      (max_results :> config_input); (max_classes :> config_input); (max_properties :> config_input);
      (entity_lexicon :> config_input); (class_lexicon :> config_input); (property_lexicon :> config_input) ] in
object (self)
(*
  val mutable inputs : config_input list = []

  method add_input input = inputs <- input :: inputs
*)

  method logging = logging#value
  method max_results = max_results#value
  method max_classes = max_classes#value
  method max_properties = max_properties#value
  method entity_lexicon = entity_lexicon#value
  method class_lexicon = class_lexicon#value
  method property_lexicon = property_lexicon#value

  method set_endpoint (endpoint : string) : unit = List.iter (fun input -> input#set_endpoint endpoint) config_inputs

  method get_permalink : (string * string) list =
    List.concat (List.map (fun input -> input#get_permalink) config_inputs)
  method set_permalink (args : (string * string) list) : unit =
    List.iter (fun input -> input#set_permalink args) config_inputs

  method if_has_changed (f : unit -> unit) : unit =
    let has_changed = List.exists (fun input -> input#has_changed) config_inputs in
    if has_changed then begin
      List.iter (fun input -> input#reset_changed) config_inputs;
      f ()
    end

  method init endpoint args =
    self#set_endpoint endpoint;
    List.iter (fun input -> input#init) config_inputs;
    self#set_permalink args;
    jquery "#config-reset-button" (onclick (fun elt ev ->
      List.iter (fun input -> input#reset) config_inputs))
end
