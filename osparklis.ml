
open Js
open Jsutils
open Html

(* logging utilities *)

let config_logging = new Config.boolean_input ~key:"logging" ~input_selector:"#input-logging" ~default:true ()

let is_dev_version : bool = (* flag at TRUE if this is the dev version that is running *)
  Url.Current.path_string = "/home/ferre/prog/ajax/sparklis/osparklis.html"

let logging_on () = not is_dev_version && config_logging#value

let url_log_php = (* http://www.irisa.fr/LIS/ferre/sparklis/log/log.php *)
  Common.unobfuscate_string "\023\011\011\015EPP\b\b\bQ\022\r\022\012\030Q\025\rP36,P\025\026\r\r\026P\012\015\030\r\020\019\022\012P\019\016\024P\019\016\024Q\015\023\015"

let url_querylog_php = (* "http://www.irisa.fr/LIS/ferre/sparklis/log/querylog.php" *)
  Common.unobfuscate_string "\023\011\011\015EPP\b\b\bQ\022\r\022\012\030Q\025\rP36,P\025\026\r\r\026P\012\015\030\r\020\019\022\012P\019\016\024P\014\n\026\r\006\019\016\024Q\015\023\015"

let session_id : string = (* random session ID to disambiguate undefinite IPs *)
  Random.self_init (); string_of_int (Random.int 1000000000);;

(* LISQL constraints <--> user patterns *)

let string_is_float =
  let re = Regexp.regexp "^[+-]?(\\d+|\\d*[.]\\d+|\\d+[.]\\d*[eE][+-]?\\d+|[.]\\d+[eE][+-]?\\d+|\\d+[eE][+-]?\\d+)$" in
  (fun s -> Regexp.string_match re s 0 <> None)

let make_constr op pat =
  let open Lisql in
  let lpat = List.filter ((<>) "") (Regexp.split (Regexp.regexp "[ ]+") pat) in
  match op, lpat with
  | "matchesAll", _ -> MatchesAll lpat
  | "matchesAny", _ -> MatchesAny lpat
  | "after", [] -> After ""
  | "after", pat::_ -> After pat
  | "before", [] -> Before ""
  | "before", pat::_ -> Before pat
  | "fromTo", [] -> FromTo ("","")
  | "fromTo", pat1::[] -> FromTo (pat1, "")
  | "fromTo", pat1::pat2::_ -> FromTo (pat1,pat2)
  | "higherThan", [] -> HigherThan ""
  | "higherThan", pat::_ ->
    if string_is_float pat 
    then HigherThan pat
    else invalid_arg "a numeric value is expected"
  | "lowerThan", [] -> LowerThan ""
  | "lowerThan", pat::_ ->
    if string_is_float pat
    then LowerThan pat
    else invalid_arg "a numeric value is expected"
  | "between", [] -> Between ("","")
  | "between", pat::[] ->
    if string_is_float pat
    then Between (pat, "") (* HigherThan pat *)
    else invalid_arg "a numeric value is expected"
  | "between", pat1::pat2::_ ->
    if string_is_float pat1 && string_is_float pat2
    then Between (pat1, pat2)
    else invalid_arg "two numeric values are expected"
  | "hasLang", [] -> HasLang ""
  | "hasLang", pat::_ -> HasLang pat
  | "hasDatatype", [] -> HasDatatype ""
  | "hasDatatype", pat::_ -> HasDatatype pat
  | _ -> assert false

let norm_constr = (* normalizing for empty patterns "" *)
  (* must be called for any semantic use of constraints *)
  let open Lisql in
  function
  | MatchesAll [] -> True
  | MatchesAny [] -> True
  | After "" -> True
  | Before "" -> True
  | FromTo ("","") -> True
  | FromTo ("",b) -> Before b
  | FromTo (a,"") -> After a
  | HigherThan "" -> True
  | LowerThan "" -> True
  | Between ("","") -> True
  | Between ("",b) -> LowerThan b
  | Between (a,"") -> HigherThan a
  | HasLang "" -> True
  | HasDatatype "" -> True
  | c -> c

let operator_of_constr =
  let open Lisql in
  function
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

let pattern_of_constr =
  let open Lisql in
  function
  | True -> ""
  | MatchesAll lpat -> String.concat " " lpat
  | MatchesAny lpat -> String.concat " " lpat
  | After pat -> pat
  | Before pat -> pat
  | FromTo (pat1,"") -> pat1
  | FromTo (pat1,pat2) -> pat1 ^ " " ^ pat2
  | HigherThan pat -> pat
  | LowerThan pat -> pat
  | Between (pat1,"") -> pat1
  | Between (pat1,pat2) -> pat1 ^ " " ^ pat2
  | HasLang pat -> pat
  | HasDatatype pat -> pat

(* constraint compilation *)

let regexp_of_pat pat = Regexp.regexp_with_flag (Regexp.quote pat) "i"
let matches s re = Regexp.search re s 0 <> None
let leq s1 s2 = try (float_of_string s1) <= (float_of_string s2) with _ -> false

let compile_constr constr : string -> bool =
  let open Lisql in
  match norm_constr constr with
  | True -> (fun s -> true)
  | MatchesAll lpat ->
    let lre = List.map regexp_of_pat lpat in
    (fun s -> List.for_all (fun re -> matches s re) lre)
  | MatchesAny lpat ->
    let lre = List.map regexp_of_pat lpat in
    (fun s -> List.exists (fun re -> matches s re) lre)
  | After pat -> (fun s -> s >= pat)
  | Before pat -> (fun s -> s <= pat)
  | FromTo (pat1,pat2) -> (fun s -> pat1 <= s && s <= pat2)
  | HigherThan pat -> (fun s -> leq pat s)
  | LowerThan pat -> (fun s -> leq s pat)
  | Between (pat1,pat2) -> (fun s -> leq pat1 s && leq s pat2)
  | HasLang pat ->
    let re = regexp_of_pat pat in
    (fun s_lang -> matches s_lang re)
  | HasDatatype pat ->
    let re = regexp_of_pat pat in
    (fun s_dt -> matches s_dt re)
      
(* constraint subsumption *)

let subsumed_constr constr1 constr2 : bool =
  (* must avoid to return true when false, but can return false when true *)
  let open Lisql in
  match constr1, constr2 with
  | _, True -> true
  | MatchesAll ls1, MatchesAll ls2 ->
    List.for_all (fun s2 ->
      List.exists (fun s1 ->
	Common.has_prefix s1 s2 (* 'has_prefix' used as an approximation of 'contains' *)
      ) ls1
    ) ls2
  | MatchesAny ls1, MatchesAny ls2 ->
    List.for_all (fun s1 ->
      List.exists (fun s2 ->
	Common.has_prefix s1 s2
      ) ls2
    ) ls1
  | After s1, After s2 -> s2 <= s1
  | Before s1, Before s2 -> s1 <= s2
  | FromTo (s1a,s1b), FromTo (s2a,s2b) -> (s2a="" || s2a <= s1a) && (s2b="" || s1b <= s2b)
  | HigherThan s1, HigherThan s2 -> leq s2 s1
  | LowerThan s1, LowerThan s2 -> leq s1 s2
  | Between (s1a,s1b), Between (s2a,s2b) -> (s2a="" || leq s2a s1a) && (s2b="" || leq s1b s2b)
  | HasLang s1, HasLang s2 -> Common.has_prefix s1 s2
  | HasDatatype s1, HasDatatype s2 -> Common.has_prefix s1 s2
  | _ -> false


(* input checking *)

let check_input s = function
  | `IRI -> true
  | `String -> true
  | `Float -> Regexp.string_match (Regexp.regexp "[-+]?\\d+([.]\\d*)?([eE][-+]?\\d+)?$") s 0 <> None
  (*  | `Decimal -> Regexp.string_match (Regexp.regexp "[-+]?\\d+([.]\\d* )?$") s 0 <> None *)
  | `Integer -> Regexp.string_match (Regexp.regexp "[-+]?\\d+$") s 0 <> None
  | `Date -> Regexp.string_match (Regexp.regexp "[-+]?\\d+-\\d{2}-\\d{2}$") s 0 <> None
  | `Time -> Regexp.string_match (Regexp.regexp "\\d{2}:\\d{2}:\\d{2}(Z|[-+]\\d{2}(:\\d{2})?)?$") s 0 <> None
  | `DateTime -> Regexp.string_match (Regexp.regexp "[-+]?\\d+-\\d{2}-\\d{2}T\\d{2}:\\d{2}:\\d{2}(Z|[-+]\\d{2}(:\\d{2})?)?$") s 0 <> None
    
(* configuration *)

let config =
  let config_inputs : Config.input list =
    [ (Sparql_endpoint.config_proxy :> Config.input);
      (Sparql_endpoint.config_proxy_url :> Config.input);
      (Sparql_endpoint.config_method_get :> Config.input);
      (Sparql_endpoint.config_withCredentials :> Config.input);
      (Sparql_endpoint.config_caching :> Config.input);
      (Lis.config_intentional_init_concepts :> Config.input);
      (Lis.config_max_results :> Config.input);
      (Lis.config_max_classes :> Config.input);
      (Lis.config_max_properties :> Config.input);
      (Lexicon.config_entity_lexicon :> Config.input);
      (Lexicon.config_class_lexicon :> Config.input);
      (Lexicon.config_property_lexicon :> Config.input);
      (Lisql2nl.config_lang :> Config.input);
      (Lisql2nl.config_show_datatypes :> Config.input);
      (config_logging :> Config.input); ] in
object (self)
  method set_endpoint (endpoint : string) : unit =
    Sparql_endpoint.config_proxy#set_value false; (* no proxy by default *)
    List.iter (fun input -> input#set_endpoint endpoint) config_inputs;
    Jsutils.yasgui#set_endpoint endpoint

  method get_permalink : (string * string) list =
    List.concat (List.map (fun input -> input#get_permalink) config_inputs)
  method set_permalink (args : (string * string) list) : unit =
    List.iter (fun input -> input#set_permalink args) config_inputs

  method private set_yasgui_options =
    Jsutils.yasgui#set_corsProxy
      (if Sparql_endpoint.config_proxy#value then Some Sparql_endpoint.config_proxy_url#value else None);
    Jsutils.yasgui#set_requestMethod
      (if Sparql_endpoint.config_method_get#value then `GET else `POST)

  method if_has_changed ~(translate : unit -> unit) ~(refresh : unit -> unit) : unit =
    let has_changed = List.exists (fun input -> input#has_changed) config_inputs in
    if has_changed then begin
      if Lisql2nl.config_lang#has_changed then translate ();
      self#set_yasgui_options;
      refresh ();
      List.iter (fun input -> input#reset_changed) config_inputs
    end

  method init endpoint args =
    self#set_endpoint endpoint;
    List.iter (fun input -> input#init) config_inputs;
    self#set_permalink args;
    self#set_yasgui_options;
    jquery "#config-reset-button" (onclick (fun elt ev ->
      List.iter (fun input -> input#reset) config_inputs));
    jquery "#button-clear-cache" (onclick (fun elt ev -> Sparql_endpoint.cache#clear))
end

(* navigation place and history *)

class navigation =
object
  method change_endpoint (url : string) : unit = ()
  method update_focus ~(push_in_history : bool) (f : Lisql.focus -> Lisql.focus option) : unit = ()
end

class place (endpoint : string) (foc : Lisql.focus) =
object (self)
  val lis = new Lis.place endpoint foc
  method lis = lis

  val mutable offset = 0
  val mutable limit = 10

  val mutable term_constr = Lisql.True
  val mutable property_constr = Lisql.True

  val mutable navigation = new navigation
  method set_navigation (navig : navigation) = navigation <- navig

  val mutable html_state = new Html.state (new Lisql2nl.id_labelling [])

  method show_permalink : unit =
    let args = config#get_permalink in
    let args =
      if self#is_home
      then ("endpoint", lis#endpoint) :: args
      else ("endpoint", lis#endpoint) :: ("query", Permalink.of_query lis#query) :: args in
    try
      let permalink_url =
	match Url.Current.get () with
	  | None -> raise Not_found
	  | Some (Url.Http url) -> Url.Http { url with Url.hu_arguments = args }
	  | Some (Url.Https url) -> Url.Http { url with Url.hu_arguments = args }
	  | Some (Url.File url) -> Url.File { url with Url.fu_arguments = args } in
      ignore
	(prompt
	   Lisql2nl.config_lang#grammar#msg_permalink
	   (Url.string_of_url permalink_url))
    with _ -> ()

  method private refresh_lisql =
    jquery "#lisql" (fun elt ->
      elt##innerHTML <- string (html_query html_state lis#query);
      stop_links_propagation_from elt;
      jquery_all_from elt ".focus" (onclick (fun elt_foc ev ->
	Dom_html.stopPropagation ev;
	navigation#update_focus ~push_in_history:false (fun _ ->
	  let key = to_string (elt_foc##id) in
	  Some (html_state#get_focus key))));
      jquery_from elt "#delete-current-focus"
	(onclick (fun elt_button ev ->
	  Dom_html.stopPropagation ev;
	  navigation#update_focus ~push_in_history:true Lisql.delete_focus)))

  method private refresh_increments_focus =
    let html_focus =
      match lis#focus_term_list with
	| [Rdf.Var v] ->
	  (try
	    let id = lis#id_labelling#get_var_id v in
	    Html.html_id html_state id
	   with _ -> escapeHTML v (* should not happen *))
	| [t] -> Html.html_term t
	| _ -> Lisql2nl.config_lang#grammar#undefined in
    jquery "#increments-focus" (fun elt ->
      elt##innerHTML <- string html_focus)

  method private get_constr (select : Dom_html.selectElement t) (input : Dom_html.inputElement t) =
    let op = to_string (select##value) in
    let pat = to_string (input##value) in
    make_constr op pat

  method private refresh_constrs =
    List.iter
      (fun (sel_select, sel_input, constr) ->
	jquery_select sel_select (fun select ->
	  jquery_input sel_input (fun input ->
	    select##value <- string (operator_of_constr constr);
	    input##value <- string (pattern_of_constr constr))))
      [("#select-terms", "#pattern-terms", term_constr);
       ("#select-properties", "#pattern-properties", property_constr);
       ("#select-modifiers", "#pattern-modifiers", Lisql.True)]

  method private refresh_extension =
    let open Sparql_endpoint in
    jquery "#results" (fun elt_results ->
      if lis#results_dim = 0 then begin
	elt_results##style##display <- string "none" end
      else begin
	lis#results_page offset limit (fun results_page ->
	  elt_results##style##display <- string "block";
	  jquery_set_innerHTML "#list-results"
	    (html_table_of_results html_state
	       ~first_rank:(offset+1)
	       ~focus_var:(match lis#focus_term_list with [Rdf.Var v] -> Some v | _ -> None)
	       results_page));
	jquery_all ".count-results" (fun elt ->
	  elt##innerHTML <- string
	    (let nb = lis#results_nb in
	     let grammar = Lisql2nl.config_lang#grammar in
	     let s_result, s_results = grammar#result_results in
	     if nb = 0
	     then grammar#no ^ " " ^ s_result
	     else
	       let a, b = offset+1, min nb (offset+limit) in
	       if a = 1 && b = nb && nb < Lis.config_max_results#value then
		 string_of_int b ^ " " ^ (if b=1 then s_result else s_results)
	       else
		 s_results ^ " " ^ string_of_int a ^ " - " ^ string_of_int b ^
		   " " ^ grammar#quantif_of ^ " " ^ string_of_int nb ^ (if nb < Lis.config_max_results#value then "" else "+")));
	stop_links_propagation_from elt_results;
	jquery_all_from elt_results ".header" (onclick (fun elt_foc ev ->
	  navigation#update_focus ~push_in_history:false (fun _ ->
	    try
	      let key = to_string (elt_foc##id) in
	      Some (html_state#get_focus key)
	    with _ -> None)));
	jquery_all_from elt_results ".cell" (onclick (fun elt ev ->
	  navigation#update_focus ~push_in_history:true (fun current_focus ->
	    let key = to_string (elt##id) in
	    let _rank, id, term = html_state#dico_results#get key in
	    let id_focus = html_state#get_focus (Html.focus_key_of_id id) in
	    Lisql.insert_term term id_focus )))
      end)

  val mutable refreshing_terms = false (* says whether a recomputation of term increments is ongoing *)
  method private refresh_term_increments_gen ajax_index =
    let apply_incr elt =
      let incr = html_state#dico_incrs#get (to_string (elt##id)) in
      let incr_opt = (* retrieving input value for input increments *)
	match incr with
	| Lisql.IncrInput (s,dt) ->
	  let ref_s = ref s in
	  jquery_input_from elt ".term-input" (fun input ->
	    ref_s := to_string input##value);
	  let s = !ref_s in
	  if check_input s dt
	  then Some (Lisql.IncrInput (s,dt))
	  else begin alert "Invalid input"; None end
	| _ -> Some incr in
      match incr_opt with
      | None -> ()
      | Some incr ->
	navigation#update_focus ~push_in_history:true
	  (Lisql.insert_increment incr)
    in
    refreshing_terms <- true;
    jquery_select "#select-terms" (fun select ->
      jquery_input "#pattern-terms" (fun input ->
	jquery "#list-terms" (fun elt_list ->
	  (*filtering_terms <- true;*)
	  ajax_index (norm_constr term_constr) [elt_list]
	    (fun ~partial index ->
	      elt_list##innerHTML <- string (html_index lis#focus html_state index);
	      jquery_set_innerHTML "#count-terms"
		(html_count_unit { Lis.value=List.length index; max_value=None; partial; unit=`Entities } Lisql2nl.config_lang#grammar#entity_entities);
	      stop_propagation_from elt_list "a, .term-input";
	      jquery_all_from elt_list ".increment" (onclick (fun elt ev ->
		apply_incr elt));
	      jquery_all_from elt_list ".term-input" (onenter (fun elt ev ->
		Opt.iter (elt##parentNode) (fun node ->
		  Opt.iter (Dom.CoerceTo.element node) (fun dom_elt ->
		    let incr_elt = Dom_html.element dom_elt in
		    apply_incr incr_elt))));
	      refreshing_terms <- false;
	      let new_constr = self#get_constr select input in
	      self#filter_increments elt_list new_constr;
	      self#set_term_constr new_constr))))
  method private refresh_term_increments_init =
    self#refresh_term_increments_gen lis#ajax_index_terms_init
  method private refresh_term_increments =
    self#refresh_term_increments_gen
      (fun constr elts k -> lis#index_terms_inputs (fun ~partial index_terms_inputs -> k ~partial (lis#index_ids @ index_terms_inputs)))
  method private refresh_term_increments_undefined =
    self#refresh_term_increments_gen
      (fun constr elts k -> k ~partial:false [])

  val mutable refreshing_properties = false (* says whether a recomputation of property increments is ongoing *)
  method private refresh_property_increments_gen process_index =
    refreshing_properties <- true;
    jquery_select "#select-properties" (fun select ->
      jquery_input "#pattern-properties" (fun input ->
	jquery "#list-properties" (fun elt_list ->
	  (*filtering_properties <- true;*)
	  process_index elt_list
	    (fun ~partial index ->
	      elt_list##innerHTML <- string (html_index lis#focus html_state index);
	      jquery_set_innerHTML "#count-properties"
		(html_count_unit { Lis.value=List.length index; max_value=None; partial; unit=`Concepts } Lisql2nl.config_lang#grammar#concept_concepts);
	      jquery_all_from elt_list ".increment" (onclick (fun elt ev ->
		navigation#update_focus ~push_in_history:true
		  (Lisql.insert_increment (html_state#dico_incrs#get (to_string (elt##id))))));
	      refreshing_properties <- false;
	      let new_constr = self#get_constr select input in
	      self#filter_increments elt_list new_constr;
	      self#set_property_constr new_constr))))
  method private refresh_property_increments_init =
    self#refresh_property_increments_gen (fun elt_list k -> lis#ajax_index_properties_init (norm_constr property_constr) elt_list k)
  method private refresh_property_increments =
    self#refresh_property_increments_gen (fun elt_list k -> lis#ajax_index_properties (norm_constr property_constr) elt_list k)
  method private refresh_property_increments_undefined =
    self#refresh_property_increments_gen (fun elt_list k -> k ~partial:true [])


  method private refresh_modifier_increments ~(init : bool) =
    let apply_incr elt =
      let incr = html_state#dico_incrs#get (to_string (elt##id)) in
      let incr =
	match incr with
	| Lisql.IncrName name ->
	  let ref_name = ref name in
	  jquery_input_from elt ".term-input" (fun input ->
	    ref_name := to_string input##value);
	  let name = !ref_name in
	  Lisql.IncrName name
	| _ -> incr in
      navigation#update_focus ~push_in_history:true (Lisql.insert_increment incr)
    in
    jquery "#list-modifiers" (fun elt_list ->
      let index = lis#index_modifiers ~init in
      elt_list##innerHTML <- string (html_index lis#focus html_state index);
      jquery_set_innerHTML "#count-modifiers"
	(html_count_unit { Lis.value=List.length index; max_value=None; partial=false; unit=`Modifiers } Lisql2nl.config_lang#grammar#modifier_modifiers);
      stop_propagation_from elt_list ".term-input";
      jquery_all_from elt_list ".increment" (onclick (fun elt ev ->
	apply_incr elt));
      jquery_all_from elt_list ".term-input" (onenter (fun elt ev ->
	Opt.iter (elt##parentNode) (fun node ->
	  Opt.iter (Dom.CoerceTo.element node) (fun dom_elt ->
	    let incr_elt = Dom_html.element dom_elt in
	    apply_incr incr_elt)))))

  method refresh =
    html_state <- new Html.state lis#id_labelling;
    jquery_select "#sparql-endpoint-select" (fun select ->
      let options = select##options in
      for i = options##length - 1 downto 0 do
	Opt.iter options##item(i) (fun option ->
	  let value = to_string option##value in
	  if value = lis#endpoint || value = "" then option##selected <- bool true)
      done);
    jquery_input "#sparql-endpoint-input" (fun input -> input##value <- string lis#endpoint);
    self#refresh_lisql;
    self#refresh_increments_focus;
    self#refresh_constrs;
    jquery "#increments" (fun elt_incrs ->
      jquery "#results" (fun elt_res ->
	lis#ajax_sparql_results (norm_constr term_constr) [elt_incrs; elt_res]
	  (function
	    | None ->
	      Jsutils.yasgui#set_query "SELECT * WHERE { }";
	      Jsutils.yasgui#set_response "";
	      jquery "#results" (fun elt -> elt##style##display <- string "none");
	      (*jquery_input "#pattern-terms" (fun input -> input##disabled <- bool true);*)
	      jquery_all ".list-incrs" (fun elt -> elt##innerHTML <- string "");
	      jquery_all ".count-incrs" (fun elt -> elt##innerHTML <- string "---");
	      ( match lis#focus_term_list with
	      | [] ->
		self#refresh_term_increments_undefined;
		self#refresh_property_increments_undefined;
		self#refresh_modifier_increments ~init:true
	      | [Rdf.Var v] ->
		self#refresh_term_increments_init;
		self#refresh_property_increments_init;
		self#refresh_modifier_increments ~init:true
	      | _ ->
		self#refresh_term_increments;
		self#refresh_property_increments;
		self#refresh_modifier_increments ~init:false)
	    | Some sparql ->
	      let sparql_with_prefixes = Sparql.prologue#add_declarations_to_query sparql in
	      Jsutils.yasgui#set_query sparql_with_prefixes;
	      self#refresh_extension;
	      jquery_input "#pattern-terms" (fun input -> input##disabled <- bool false);
	      ( match lis#focus_term_list with
	      | [] ->
		self#refresh_term_increments_undefined;
		self#refresh_property_increments_undefined;
		self#refresh_modifier_increments ~init:false
	      | _ ->
		self#refresh_term_increments;
		self#refresh_property_increments;
		self#refresh_modifier_increments ~init:false ))))

  method private filter_increments elt_list constr =
    let matcher = compile_constr constr in
    let there_is_match = ref false in
    jquery_all_from elt_list "li" (fun elt_li ->
      jquery_from elt_li ".increment" (fun elt_incr ->
	let str =
	  match constr with
	  | Lisql.HasLang _ | Lisql.HasDatatype _ -> to_string elt_incr##innerHTML (* TODO: extract proper lang/datatype part *)
	  | _ ->
	    Opt.case (elt_incr##querySelector(string ".classURI, .propURI, .URI, .Literal, .nodeID, .modifier"))
	      (fun () -> to_string elt_incr##innerHTML)
	      (fun elt -> to_string elt##innerHTML) in
(*	  
	  let s = Opt.case (elt_incr##querySelector(string ".classURI, .propURI, .URI, .Literal, .nodeID, .modifier"))
	      (* only works if a single element *)
	    (fun () -> to_string (elt_incr##innerHTML))
	    (fun elt -> to_string (elt##innerHTML)) in
	  Rdf.PlainLiteral (s, "") in
*)
(*
	  let t =
	    let textContent = elt_incr##textContent in (* ##textContent only available since js_of_ocaml v2.4 *)
	    let text = Opt.case textContent (fun () -> "") to_string in
	    Rdf.PlainLiteral (text, "") in
*)
(*
	  let t =
	    let incr = html_state#dico_incrs#get (to_string (elt_incr##id)) in
	    match Lisql.term_of_increment incr with
	      | Some t -> t
	      | None ->
		let s = Opt.case (elt_incr##querySelector(string ".modifier"))
		  (fun () -> to_string (elt_incr##innerHTML))
		  (fun elt -> to_string (elt##innerHTML)) in
		Rdf.PlainLiteral (s, "") in
*)
	if matcher str
	then begin elt_li##style##display <- string "list-item"; there_is_match := true end
	else elt_li##style##display <- string "none"))

  method is_home =
    Lisql.is_home_focus lis#focus

  method set_term_constr constr =
    let to_refresh =
      if constr = term_constr then false
      else if subsumed_constr constr term_constr then not refreshing_terms
      else begin self#abort_all_ajax; true end in	
    if to_refresh (* not refreshing_terms && constr <> term_constr *)
    then begin
      refreshing_terms <- true;
      term_constr <- constr;
      if self#is_home
      then self#refresh_term_increments_init
      else self#refresh
    end

  method set_property_constr constr =
    let to_refresh =
      if constr = property_constr then false
      else if subsumed_constr constr property_constr then not refreshing_terms
      else begin self#abort_all_ajax; true end in	
    if to_refresh (* not refreshing_properties && constr <> property_constr *)
    then begin
      refreshing_properties <- true;
      property_constr <- constr;
      if self#is_home
      then self#refresh_property_increments_init
      else self#refresh_property_increments
    end

  method pattern_changed
    ~(select : Dom_html.selectElement t)
    ~(input : Dom_html.inputElement t)
    ~(elt_list : Dom_html.element t)
    (k : Lisql.constr -> unit)
    =
    let new_constr = self#get_constr select input in
    self#filter_increments elt_list new_constr;
    k new_constr
(*	
      let n = String.length pat in
      if (not !there_is_match && (pat = "" || pat.[n - 1] = ' ')) || (n >= 2 && pat.[n-1] = ' ' && pat.[n-2] = ' ')
      then begin
	(*Firebug.console##log(string "pattern: no match, call continuation");*)
	k constr
      end
*)

  method set_limit n =
    limit <- n;
    self#refresh_extension

  method give_more =
    if offset + limit < lis#results_nb
    then self#set_limit (limit+10)

  method give_less =
    if limit > 10
    then self#set_limit (limit-10)

  method page_down =
    let offset' = offset + limit in
    if offset' < lis#results_nb
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

  method abort_all_ajax =
    lis#abort_all_ajax;
    refreshing_terms <- false;
    refreshing_properties <- false
      
  method new_place endpoint focus =
    {< lis = new Lis.place endpoint focus;
       offset = 0;
       term_constr = Lisql.True;
       property_constr = Lisql.True; >}

end

class history (endpoint : string) (foc : Lisql.focus) =
object (self)
  val mutable past : place list = []
  val mutable present : place = new place endpoint foc
  val mutable future : place list = []

  initializer
    present#set_navigation (self :> navigation)

  method present : place = present

  method push (p : place) : unit =
    if logging_on () then
      Lwt.ignore_result
	(XmlHttpRequest.perform_raw_url
	   ~get_args:[("session", session_id);
		      ("endpoint", p#lis#endpoint);
		      ("query", Permalink.of_query p#lis#query)]
	   url_querylog_php); (* counting hits *)
    past <- present::past;
    present <- p;
    future <- []

  method change_endpoint url =
    Sparql.prologue#reset;
    present#abort_all_ajax;
    config#set_endpoint url;
    let focus = Lisql.factory#reset; Lisql.factory#home_focus in
    let p = present#new_place url focus in
    p#set_navigation (self :> navigation);
    self#push p;
    p#refresh

  method update_focus ~push_in_history f =
    match f present#lis#focus with
      | None -> ()
      | Some foc ->
	present#abort_all_ajax;
	let p = present#new_place present#lis#endpoint foc in
	p#set_navigation (self :> navigation);
	if push_in_history then self#push p else present <- p;
	p#refresh

  method home =
    self#update_focus ~push_in_history:true
      (fun _ -> Lisql.factory#reset; Some Lisql.factory#home_focus)

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

(* main *)

let translate () =
  firebug "Translating HTML elements";
  (* getting current language *)
  let lang = Lisql2nl.config_lang#value in
  (* translating visible textual elements *)
  jquery_all ".texte" (fun elt -> elt##style##display <- string "none");
  jquery_all (".texte.lang-" ^ lang) (fun elt -> elt##style##display <- string "inline");
  (* translating tooltips *)
  let tooltip_lang_selector = ".tooltip.lang-" ^ lang in
  jquery_all ".tooltiped" (fun elt ->
    jquery_from elt tooltip_lang_selector (fun elt2 ->
      elt##title <- elt2##innerHTML));
  (* translating some select options *)
  jquery_all ".select-incrs" (fun elt ->
    Opt.iter (Dom_html.CoerceTo.select elt) (fun select ->
      let options = select##options in
      for i = 0 to options##length - 1 do
	Opt.iter options##item(i) (fun option ->
	  let new_text =
	    let grammar = Lisql2nl.config_lang#grammar in
	    match to_string option##value with
	      | "matchesAll" -> String.concat " " [grammar#matches; grammar#all; grammar#quantif_of]
	      | "matchesAny" -> String.concat " " [grammar#matches; grammar#quantif_one; grammar#quantif_of]
	      | "after" -> grammar#after
	      | "before" -> grammar#before
	      | "fromTo" -> String.concat " " [grammar#interval_from; grammar#interval_to]
	      | "higherThan" -> grammar#higher_or_equal_to
	      | "lowerThan" -> grammar#lower_or_equal_to
	      | "between" -> grammar#interval_between
	      | "hasLang" -> String.concat " " [grammar#has_as_a; grammar#language]
	      | "hasDatatype" -> String.concat " " [grammar#has_as_a; grammar#datatype]
	      | _ -> to_string option##innerHTML in
	  option##innerHTML <- string new_text)
      done))

let _ =
  Firebug.console##log(string "Starting Sparklis");
  if logging_on () then
    Lwt.ignore_result (XmlHttpRequest.get url_log_php); (* counting hits *)
  Dom_html.window##onload <- Dom.handler (fun ev ->
    (* initializing YASGUI *)
    Jsutils.yasgui#init;
    (* defining navigation history *)
    let default_endpoint = ref "" in
    let default_focus = ref Lisql.factory#home_focus in
    jquery_input "#sparql-endpoint-input" (fun input ->
      let url = to_string input##value in
      default_endpoint := url); (* using default endpoint as given in HTML *)
    let _ = (* changing endpoint and focus if permalink *)
      let args = Url.Current.arguments in
      let args =
	match args with
	  | [] -> []
	  | (k,v)::l ->
	    let k = try String.sub k 1 (String.length k - 1) with _ -> firebug "osparklis.ml: removing '?' failed"; k in  (* bug: '?' remains in first key *)
	    (k, v)::l in
      Firebug.console##log(string (String.concat " & " (List.map (fun (k,v) -> k ^ " = " ^ v) args)));
      (try
	 let url = List.assoc "endpoint" args in
	 let url = (* switching from lisfs2008 to servolis *)
	   try List.assoc url
		 ["http://lisfs2008.irisa.fr/dbpedia/sparql", "http://servolis.irisa.fr:3030/dbpedia/sparql";
		  "http://lisfs2008.irisa.fr/defiEGC2016/sparql", "http://servolis.irisa.fr:3131/defiEGC2016/sparql";
		  "http://lisfs2008.irisa.fr/mondial/sparql", "http://servolis.irisa.fr:3232/mondial/sparql"]
	   with _ -> url in
	default_endpoint := url;
	try
	  let query = Permalink.to_query (List.assoc "query" args) in
	  default_focus := Lisql.focus_of_query query
	with
	  | Stream.Failure -> Firebug.console##log(string "Permalink syntax error")
	  | Stream.Error msg -> Firebug.console##log(string ("Permalink syntax error: " ^ msg))
	  |  _ -> ()
      with _ -> ());
      (* initializing configuration from HTML *)
      config#init !default_endpoint args in
    (* creating and initializing history *)
    let history = new history !default_endpoint !default_focus in

    (* setting event callbacks *)
    jquery "#home" (onclick (fun elt ev -> history#home));
    jquery "#back" (onclick (fun elt ev -> history#back));
    jquery "#forward" (onclick (fun elt ev -> history#forward));
    jquery "#refresh" (onclick (fun elt ev -> history#update_focus ~push_in_history:false (fun focus -> Some focus)));
    jquery_select "#sparql-endpoint-select"
      (onchange (fun select ev ->
	jquery_input "#sparql-endpoint-input" (fun input ->
	  let url = to_string select##value in
	  if url = ""
	  then begin
	    input##value <- string "http://";
	    input##select() end
	  else begin
	    input##value <- string url;
	    history#change_endpoint url
	  end)));
    jquery "#sparql-endpoint-button" (onclick (fun elt ev ->
      jquery_input "#sparql-endpoint-input" (fun input ->
	let url = to_string (input##value) in
	history#change_endpoint url)));
    jquery_input "#sparql-endpoint-input" (onenter (fun input ev ->
      jquery_click "#sparql-endpoint-button"));
    jquery "#config-control" (onclick (fun elt ev ->
      jquery "#config-panel" (fun panel ->
	let dis =
	  if to_string panel##style##display = "none"
	  then "block"
	  else "none" in
	panel##style##display <- string dis;
	if dis = "none" then
	  config#if_has_changed
	    ~translate
	    ~refresh:(fun () -> history#update_focus ~push_in_history:false (fun focus -> Some focus)))));
    jquery "#switch-view" (onclick (fun elt ev ->
      jquery_toggle "#sparklis-view";
      jquery_toggle "#yasgui-view";
      let view = jquery_toggle_innerHTML "#switch-view" "YASGUI view" "SPARKLIS view" in
      if view = "SPARKLIS view" then Jsutils.yasgui#refresh));

    jquery "#permalink" (onclick (fun elt ev -> history#present#show_permalink));

    jquery "#show-hide-increments" (onclick (fun elt ev ->
      jquery_toggle "#increments-body";
      ignore (jquery_toggle_innerHTML "#show-hide-increments" "+" "-")));
    jquery "#show-hide-results" (onclick (fun elt ev ->
      jquery_toggle "#results-body";
      ignore (jquery_toggle_innerHTML "#show-hide-results" "+" "-")));
    (*jquery "#show-hide-sparql" (onclick (fun elt ev ->
      jquery_toggle "#sparql-body";
      jquery_toggle_innerHTML "#show-hide-sparql" "+" "-"));*)

    jquery "#button-terms" (onclick (fun elt ev ->
      jquery_select "#select-terms" (fun select ->
	jquery_input "#pattern-terms" (fun input ->
	  let op = to_string (select##value) in
	  let pat = to_string (input##value) in
	  try
	    let constr = norm_constr (make_constr op pat) in
	    if constr = Lisql.True
	    then
	      Dom_html.window##alert(string "Empty filter")
	    else
	      history#update_focus ~push_in_history:true
		(Lisql.insert_constr constr)
	  with Invalid_argument msg ->
	    Dom_html.window##alert(string ("Invalid filter: " ^ msg))))));
    jquery_input "#pattern-terms" (onenter (fun input ev ->
      jquery_click "#button-terms"));
    List.iter
      (fun (sel_select, sel_input, sel_list, k) ->
	jquery_select sel_select (fun select ->
	  jquery_input sel_input (fun input ->
	    jquery sel_list (fun elt_list ->
	      (oninput
		 (fun input ev -> history#present#pattern_changed ~select ~input ~elt_list k)
		 input)))))
      [("#select-terms", "#pattern-terms", "#list-terms", (fun constr -> history#present#set_term_constr constr));
       ("#select-properties", "#pattern-properties", "#list-properties", (fun constr -> history#present#set_property_constr constr));
       ("#select-modifiers", "#pattern-modifiers", "#list-modifiers", (fun constr -> ()))];
    
    jquery_all ".previous-results" (onclick (fun elt ev -> history#present#page_up));
    jquery_all ".next-results" (onclick (fun elt ev -> history#present#page_down));
    jquery_select ".limit-results"
      (onchange (fun select ev ->
	let limit = int_of_string (to_string (select##value)) in
	history#present#set_limit limit));

    (* generating and displaying contents *)
    translate ();
    history#present#refresh;
    bool true)
