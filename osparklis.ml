(*
  Copyright 2013-2017 Sébastien Ferré, IRISA, Université de Rennes 1

  This file is part of Sparklis.
*)

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

(* other configs *)

let config_short_permalink = new Config.boolean_input ~key:"short-permalink" ~input_selector:"#input-short-permalink" ~default:true ()

let config_auto_filtering = new Config.boolean_input ~key:"auto-filtering" ~input_selector:"#input-auto-filtering" ~default:true ()

(* debug utilities *)

let rec string_of_delta =
  let open Lisql in
  function
  | DeltaNil -> "no change"
  | DeltaIds ids -> "new ids: " ^ String.concat ", " (List.map string_of_int ids)
  | DeltaDuplicate map -> "dup: " ^ String.concat ", " (List.map (fun (id,id') -> string_of_int id ^ "->" ^ string_of_int id') map)
  | DeltaSelection (d,ld) -> "sel: " ^ string_of_delta d ^ " [" ^ String.concat "; " (List.map string_of_delta ld) ^ "]"
				 
(* constraint compilation *)

let rec get_constr ~endpoint
	  (current_constr : Lisql.constr)
	  (getting_constr : bool ref)  (* flag to avoid parallel run of [get_constr] *)
	  (input_changed : bool ref) (* flag to know when some input was blocked by getting_constr=true *)
	  (select : Dom_html.selectElement t) (input : Dom_html.inputElement t)
	  (k : Lisql.constr -> unit) : unit =
  input_changed := false;
  Html.make_new_constr
    ~endpoint
    current_constr
    select input
    (fun new_constr_opt ->
     let new_constr =
       match new_constr_opt with
       | Some new_constr -> k new_constr; new_constr
       | None -> current_constr in (* do nothing when the constraint has not changed *)
     if !input_changed
     then get_constr ~endpoint new_constr getting_constr input_changed select input k
     else getting_constr := false)

let regexp_of_pat pat = Regexp.regexp_with_flag (Regexp.quote pat) "i"
let matches s re = Regexp.search re s 0 <> None
let leq s1 s2 = try (float_of_string s1) <= (float_of_string s2) with _ -> false

let norm_constr = (* normalizing for empty patterns "" *)
  (* MUST be called for any semantic use of constraints *)
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
  | ExternalSearch (`Wikidata [], _) -> True
  | ExternalSearch (`TextQuery [], _) -> True
  | c -> c

let compile_constr ?(on_modifiers = false) constr : (string -> bool) =
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
  | ExternalSearch ((`Wikidata kwds | `TextQuery kwds), _) ->
     let lre = List.map regexp_of_pat kwds in
     (fun s -> List.for_all (fun re -> matches s re) lre)

let replace_symbol_by_ascii = (* for constraint matching on modifiers *)
  let l_re_by =
    List.map
      (fun (symbol,ascii) -> (Regexp.regexp_string symbol, ascii))
      ["≠", "!=";
       "≥", ">=";
       "≤", "<="] in
  fun str ->
  List.fold_left
    (fun str (re,by) -> Regexp.global_replace re str by)
    str l_re_by

(* constraint subsumption *)

let equivalent_constr constr1 constr2 : bool =
  norm_constr constr1 = norm_constr constr2

let subsumed_constr constr1 constr2 : bool =
  (* must avoid to return true when false, but can return false when true *)
  let open Lisql in
  match norm_constr constr1, norm_constr constr2 with
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
  | ExternalSearch (`Wikidata kwds1, _), ExternalSearch (`Wikidata kwds2, _)
  | ExternalSearch (`TextQuery kwds1, _), ExternalSearch (`TextQuery kwds2, _) ->
     List.for_all (fun s2 ->
      List.exists (fun s1 ->
	Common.has_prefix s1 s2 (* 'has_prefix' used as an approximation of 'contains' *)
      ) kwds1
    ) kwds2
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
  | `Duration -> s <> "P" && s <> "PT" && Regexp.string_match (Regexp.regexp "P(\\d+Y)?(\\d+M)?(\\d+D)?(T(\\d+H)?(\\d+M)?(\\d+([.]\\d+)?S)?)?$") s 0 <> None
    
(* configuration *)

let config =
  let config_inputs : Config.input list =
    [ (Rdf.config_wikidata_mode :> Config.input);
      (Sparql_endpoint.config_proxy :> Config.input);
      (Sparql_endpoint.config_proxy_url :> Config.input);
      (Sparql_endpoint.config_method_get :> Config.input);
      (Sparql_endpoint.config_withCredentials :> Config.input);
      (Sparql_endpoint.config_caching :> Config.input);
      (Sparql_endpoint.config_default_graphs :> Config.input);
      (Sparql_endpoint.config_schema_graphs :> Config.input);
      (Ontology.sparql_relations :> Config.input);
      (Ontology.config_class_hierarchy :> Config.input);
      (Ontology.config_property_hierarchy :> Config.input);
      (Ontology.config_hierarchy_inheritance :> Config.input);
      (Ontology.config_sort_by_position :> Config.input);
      (Ontology.config_show_logo :> Config.input);
      (Lis.config_intentional_init_concepts :> Config.input);
      (Lis.config_nary_relations :> Config.input);
      (Lis.config_concept_profile :> Config.input);
      (Lis.config_regexp_hidden_URIs :> Config.input);
      (Lis.config_max_results :> Config.input);
      (Lis.config_max_increment_samples :> Config.input);
      (Lis.config_max_classes :> Config.input);
      (Lis.config_max_properties :> Config.input);
      (Lexicon.config_entity_lexicon :> Config.input);
      (Lexicon.config_class_lexicon :> Config.input);
      (Lexicon.config_property_lexicon :> Config.input);
      (Lexicon.config_arg_lexicon :> Config.input);
      (Lisql2nl.config_lang :> Config.input);
      (Lisql2nl.config_show_datatypes :> Config.input);
      (Lisql2sparql.config_fulltext_search :> Config.input);
      (Html.config_logo_height :> Config.input);
      (config_logging :> Config.input);
      (config_short_permalink :> Config.input);
      (config_auto_filtering :> Config.input); ] in
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

let dummy_title = "???" (* to suggest defining a title *)
  
let permalink_of_place (lis : Lis.place) : string =
  let endpoint = lis#endpoint in
  let title = jquery_get_innerHTML "#sparql-endpoint-title" in
  let args = config#get_permalink in
  let args =
    ("endpoint",endpoint)
    :: (if Lisql.is_home_focus lis#focus
	then args
	else ("sparklis-query", Permalink.of_query lis#query)
	     :: ("sparklis-path", Permalink.of_path lis#path)
	     :: args) in
  let args =
    if title = dummy_title
    then args
    else ("title",title) :: args in
  let permalink_url =
    let current_url =
      match Url.Current.get () with
      | None -> Url.(Http { hu_host = "localhost";
			    hu_port = 8080;
			    hu_path = [];
			    hu_path_string = "";
			    hu_arguments = [];
			    hu_fragment = "" })
      | Some url -> url in
    match current_url with
    | Url.Http url -> Url.Http { url with Url.hu_arguments = args }
    | Url.Https url -> Url.Https { url with Url.hu_arguments = args }
    | Url.File url -> Url.File { url with Url.fu_arguments = args } in
  Url.string_of_url permalink_url
  
(* navigation place and history *)

let sorting_frequency = "frequency"
		    
class navigation =
object
  method change_endpoint (url : string) : unit = ()
  method update_focus ~(push_in_history : bool) (f : Lisql.focus -> (Lisql.focus * Lisql.delta) option) : unit = ()
end

class increment_selection (sel_selection : string) =
object (self)
  val mutable l_incr : Lisql.increment list = []
  method get = List.rev l_incr
  method private refresh =
    let n_incr = List.length l_incr in
    jquery sel_selection (fun elt ->
      elt##style##display <-
	string (if n_incr=0 then "none" else "block");
      jquery_from elt ".selection-count" (fun elt_count ->
        elt_count##innerHTML <- string (string_of_int n_incr)))
  method toggle (incr : Lisql.increment) : unit =
    let _ =
      if List.mem incr l_incr
      then l_incr <- List.filter ((<>) incr) l_incr
      else l_incr <- incr :: l_incr in
    self#refresh
  method reset =
    l_incr <- [];
    self#refresh
end

class place (endpoint : string) (foc : Lisql.focus) =
object (self)
  val mutable lis = new Lis.place endpoint foc
  method lis = lis

  val mutable offset = 0
  val mutable limit = 10

  val mutable term_constr = Lisql.True
  method term_constr = term_constr
  method set_term_constr c = term_constr <- c

  val mutable property_constr = Lisql.True
  method property_constr = property_constr
  method set_property_constr c = property_constr <- c
						 
  val mutable modifier_constr = Lisql.True
  method modifier_constr = modifier_constr
  method set_modifier_constr c = modifier_constr <- c
						 
  val term_selection = new increment_selection "#selection-terms"
  val property_selection = new increment_selection "#selection-properties"
  val modifier_selection = new increment_selection "#selection-modifiers"
				  
  (* UI state *)
  val mutable document_scroll = 0
  val mutable property_scroll = 0
  val mutable term_scroll = 0
  val mutable modifier_scroll = 0
  val mutable inverse_terms = false
  val mutable inverse_properties = false
  val mutable sorting_terms = sorting_frequency
  val mutable sorting_properties = sorting_frequency
  val mutable expanded_terms : Lisql.increment list = []
  val mutable expanded_properties : Lisql.increment list = []
							     
  val mutable navigation = new navigation
  method set_navigation (navig : navigation) = navigation <- navig

  val mutable html_state = new Html.state (new Lisql2nl.id_labelling [])
  initializer html_state <- new Html.state lis#id_labelling

  val mutable permalink = ""
  initializer permalink <- permalink_of_place lis
				
  method show_permalink : unit =
    let show (url : string) : unit =
      ignore (prompt
		Lisql2nl.config_lang#grammar#msg_permalink
		url) in
    if config_short_permalink#value
    then
      let permalink = (* converting local URLs to http URLs *)
	match Url.url_of_string permalink with
	| Some (Url.File url) ->
	   Url.string_of_url
	     (Url.(Http { hu_host = "www.irisa.fr";
			  hu_port = 80;
			  hu_path = ["LIS"; "ferre"; "sparklis"; "osparklis.html"];
			  hu_path_string = "/LIS/ferre/sparklis/osparklis.html";
			  hu_arguments = url.fu_arguments;
			  hu_fragment = "" }))
	| _ -> permalink in
      Lwt.ignore_result
	(Lwt.bind
	   (XmlHttpRequest.perform_raw
	      ~headers:["Content-Type", "application/json";
			"apikey", "4ac1772b3b4749748bec9ffc66044157"]
	      ~get_args:["destination", permalink]
	      ~response_type:XmlHttpRequest.JSON
	      "https://api.rebrandly.com/v1/links/new")
	   (fun http_frame ->
	    let open XmlHttpRequest in
	    Opt.case http_frame.content
		     (fun () -> show permalink)
		     (fun js -> show js##shortUrl);
	    Lwt.return ()))
    else show permalink

  method private refresh_lisql =
    jquery "#lisql" (fun elt ->
      elt##innerHTML <- string (html_query html_state lis#query);
      stop_links_propagation_from elt;
      jquery_all_from elt ".focus" (onclick (fun elt_foc ev ->
	Dom_html.stopPropagation ev;
	navigation#update_focus ~push_in_history:false (fun _ ->
	  let key = to_string (elt_foc##id) in
	  Some (html_state#get_focus key, Lisql.DeltaNil))));
      jquery_from elt "#delete-current-focus"
	(onclick (fun elt_button ev ->
	  Dom_html.stopPropagation ev;
	  navigation#update_focus ~push_in_history:true Lisql.delete_focus)))

  method private refresh_focus =
    let html_focus_np, html_focus_ng =
      match lis#focus_term_opt with
	| Some (Rdf.Var v) ->
	  (try
	      let id = lis#id_labelling#get_var_id v in
	      Html.html_id_np html_state id, Html.html_id_ng html_state id
	    with _ -> (* should not happen *)
		 let html = escapeHTML v in
		 html, html)
	| Some t ->
 	   let html = Html.html_term t in
	   html, html
	| None ->
	   let html = "(" ^ Lisql2nl.config_lang#grammar#undefined ^ ")" in
	   html, html in
    jquery_all ".focus-np"
	       (fun elt ->
		elt##innerHTML <- string html_focus_np);
    jquery_all ".focus-ng"
	       (fun elt ->
		elt##innerHTML <- string html_focus_ng)

  method private refresh_constrs term_constr property_constr =
    List.iter
      (fun (sel_select, sel_input, constr, get_list_constraints) ->
	jquery_select sel_select (fun select ->
	  jquery_input sel_input (fun input ->
	    let l_constr = get_list_constraints constr in
	    let html_select_options =
	      html_list_constr html_state l_constr in
	    select##innerHTML <- string html_select_options;
	    let op = Html.option_of_constr constr in
	    let pat = Html.pattern_of_constr constr in
	    select##value <- string op;
	    if select##selectedIndex < 0 then select##selectedIndex <- 0;
	    input##value <- string pat)))
      [("#select-terms", "#pattern-terms", term_constr, lis#list_term_constraints);
       ("#select-properties", "#pattern-properties", property_constr, lis#list_property_constraints);
       ("#select-modifiers", "#pattern-modifiers", Lisql.MatchesAll [], lis#list_modifier_constraints)]

  method private refresh_extension =
    let open Sparql_endpoint in
    if lis#results_dim = 0 then (
	jquery_disable_all "#nav-results-nested-table";
	jquery_set_innerHTML "#nested-table" "";
	jquery_disable_all "#nav-results-table";
	jquery_set_innerHTML "#list-results" "";
	jquery_set_innerHTML "#count-results"
			     (let grammar = Lisql2nl.config_lang#grammar in
			      grammar#no ^ " " ^ fst grammar#result_results);
	jquery_disable_all "#nav-results-map";
	jquery_set_innerHTML "#map" "No geolocalized data";
	jquery_disable_all "#nav-results-slideshow";
	jquery_set_innerHTML "#carousel-slides" "No media" )
    else begin
      let focus_var =
	match lis#focus_term_opt with
	| Some (Rdf.Var v) -> Some v
	| _ -> None in
      let tables_handler elt_table =
	(* common handlers between table and nested-table *)
	stop_links_propagation_from elt_table;
	jquery_all_from elt_table ".header[id]" (onclick (fun elt_foc ev ->
	  navigation#update_focus ~push_in_history:false (fun _ ->
	    try
	      let key = to_string (elt_foc##id) in
	      Some (html_state#get_focus key, Lisql.DeltaNil)
	    with _ -> None)));
	jquery_all_from elt_table ".partial-count" (onclick (fun elt ev ->
	  Dom_html.stopPropagation ev;
	  let key = to_string elt##id in
	  let id = html_state#dico_counts#get key in
	  lis#ajax_count_id id [elt]
	    ~k_count:(function
		       | Some n ->
			  elt##innerHTML <- string (string_of_int n);
			  elt##className <- string "frequency-entities"
		       | None -> ())));
	jquery_all_from elt_table ".cell[id]" (onclick (fun elt ev ->
	  navigation#update_focus ~push_in_history:true (fun current_focus ->
	    let key = to_string (elt##id) in
	    let _view, _rank, id, term = html_state#dico_results#get key in
	    let id_focus = html_state#get_focus (Html.focus_key_of_id id) in
	    Lisql.insert_term term id_focus)))
      in
      (* nested table *)
      jquery "#nested-table" (fun elt_table ->
	lis#results_shape_data
	  (fun lv shape_data ->
	   let counts =
	     match lv with (* only on first column *)
	     | Some v::lv1 -> lis#estimate_count_var v :: List.map (fun _ -> None) lv1
	     | _ -> List.map (fun _ -> None) lv in
	   let partial = lis#partial_results in
	   jquery_enable_all "#nav-results-nested-table";
	   jquery_set_innerHTML "#nested-table"
	     (Html.html_trees html_state ~partial ~focus_var lv shape_data counts);
	   tables_handler elt_table));
      (* table of results *)
      jquery "#list-results" (fun elt_results ->
	lis#results_page offset limit (fun results_page ->
	  let counts =
	    List.map
	      (fun (v,i) -> lis#estimate_count_var v)
	      results_page.Sparql_endpoint.vars in
	  jquery_enable_all "#nav-results-table";
	  let partial = lis#partial_results in		       
	  jquery_set_innerHTML "#list-results"
	    (html_table_of_results html_state
	       ~partial
	       ~first_rank:(offset+1)
	       ~focus_var
	       results_page counts);
	  jquery "#count-results" (fun elt ->
	    elt##innerHTML <- string
	      (let nb = lis#results_nb in
	       let grammar = Lisql2nl.config_lang#grammar in
	       let s_result, s_results = grammar#result_results in
	       if nb = 0
	       then grammar#no ^ " " ^ s_results
	       else
		 let a, b = offset+1, min nb (offset+limit) in
		 if a = 1 && b = nb && not partial then
		   string_of_int b ^ " " ^ (if b=1 then s_result else s_results)
		 else
		   s_results ^ " " ^ string_of_int a ^ " - " ^ string_of_int b ^
		     " " ^ grammar#quantif_of ^ " " ^ string_of_int nb ^ (if not partial then "" else "+")));
	  tables_handler elt_results));
      (* slideshow of results *)
      lis#results_slides
	(function
	  | [] ->
	     jquery_disable_all "#nav-results-slideshow";
	     jquery_set_innerHTML "#carousel-slides" "No media"
	  | slides ->
	     jquery_enable_all "#nav-results-slideshow";
	     jquery_set_innerHTML
	       "#carousel-slides"
	       (Html.html_slides html_state slides));
      (* map of results *)
      lis#results_geolocations (fun geolocations ->
	  jquery "#map" (fun elt_map ->
	    if geolocations = [] then begin
		jquery_disable_all "#nav-results-map";
		elt_map##innerHTML <- string "No geolocalized data"
	      end
	    else begin
		jquery_enable_all "#nav-results-map";
		jquery "#nav-tab-map"
		       (fun elt ->
			let _id = Dom_html.addEventListener
				    elt
				    (Dom_html.Event.make "click" (*"shown.bs.tab"*))
				    (Dom_html.handler
				       (fun ev ->
					let geolocations =
					  List.map
					    (fun (lat,long,term) ->
					     let html = Html.html_cell_contents term in
					     (lat,long,html))
					    geolocations in
					Lwt.on_termination
					  (Lwt_js.sleep 0.2)
					  (fun () ->
					   google#draw_map geolocations elt_map);
					bool true))
				    (bool false) in
			jquery "li.active a#nav-tab-map"
			       (fun elt ->
				firebug "Clicked map tab";
				Unsafe.(meth_call elt "click" [||]));
			());
	    end))
      end


  val mutable refreshing_terms = false (* says whether a recomputation of term increments is ongoing *)
  method private refresh_term_increments current_constr =
    let get_incr_opt elt =
      let incr = html_state#dico_incrs#get (to_string (elt##id)) in
      (* retrieving input value for input increments *)
      match incr with
      | Lisql.IncrSelection (selop,_) ->
	 let l_incr = term_selection#get in
	 if l_incr = []
	 then begin alert "Empty selection"; None end
	 else Some (Lisql.IncrSelection (selop, l_incr))
      | Lisql.IncrInput (s,dt) ->
	 let ref_s = ref s in
	 jquery_input_from
	   elt
	   ".term-input"
	   (fun input -> ref_s := to_string input##value);
	 let s = !ref_s in
	 if check_input s dt
	 then Some (Lisql.IncrInput (s,dt))
	 else begin alert "Invalid input"; None end
      | _ -> Some incr in
    let apply_incr elt =
      match get_incr_opt elt with
      | None -> ()
      | Some incr ->
	 navigation#update_focus ~push_in_history:true
				 (Lisql.insert_increment incr) in
    let toggle_incr elt =
      match get_incr_opt elt with
      | Some (Lisql.IncrTerm _ | Lisql.IncrId _ as incr) ->
	 let _present = toggle_class elt "selected-incr" in
	 term_selection#toggle incr
      | _ -> ()
    in
    refreshing_terms <- true;
    jquery_select "#select-terms" (fun select ->
     jquery_input "#pattern-terms" (fun input ->
      jquery "#selection-terms-items" (fun elt_sel_items ->
       jquery "#list-terms" (fun elt_list ->
	jquery_select "#select-sorting-terms" (fun sel_sorting ->
	jquery_input "#input-inverse-terms" (fun input_inverse ->
	  lis#ajax_index_terms_inputs_ids (norm_constr current_constr) [elt_list]
	   (fun ~partial -> function
	    | None ->
	       refreshing_terms <- false;
	       let new_constr = term_constr in
	       self#refresh_new_term_constr current_constr new_constr
	    | Some index ->
	      input_inverse##checked <- bool inverse_terms;
	      sel_sorting##value <- string sorting_terms;
	      let html_sel, html_list, count =
		let inverse = to_bool input_inverse##checked in
		let sort_by_frequency = to_string sel_sorting##value = sorting_frequency in 
		html_index lis#focus html_state index ~inverse ~sort_by_frequency in
	      elt_sel_items##innerHTML <- string html_sel;
	      elt_list##innerHTML <- string html_list;
	      elt_list##scrollTop <- term_scroll;
	      self#restore_expanded_terms;
	      jquery_set_innerHTML "#count-terms"
				   (html_count_unit { Lis.value=count; max_value=None; partial; unit=`Entities } Lisql2nl.config_lang#grammar#entity_entities);
	      term_selection#reset;			   
	      stop_propagation_from elt_list "a, .term-input";
	      jquery_all_from elt_sel_items ".selection-increment" (onclick (fun elt ev ->
	        apply_incr elt));
	      jquery_all_from elt_list ".increment" (onclick (fun elt ev ->
		if to_bool ev##ctrlKey
		then toggle_incr elt
		else apply_incr elt));
	      jquery_all_from elt_list ".term-input" (onenter (fun elt ev ->
		Opt.iter (elt##parentNode) (fun node ->
		  Opt.iter (Dom.CoerceTo.element node) (fun dom_elt ->
		    let incr_elt = Dom_html.element dom_elt in
		    apply_incr incr_elt))));
	      refreshing_terms <- false;
	      let new_constr = term_constr in
	      self#refresh_new_term_constr current_constr new_constr)))))))

  val mutable refreshing_properties = false (* says whether a recomputation of property increments is ongoing *)
  method private refresh_property_increments current_constr =
    let get_incr_opt elt =
      let incr = html_state#dico_incrs#get (to_string (elt##id)) in
      (* retrieving selected increments for selection *)
      match incr with
      | Lisql.IncrSelection (selop,_) ->
	 let l_incr = property_selection#get in
	 if l_incr = []
	 then begin alert "Empty selection"; None end
	 else Some (Lisql.IncrSelection (selop, l_incr))
      | _ -> Some incr in
    let apply_incr elt =
      match get_incr_opt elt with
      | None -> ()
      | Some incr ->
	 navigation#update_focus
	   ~push_in_history:true
	   (let _ =
	      match incr with
	      | Lisql.IncrLatLong _ -> jquery_click "#nav-tab-map"
	      | _ -> () in
	    Lisql.insert_increment incr) in
    let toggle_incr elt =
      match get_incr_opt elt with
      | Some (Lisql.IncrType _ | Lisql.IncrRel _ | Lisql.IncrLatLong _ | Lisql.IncrPred _ as incr) ->
	 let _present = toggle_class elt "selected-incr" in
	 property_selection#toggle incr
      | _ -> ()
    in
    refreshing_properties <- true;
    jquery_select "#select-properties" (fun select ->
      jquery_input "#pattern-properties" (fun input ->
       jquery "#selection-properties-items" (fun elt_sel_items ->
	jquery "#list-properties" (fun elt_list ->
	 jquery_select "#select-sorting-properties" (fun sel_sorting ->
	 jquery_input "#input-inverse-properties" (fun input_inverse ->
	   lis#ajax_index_properties (norm_constr current_constr) elt_list
	    (fun ~partial -> function
	    | None ->
	       refreshing_properties <- false;
	       let new_constr = property_constr in
	       self#refresh_new_property_constr current_constr new_constr    
	    | Some index ->
	      input_inverse##checked <- bool inverse_properties;
	      sel_sorting##value <- string sorting_properties;
	      let html_sel, html_list, count =
		let inverse = to_bool input_inverse##checked in
		let sort_by_frequency = to_string sel_sorting##value = sorting_frequency in
		html_index lis#focus html_state index ~inverse ~sort_by_frequency in
	      elt_sel_items##innerHTML <- string html_sel;
	      elt_list##innerHTML <- string html_list;
	      elt_list##scrollTop <- property_scroll;
	      self#restore_expanded_properties;
	      jquery_set_innerHTML "#count-properties"
				   (html_count_unit { Lis.value=count; max_value=None; partial; unit=`Concepts } Lisql2nl.config_lang#grammar#concept_concepts);
	      property_selection#reset;
	      jquery_all_from elt_sel_items ".selection-increment" (onclick (fun elt ev ->
		 apply_incr elt));
	      jquery_all_from elt_list ".increment" (onclick (fun elt ev ->
		 if to_bool ev##ctrlKey
		 then toggle_incr elt
		 else apply_incr elt));
	      refreshing_properties <- false;
	      let new_constr = property_constr in
	      self#refresh_new_property_constr current_constr new_constr)))))))

  method private refresh_modifier_increments =
    let filter_dropdown_increment =
      let open Lisql in
      function
      | IncrThatIs | IncrSomethingThatIs | IncrTriplify | IncrHierarchy _
      | IncrSimRankIncr | IncrSimRankDecr
      | IncrAnd | IncrDuplicate | IncrOr | IncrChoice | IncrMaybe
      | IncrNot | IncrIn | IncrUnselect | IncrOrder _ -> true
      | _ -> false in
    let get_incr_opt elt =
      let incr = html_state#dico_incrs#get (to_string (elt##id)) in
      match incr with
      | Lisql.IncrName name ->
	 let ref_name = ref name in
	 jquery_input_from elt ".term-input" (fun input ->
	    ref_name := to_string input##value);
	 let name = !ref_name in
	 Some (Lisql.IncrName name)
      | Lisql.IncrSelection (selop,_) ->
	 let l_incr = modifier_selection#get in
	 if l_incr = []
	 then begin alert "Empty selection"; None end
	 else Some (Lisql.IncrSelection (selop, l_incr))
      | _ -> Some incr in
    let apply_incr elt =
      match get_incr_opt elt with
      | None -> ()
      | Some incr ->
	 navigation#update_focus
	   ~push_in_history:true
	   (Lisql.insert_increment incr) in
    let toggle_incr elt =
      match get_incr_opt elt with
      | Some (Lisql.IncrForeachId _ | Lisql.IncrAggregId _ as incr) ->
	 let _present = toggle_class elt "selected-incr" in
	 modifier_selection#toggle incr
      | _ -> ()
    in
    jquery "#selection-modifiers-items" (fun elt_sel_items ->
    jquery "#list-modifiers" (fun elt_list ->
    jquery "#focus-dropdown-content" (fun elt_dropdown ->
      let index = lis#index_modifiers in
      let html_sel, html_list, count =
	html_index
	  ~filter:(fun incr -> not (filter_dropdown_increment incr))
	  lis#focus html_state index
	  ~inverse:false ~sort_by_frequency:false in
      let _, html_drop, _ =
	html_index
	  ~filter:filter_dropdown_increment
	  lis#focus html_state index
	  ~inverse:false ~sort_by_frequency:false in
      elt_dropdown##innerHTML <- string html_drop;
      elt_sel_items##innerHTML <- string html_sel;
      elt_list##innerHTML <- string html_list;
      elt_list##scrollTop <- modifier_scroll;
      jquery_set_innerHTML "#count-modifiers"
			   (html_count_unit { Lis.value=count; max_value=None; partial=false; unit=`Modifiers } Lisql2nl.config_lang#grammar#modifier_modifiers);
      jquery "#focus-dropdown" (onclick (fun elt ev ->
	Dom_html.stopPropagation ev;
	jquery_toggle "#focus-dropdown-content"));
      jquery "#focus-dropdown" (onhover (fun elt ev ->
	Dom_html.stopPropagation ev;
	jquery_show "#focus-dropdown-content"));
      jquery "#focus-dropdown-content" (onhover_out (fun elt ev ->
	Dom_html.stopPropagation ev;
	jquery_hide "#focus-dropdown-content"));
      modifier_selection#reset;
      stop_propagation_from elt_list ".term-input";
      jquery_all_from elt_sel_items ".selection-increment" (onclick (fun elt ev ->
	 apply_incr elt));
      jquery_all_from elt_dropdown ".increment" (onclick (fun elt ev ->
	Dom_html.stopPropagation ev;
	apply_incr elt));
      jquery_all_from elt_list ".increment" (onclick (fun elt ev ->
	if to_bool ev##ctrlKey
	then toggle_incr elt
	else apply_incr elt));
      jquery_all_from elt_list ".term-input" (onenter (fun elt ev ->
	Opt.iter (elt##parentNode) (fun node ->
	  Opt.iter (Dom.CoerceTo.element node) (fun dom_elt ->
	    let incr_elt = Dom_html.element dom_elt in
	    apply_incr incr_elt)))))))

  method private refresh_sparql =
    function
    | None ->
       Jsutils.yasgui#set_query "SELECT * WHERE { }"
    | Some sparql ->
       let sparql_with_prefixes = Sparql.prologue#add_declarations_to_query sparql in
       Jsutils.yasgui#set_query sparql_with_prefixes
	   
  method refresh =
    Dom_html.window##history##replaceState(Js.null, string "", Js.some (string permalink));
    Dom_html.document##body##scrollTop <- document_scroll;
    Dom_html.document##documentElement##scrollTop <- document_scroll;
    jquery_input "#sparql-endpoint-input"
		 (fun input -> input##value <- string lis#endpoint);
    self#refresh_lisql;
    jquery "#increments" (fun elt_incrs ->
      jquery "#list-results" (fun elt_res ->
	let term_constr = term_constr in (* BECAUSE state term_constr can change any time *)
	let property_constr = property_constr in (* BECAUSE state property_constr can change any time *)
	lis#ajax_sparql_results (norm_constr term_constr) [elt_incrs; elt_res]
	  ~k_sparql:self#refresh_sparql
	  ~k_results:
	  (function
	  | None ->
	      (*Jsutils.yasgui#set_response "";
	      elt_res##style##display <- string "none";*)
	      self#refresh_extension;
	      self#refresh_constrs term_constr property_constr;
	      (*jquery_input "#pattern-terms" (fun input -> input##disabled <- bool true);*)
	      jquery_all ".list-incrs" (fun elt -> elt##innerHTML <- string "");
	      jquery_all ".count-incrs" (fun elt -> elt##innerHTML <- string "---");
	      self#refresh_modifier_increments;
	      self#refresh_property_increments property_constr;
	      self#refresh_term_increments term_constr;
	      self#refresh_focus (* after increments, because they have `FocusName words *)
	  | Some sparql ->
	      self#refresh_extension;
	      self#refresh_constrs term_constr property_constr;
	      jquery_input "#pattern-terms" (fun input -> input##disabled <- bool false);
	      self#refresh_modifier_increments;
	      self#refresh_property_increments property_constr;
	      self#refresh_term_increments term_constr;
	      self#refresh_focus)))

  method refresh_for_term_constr term_constr =
    (* same as method refresh, but assuming same query and focus *)
    jquery "#increments" (fun elt_incrs ->
      jquery "#list-results" (fun elt_res ->
	let property_constr = property_constr in (* BECAUSE state property_constr can change any time *)
	lis#ajax_sparql_results (norm_constr term_constr) [elt_incrs; elt_res]
	  ~k_sparql:self#refresh_sparql
	  ~k_results:
	  (function
	  | None ->
	      self#refresh_extension;
	      jquery_all ".list-incrs" (fun elt -> elt##innerHTML <- string "");
	      jquery_all ".count-incrs" (fun elt -> elt##innerHTML <- string "---");
	      self#refresh_modifier_increments;
	      self#refresh_property_increments property_constr;
	      self#refresh_term_increments term_constr
	  | Some sparql ->
	      self#refresh_extension;
	      self#refresh_modifier_increments;
	      self#refresh_property_increments property_constr;
	      self#refresh_term_increments term_constr)))

  method private get_more_results (k : unit -> unit) =
    jquery "#list-results"
	   (fun elt_res ->
	    lis#ajax_get_more_results
	      (norm_constr term_constr) [elt_res]
	      ~k_sparql:self#refresh_sparql
	      ~k_results:(fun _ -> k ()))
	   
  method private filter_increments ?on_modifiers elt_list constr =
    let matcher = compile_constr ?on_modifiers constr in
    let there_is_match = ref false in
    jquery_all_from elt_list "li" (fun elt_li ->
      jquery_from elt_li ".filterable-increment" (fun elt_incr ->
	let str =
	  match constr with
	  | Lisql.HasLang _
	  | Lisql.HasDatatype _ ->
	     to_string elt_incr##innerHTML (* TODO: extract proper lang/datatype part *)
	  | _ ->
	     if on_modifiers = Some true
	     then
	       let str =
		 Opt.case (elt_incr##textContent)
			  (fun () -> to_string elt_incr##innerHTML)
			  (fun s -> to_string s) in
	       replace_symbol_by_ascii str
	     else
	       Opt.case (elt_incr##querySelector(string ".function, .classURI, .propURI, .naryURI, .URI, .Literal, .nodeID, .modifier"))
			(fun () -> to_string elt_incr##innerHTML)
			(fun elt -> to_string elt##innerHTML) in
	if matcher str
	then begin elt_li##style##display <- string "list-item"; there_is_match := true end
	else elt_li##style##display <- string "none"))

  method is_home =
    Lisql.is_home_focus lis#focus

  method refresh_new_term_constr current_constr new_constr =
    let to_filter, to_refresh =
      if equivalent_constr new_constr current_constr then
	false, false
      else if config_auto_filtering#value && subsumed_constr new_constr current_constr then
	true, not refreshing_terms
      else (
	self#abort_all_ajax;
	true, true ) in
    if to_filter then begin
      jquery "#list-terms" (fun elt_list ->
	self#filter_increments elt_list new_constr)
      end;
    if to_refresh then begin (* not refreshing_terms && constr <> term_constr *)
      refreshing_terms <- true;
      self#save_ui_state;
      self#refresh_for_term_constr new_constr
      end

  method refresh_new_property_constr current_constr new_constr =
    let to_filter, to_refresh =
      if equivalent_constr new_constr current_constr then false, false
      else if subsumed_constr new_constr current_constr then true, not refreshing_properties
      else begin self#abort_all_ajax; true, true end in
    if to_filter then begin
      jquery "#list-properties" (fun elt_list ->
	 self#filter_increments elt_list new_constr)
      end;
    if to_refresh then begin (* not refreshing_properties && constr <> property_constr *)
      refreshing_properties <- true;
      self#save_ui_state;
      self#refresh_property_increments new_constr
      end

  method refresh_new_modifier_constr current_constr new_constr =
    let to_filter =
      not (equivalent_constr new_constr current_constr) in
    if to_filter then
      jquery "#list-modifiers" (fun elt_list ->
	 self#filter_increments ~on_modifiers:true elt_list new_constr)

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
    let process () =
      if offset' < lis#results_nb
      then begin
	  offset <- offset';
	  self#refresh_extension
	end
    in
    if offset' < lis#results_nb
    then process ()
    else self#get_more_results
	   (fun () -> process ())

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

  method more_results =
    self#get_more_results
      (fun () -> self#refresh_extension)
	   
  method abort_all_ajax =
    lis#abort_all_ajax;
    refreshing_terms <- false;
    refreshing_properties <- false


  method save_ui_state =
    document_scroll <-
      max
	Dom_html.document##body##scrollTop
	Dom_html.document##documentElement##scrollTop;
    jquery "#list-properties" (fun elt -> property_scroll <- elt##scrollTop);
    jquery "#list-terms" (fun elt -> term_scroll <- elt##scrollTop);
    jquery "#list-modifiers" (fun elt -> modifier_scroll <- elt##scrollTop);
    jquery_input "#input-inverse-terms" (fun input -> inverse_terms <- to_bool input##checked);
    jquery_input "#input-inverse-properties" (fun input -> inverse_properties <- to_bool input##checked);
    jquery_select "#select-sorting-terms" (fun select -> sorting_terms <- to_string select##value);
    jquery_select "#select-sorting-properties" (fun select -> sorting_properties <- to_string select##value);
    self#save_expanded_terms;
    self#save_expanded_properties
  method save_expanded_terms =
    expanded_terms <- [];
    jquery_all "#list-terms .input-treeview:checked"
	       (fun elt ->
		try
		  let incr = self#increment_of_elt elt in
		  expanded_terms <- incr :: expanded_terms
		with _ -> ())
  method save_expanded_properties =
    expanded_properties <- [];
    jquery_all "#list-properties .input-treeview:checked"
	       (fun elt ->
		try
		  let incr = self#increment_of_elt elt in
		  expanded_properties <- incr :: expanded_properties
		with _ -> ())
  method private increment_of_elt elt =
    let id = to_string elt##id in
    let key = Html.key_of_collapse id in
    html_state#dico_incrs#get key

			      
  method restore_expanded_terms =
    self#restore_expanded_gen expanded_terms
  method restore_expanded_properties =
    self#restore_expanded_gen expanded_properties
  method private restore_expanded_gen expanded =
    List.iter
      (fun incr ->
       match  html_state#dico_incrs#get_key incr with
       | Some key ->
	  let id = Html.collapse_of_key key in
	  jquery_input ("#" ^ id)
		       (fun input ->
			input##checked <- bool true)
       | None -> ())
      expanded

  method reinit =
    lis <- new Lis.place lis#endpoint lis#focus;
    html_state <- new Html.state lis#id_labelling;
    permalink <- permalink_of_place lis
      
  method new_place endpoint focus =
    let lis = new Lis.place endpoint focus in
    {< lis = lis;
       html_state = new Html.state lis#id_labelling;
       permalink = permalink_of_place lis;
       offset = 0;
       term_constr = Lisql.True (*Lisql.MatchesAll []*);
       property_constr = Lisql.True (*Lisql.MatchesAll []*);
       (* keeping same document scroll *)
       property_scroll = 0;
       term_scroll = 0;
       modifier_scroll = 0;
       (* keeping increment display options *)
       (* keeping expanded increments *) >}

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
    present#save_ui_state;
    config#set_endpoint url;
    jquery_set_innerHTML "#sparql-endpoint-title" dummy_title;
    let focus, delta = Lisql.factory#reset; Lisql.home_focus () in
    firebug ("delta = " ^ string_of_delta delta);
    let p = present#new_place url focus in
    p#set_navigation (self :> navigation);
    self#push p;
    p#refresh

  method update_focus ~push_in_history f =
    match f present#lis#focus with
      | None -> ()
      | Some (foc,delta) ->
	 firebug ("delta = " ^ string_of_delta delta);
	 present#abort_all_ajax;
	 present#save_ui_state;
	 let p = present#new_place present#lis#endpoint foc in
	 p#set_navigation (self :> navigation);
	 if push_in_history then self#push p else present <- p;
	 p#refresh

  method home =
    self#update_focus ~push_in_history:true
      (fun _ -> Lisql.factory#reset; Some (Lisql.home_focus ()))

  method back : unit =
    match past with
      | [] -> ()
      | p::lp ->
	 present#abort_all_ajax;
	 present#save_ui_state;
	 future <- present::future;
	 present <- p;
	 past <- lp;
	 p#refresh
	   
  method forward : unit =
    match future with
      | [] -> ()
      | p::lp ->
	 present#abort_all_ajax;
	 present#save_ui_state;
	 past <- present::past;
	 present <- p;
	 future <- lp;
	 p#refresh

  method refresh : unit =
    present#abort_all_ajax;
    present#save_ui_state;
    present#reinit;
    present#refresh
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
(* translating sorting options *)
  let options = Html.html_list_sorting () in
  jquery_set_innerHTML "#select-sorting-terms" options;
  jquery_set_innerHTML "#select-sorting-properties" options

let initialize endpoint focus =
  let history = new history endpoint focus in
  
  (* setting event callbacks *)
  jquery "#button-home" (onclick (fun elt ev -> history#home));
  jquery "#button-back" (onclick (fun elt ev -> history#back));
  jquery "#button-forward" (onclick (fun elt ev -> history#forward));
  jquery "#button-refresh" (onclick (fun elt ev -> history#refresh));
  jquery "#sparql-endpoint-button" (onclick (fun elt ev ->
     jquery_input "#sparql-endpoint-input" (fun input ->
        let url = to_string (input##value) in
	history#change_endpoint url)));
    jquery_input "#sparql-endpoint-input" (onenter (fun input ev ->
      jquery_click "#sparql-endpoint-button"));
    (*jquery "#config-control" (onclick (fun elt ev ->
      jquery "#config-panel" (fun panel ->
	let dis =
	  if to_string panel##style##display = "none"
	  then "block"
	  else "none" in
	panel##style##display <- string dis;
	if dis = "none" then
	  config#if_has_changed
	    ~translate
	    ~refresh:(fun () -> history#update_focus ~push_in_history:false (fun focus -> Some focus)))));*)
    jquery_all ".config-close" (onclick (fun elt ev ->
      config#if_has_changed
	~translate
	~refresh:(fun () -> history#update_focus ~push_in_history:false (fun focus -> Some (focus, Lisql.DeltaNil)))));
    jquery "#switch-view" (onclick (fun elt ev ->
      jquery_toggle "#sparklis-view";
      jquery_toggle "#yasgui-view";
      let view = jquery_toggle_innerHTML "#switch-view" "YASGUI view" "SPARKLIS view" in
      if view = "SPARKLIS view" then Jsutils.yasgui#refresh));

    jquery "#permalink" (onclick (fun elt ev -> history#present#show_permalink));

(*
    jquery "#show-hide-increments" (onclick (fun elt ev ->
      jquery_toggle "#increments-body";
      ignore (jquery_toggle_innerHTML "#show-hide-increments" (html_glyphicon "collapse-down") (html_glyphicon "collapse-up"))));
    jquery "#show-hide-results" (onclick (fun elt ev ->
      jquery_toggle "#list-results";
      ignore (jquery_toggle_innerHTML "#show-hide-results" (html_glyphicon "collapse-down") (html_glyphicon "collapse-up"))));
 *)
    
    jquery "#button-terms" (onclick (fun elt ev ->
      jquery_select "#select-terms" (fun select ->
	jquery_input "#pattern-terms" (fun input ->
	   let constr = norm_constr history#present#term_constr in
	   if constr = Lisql.True
	   then
	     Jsutils.alert "Empty filter"
	   else
	     history#update_focus ~push_in_history:true
				  (Lisql.insert_constr constr)))));

    List.iter
      (fun (getting_constr, input_changed,
	    sel_select, sel_input,
	    current_constr, k) ->
	jquery_select sel_select (fun select ->
	  jquery_input sel_input (fun input ->
	    let handler ~oninput input ev =
	      if oninput = config_auto_filtering#value || input##value##length = 0 then
		if !getting_constr
		then input_changed := true
		else
		  begin
		    getting_constr := true;
		    let current_constr = current_constr () in
		    get_constr
		      ~endpoint
		      current_constr
		      getting_constr input_changed
		      select input
		      (fun new_constr ->
		       k current_constr new_constr)
		  end
	      else if not oninput (* onenter, and auto-filtering *)
		      && sel_input = "#pattern-terms" then
		jquery_click "#button-terms"
	    in
	    (* register on both events, and handler decides based on config *)
	    oninput (handler ~oninput:true) input;
	    onenter (handler ~oninput:false) input)))
      [(ref false, ref false,
	"#select-terms", "#pattern-terms",
	(fun () -> history#present#term_constr),
	(fun current_constr new_constr ->
	 history#present#set_term_constr new_constr;
	 history#present#refresh_new_term_constr current_constr new_constr));
       (ref false, ref false,
	"#select-properties", "#pattern-properties",
	(fun () -> history#present#property_constr),
	(fun current_constr new_constr ->
	 history#present#set_property_constr new_constr;
	 history#present#refresh_new_property_constr current_constr new_constr));
       (ref false, ref false,
	"#select-modifiers", "#pattern-modifiers",
	(fun () -> history#present#modifier_constr),
	(fun current_constr new_constr ->
	 history#present#set_modifier_constr new_constr;
	 history#present#refresh_new_modifier_constr current_constr new_constr))];

    List.iter
      (fun (sel_btn,sel_list_incrs,checked) ->
       jquery sel_btn
	      (onclick
		 (fun elt ev ->
		  jquery_all
		    (sel_list_incrs ^ " .input-treeview")
		    (fun elt ->
		     Opt.iter
		       (Dom_html.CoerceTo.input elt)
		       (fun input -> input##checked <- bool checked)))))
      ["#button-expand-properties", "#list-properties", true;
       "#button-collapse-properties", "#list-properties", false;
       "#button-expand-terms", "#list-terms", true;
       "#button-collapse-terms", "#list-terms", false];
    List.iter
      (fun sel_select ->
       jquery_select sel_select
		     (onchange (fun select ev ->
				let place = history#present in
				place#save_ui_state;
				place#refresh)))
      ["#select-sorting-terms";
       "#select-sorting-properties"];
    List.iter
      (fun sel_input ->
       jquery_input sel_input
		    (onchange (fun input ev ->
			       let place = history#present in
			       place#save_ui_state;
			       place#refresh)))
      ["#input-inverse-terms";
       "#input-inverse-properties"];
    
    jquery "#previous-results" (onclick (fun elt ev -> history#present#page_up));
    jquery "#next-results" (onclick (fun elt ev -> history#present#page_down));
    jquery_select "#limit-results" (fun select -> select |> onchange (fun select ev ->
        firebug "changed limit-results";
	let limit = int_of_string (to_string (select##value)) in
	history#present#set_limit limit));
    jquery "#next-nested-table" (onclick (fun elt ev -> history#present#more_results));
    (* to force redraw of Google Map when changing BS tab *)
(*
    jquery "#nav-tab-map"
	       (onclick (fun elt ev ->
			 Dom_html.stopPropagation ev;
			 Unsafe.(meth_call elt "tab" [|inject (string "show")|])));
    
    jquery "#nav-tab-map" (fun elt ->
			   ignore (Dom_html.addEventListener
				     elt
				     (Dom_html.Event.make "shown.bs.tab")
				     (Dom_html.handler (fun ev -> firebug "shown.bs.tab FIRED"; bool true))
				     (bool false)));
 *)
    
    (* generating and displaying contents *)
    translate ();
    history#present#refresh

(* main *)
let _ =
  Firebug.console##log(string "Starting Sparklis");
  if logging_on () then
    Lwt.ignore_result (XmlHttpRequest.get url_log_php); (* counting hits *)
  Dom_html.window##onload <- Dom.handler (fun ev ->
   Jsutils.google#set_on_load_callback (fun () -> (* initializing Google charts *)
    (* initializing YASGUI and other libs *)
    Jsutils.yasgui#init;
    (* (try Jsutils.google#draw_map with exn -> firebug (Printexc.to_string exn));*)
    (* defining endpoint, title *)
    let args = Url.Current.arguments in
    let endpoint =
      try List.assoc "endpoint" args
      with Not_found ->  "http://servolis.irisa.fr/dbpedia/sparql" in
    let title =
      try List.assoc "title" args
      with Not_found -> "Core English DBpedia" in
    let endpoint = (* switching from lisfs2008 to servolis *)
      try List.assoc
	    endpoint
	    ["http://lisfs2008.irisa.fr/dbpedia/sparql", "http://servolis.irisa.fr/dbpedia/sparql";
	     "http://lisfs2008.irisa.fr/mondial/sparql", "http://servolis.irisa.fr/mondial/sparql"]
      with _ -> endpoint in
    config#init endpoint args;
    jquery_set_innerHTML "#sparql-endpoint-title" title;
    (* defining focus and navigation history *)
    let arg_query =
      try List.assoc "sparklis-query" args
      with Not_found ->
	   try List.assoc "query" args (* for backward compatibility of permalinks *)
	   with Not_found -> "" in
    Permalink.to_query
      arg_query
      (fun query_opt ->
       let focus =
	 match query_opt with
	 | Some query ->
	    let path =
	      try Permalink.to_path (List.assoc "sparklis-path" args)
	      with Not_found -> [] in
	    Lisql.focus_of_query_path query path
	 | None -> fst Lisql.factory#home_focus in
       initialize endpoint focus);
    bool true))

(*    
    let default_endpoint = ref "http://servolis.irisa.fr/dbpedia/sparql" in
    let default_title = ref "Core English DBpedia" in
    let default_focus = ref Lisql.factory#home_focus in
    let _ = (* changing endpoint, title, and focus if permalink *)
      let args = Url.Current.arguments in
      (*let args =
	match args with
	  | [] -> []
	  | (k,v)::l ->
	     let k = try String.sub k 1 (String.length k - 1) with _ -> firebug "osparklis.ml: removing '?' failed"; k in  (* bug: '?' remains in first key ==> bug fixed in js_of_ocaml 2.7 *)
	     (k, v)::l in*)
      (*Firebug.console##log(string (String.concat " & " (List.map (fun (k,v) -> k ^ " = " ^ v) args)));*)
      (try
	  let url = List.assoc "endpoint" args in
	  let url = (* switching from lisfs2008 to servolis *)
	    try List.assoc
		  url
		  ["http://lisfs2008.irisa.fr/dbpedia/sparql", "http://servolis.irisa.fr/dbpedia/sparql";
		   "http://lisfs2008.irisa.fr/mondial/sparql", "http://servolis.irisa.fr/mondial/sparql"]
	    with _ -> url in
	  default_endpoint := url;
	  default_title := (try List.assoc "title" args with _ -> dummy_title);
	  (try
	      Permalink.to_query
		(try List.assoc "sparklis-query" args
		 with _ -> List.assoc "query" args) (* for backward compatibility of permalinks *)
		(fun query ->
		 let path =
		   try Permalink.to_path (List.assoc "sparklis-path" args)
		   with _ -> [] in
		 default_focus := Lisql.focus_of_query_path query path)
	    with
	    | Stream.Failure -> Firebug.console##log(string "Permalink syntax error")
	    | Stream.Error msg -> Firebug.console##log(string ("Permalink syntax error: " ^ msg))
	    |  _ -> ())
       with _ -> ());
      (* setting title if any *)
      jquery_set_innerHTML "#sparql-endpoint-title" !default_title;
      (* initializing configuration from HTML *)
      config#init !default_endpoint args in
    (* creating and initializing history *)
    let history = new history !default_endpoint !default_focus in
 *)
