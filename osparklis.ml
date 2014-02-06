
open Js
open XmlHttpRequest
open Jsutils
open Lisql
open Html

(* LISQL constraints <--> user patterns *)

let string_is_float =
  let re = Regexp.regexp "^[+-]?(\\d+|\\d*[.]\\d+|\\d+[.]\\d*[eE][+-]?\\d+|[.]\\d+[eE][+-]?\\d+|\\d+[eE][+-]?\\d+)$" in
  (fun s -> Regexp.string_match re s 0 <> None)

let make_constr op pat =
  let lpat = List.filter ((<>) "") (Regexp.split (Regexp.regexp "[ ]+") pat) in
  if lpat = []
  then True
  else
    match op, lpat with
      | "matchesAll", _ -> MatchesAll lpat
      | "matchesAny", _ -> MatchesAny lpat
      | "after", pat::_ -> After pat
      | "before", pat::_ -> Before pat
      | "fromTo", pat1::[] -> After pat1
      | "fromTo", pat1::pat2::_ -> FromTo (pat1,pat2)
      | "higherThan", pat::_ ->
	if string_is_float pat 
	then HigherThan pat
	else invalid_arg "a numeric value is expected"
      | "lowerThan", pat::_ ->
	if string_is_float pat
	then LowerThan pat
	else invalid_arg "a numeric value is expected"
      | "between", pat::[] ->
	if string_is_float pat
	then HigherThan pat
	else invalid_arg "a numeric value is expected"
      | "between", pat1::pat2::_ ->
	if string_is_float pat1 && string_is_float pat2
	then Between (pat1, pat2)
	else invalid_arg "two numeric values are expected"
      | "hasLang", pat::_ -> HasLang pat
      | "hasDatatype", pat::_ -> HasDatatype pat
      | _ -> True

let operator_of_constr = function
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

let pattern_of_constr = function
  | True -> ""
  | MatchesAll lpat -> String.concat " " lpat
  | MatchesAny lpat -> String.concat " " lpat
  | After pat -> pat
  | Before pat -> pat
  | FromTo (pat1,pat2) -> pat1 ^ " " ^ pat2
  | HigherThan pat -> pat
  | LowerThan pat -> pat
  | Between (pat1,pat2) -> pat1 ^ " " ^ pat2
  | HasLang pat -> pat
  | HasDatatype pat -> pat

(* extraction of the extension and indexes *)

let page_of_results (offset : int) (limit : int) results : Sparql_endpoint.results =
  let open Sparql_endpoint in
  let rec aux offset limit = function
    | [] -> []
    | binding::l ->
      if offset > 0 then aux (offset-1) limit l
      else if limit > 0 then binding :: aux offset (limit-1) l
      else []
  in
  { results with bindings = aux offset limit results.bindings }

let list_of_results_column (var : Rdf.var) results : Rdf.term list =
  let open Sparql_endpoint in
  try
    let i = List.assoc var results.vars in
    List.sort
      (fun t1 t2 -> Pervasives.compare t2 t1)
      (List.fold_left
	 (fun res binding ->
	   match binding.(i) with
	     | None -> res
	     | Some t -> t::res)
	 [] results.bindings)
  with Not_found ->
    Firebug.console##log(string ("list_of_results_column: missing variable " ^ var));
    []

let index_of_results_column (var : Rdf.var) results : (Rdf.term * int) list =
  let open Sparql_endpoint in
  try
    let i = List.assoc var results.vars in
    let ht = Hashtbl.create 1000 in
    List.iter
      (fun binding ->
	match binding.(i) with
	  | None -> ()
	  | Some term ->
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

let index_of_results_2columns (var_x : Rdf.var) (var_count : Rdf.var) results : (Rdf.term * int) list =
  let open Sparql_endpoint in
  try
    let i_x = List.assoc var_x results.vars in
    let i_count = try List.assoc var_count results.vars with _ -> -1 in
    let index =
      List.fold_left
	(fun res binding ->
	  match binding.(i_x) with
	    | None -> res
	    | Some x ->
	      let count =
		if i_count < 0
		then 1
		else
		  match binding.(i_count) with
		    | Some (Rdf.Number (f,s,dt)) -> (try int_of_string s with _ -> 0)
		    | Some (Rdf.TypedLiteral (s,dt)) -> (try int_of_string s with _ -> 0)
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

(* dictionaries for foci and increments in user interface *)

class ['a] dico (prefix : string) =
object
  val mutable cpt = 0
  val ht : (string,'a) Hashtbl.t = Hashtbl.create 100

  method add (x : 'a) : string =
    cpt <- cpt + 1;
    let key = prefix ^ string_of_int cpt in
    Hashtbl.add ht key x;
    key

  method get (key : string) : 'a =
    try Hashtbl.find ht key
    with _ ->
      Firebug.console##log(string ("Missing element in dico: " ^ key));
      failwith "Osparqlis.dico#get"
end

class dico_foci =
object
  inherit [focus] dico "focus"
end

class dico_increments =
object
  inherit [increment] dico "incr"
  val dico_foci = new dico_foci
  method dico_foci = dico_foci
end

(* navigation place and history *)

class navigation =
object
  method change_endpoint (url : string) : unit = ()
  method update_focus ~(push_in_history : bool) (f : focus -> focus option) : unit = ()
end

class place =
object (self)
  (* constants *)

  val max_results = 200
  val max_classes = 200
  val max_properties = 1000

  (* essential state *)

(*  val endpoint = "http://dbpedia.org/sparql" *)
  val endpoint = "http://localhost:3030/ds/sparql"
  method endpoint = endpoint

  val focus = home_focus
  method focus = focus

  val mutable offset = 0
  val mutable limit = 10

  val mutable term_constr = True
  val mutable class_constr = True
  val mutable property_constr = True

  (* utilities *)

  val ajax_pool = new ajax_pool
  method abort_all_ajax = ajax_pool#abort_all

  val mutable navigation = new navigation
  method set_navigation (navig : navigation) = navigation <- navig

  (* derived state *)

  val mutable focus_term_opt : Rdf.term option = None
  val mutable query_opt : sparql_template option = None
  val mutable query_class_opt : sparql_template option = None
  val mutable query_prop_has_opt : sparql_template option = None
  val mutable query_prop_isof_opt : sparql_template option = None

  method init =
    begin
      let t_opt, q_opt, qc_opt, qph_opt, qpi_opt = sparql_of_focus focus in
      focus_term_opt <- t_opt;
      query_opt <- q_opt;
      query_class_opt <- qc_opt;
      query_prop_has_opt <- qph_opt;
      query_prop_isof_opt <- qpi_opt
    end

  initializer self#init

  val mutable dico_foci = new dico_foci
  val mutable results = Sparql_endpoint.empty_results
  val mutable focus_term_index : (Rdf.term * int) list = []
  val mutable dico_incrs = new dico_increments

  method private define_focus_term_index = (* requires 'results' to be defined *)
    focus_term_index <-
      ( match focus_term_opt with
	| None -> []
	| Some (Rdf.Var v) ->
	  List.filter
	    (function
	      | (Rdf.URI uri, _) when String.contains uri ' ' -> false
	      (* URIs with spaces inside are not allowed in SPARQL queries *)
	      | _ -> true)
	    (index_of_results_column v results)
	| Some t -> [(t, results.Sparql_endpoint.length)] )

  method private refresh_lisql =
    jquery "#lisql" (fun elt ->
      elt##innerHTML <- string (html_focus dico_foci focus);
      jquery_all_from elt ".focus" (onclick (fun elt_foc ev ->
	Dom_html.stopPropagation ev;
	navigation#update_focus ~push_in_history:false (fun _ ->
	  let key = to_string (elt_foc##id) in
	  Firebug.console##log(string key);
	  Some (dico_foci#get key))));
      jquery_from elt "#delete-current-focus"
	(onclick (fun elt_button ev ->
	  Dom_html.stopPropagation ev;
	  navigation#update_focus ~push_in_history:true delete_focus)))

  method private refresh_constrs =
    List.iter
      (fun (sel_select, sel_input, constr) ->
	jquery_select sel_select (fun select ->
	  jquery_input sel_input (fun input ->
	    select##value <- string (operator_of_constr constr);
	    input##value <- string (pattern_of_constr constr))))
      [("#select-terms", "#pattern-terms", term_constr);
       ("#select-classes", "#pattern-classes", class_constr);
       ("#select-properties", "#pattern-properties", property_constr);
       ("#select-modifiers", "#pattern-modifiers", True)]

  method private refresh_extension =
    let open Sparql_endpoint in
    jquery "#results" (fun elt_results ->
      if results.dim = 0 then begin
	elt_results##style##display <- string "none" end
      else begin
	elt_results##style##display <- string "block";
	jquery_set_innerHTML "#list-results"
	  (html_table_of_results
	     ~first_rank:(offset+1)
	     ~focus_var:(match focus_term_opt with Some (Rdf.Var v) -> v | _ -> "")
	     (page_of_results offset limit results));
	jquery_all ".count-results" (fun elt ->
	  elt##innerHTML <- string
	    (if results.Sparql_endpoint.length = 0
	     then "No results"
	     else
		let a, b = offset+1, min results.length (offset+limit) in
		if a = 1 && b = results.length && results.length < max_results then
		  string_of_int b ^ (if b=1 then " result" else " results")
		else
		  "Results " ^ string_of_int a ^ " - " ^ string_of_int b ^
		    " of " ^ string_of_int results.length ^ (if results.length < max_results then "" else "+")))
      end)

  method private refresh_term_increments =
    jquery "#list-terms" (fun elt ->
      elt##innerHTML <- string
	(html_increment_frequency_list focus dico_incrs
	   (List.rev_map (fun (t, freq) -> (IncrTerm t, freq)) focus_term_index));
      jquery_all_from elt ".increment" (onclick (fun elt ev ->
	navigation#update_focus ~push_in_history:true
	  (insert_increment (dico_incrs#get (to_string (elt##id)))))));
    jquery_set_innerHTML "#count-terms"
      (html_count_unit (List.length focus_term_index) max_results "term" "terms")

  method private refresh_class_increments_init =
    let process elt results =
      let class_list = list_of_results_column "class" results in
      elt##innerHTML <- string
	(html_increment_frequency_list focus dico_incrs
	   (List.fold_left
	      (fun res -> function
		| Rdf.URI c -> (IncrClass c, 1) :: res
		| _ -> res)
	      [] class_list));
      jquery_all_from elt ".increment" (onclick (fun elt ev ->
	navigation#update_focus ~push_in_history:true
	  (insert_increment (dico_incrs#get (to_string (elt##id))))));
      jquery_set_innerHTML "#count-classes"
	(html_count_unit (List.length class_list) 1000 "class" "classes")
    in
    jquery "#list-classes" (fun elt ->
      let sparql =
	"PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> " ^
	  "PREFIX owl: <http://www.w3.org/2002/07/owl#> " ^
	  "SELECT DISTINCT ?class WHERE { { ?class a rdfs:Class } UNION { ?class a owl:Class } " ^
	  sparql_constr (Rdf.Var "class") class_constr ^
	  " } LIMIT 1000" in
      Sparql_endpoint.ajax_in [elt] ajax_pool endpoint sparql
	(fun results ->
	  if results.Sparql_endpoint.length > 0
	  then process elt results
	  else
	    let sparql = "SELECT DISTINCT ?class WHERE { [] a ?class " ^ sparql_constr (Rdf.Var "class") class_constr ^ " } LIMIT 200" in
	    Sparql_endpoint.ajax_in [elt] ajax_pool endpoint sparql
	      (fun results -> process elt results)
	      (fun code -> process elt Sparql_endpoint.empty_results))
	(fun code -> process elt Sparql_endpoint.empty_results))

  method private refresh_property_increments_init =
    let process elt results =
      let prop_list = list_of_results_column "prop" results in
      elt##innerHTML <- string
	(html_increment_frequency_list focus dico_incrs
	   (List.fold_left
	      (fun res -> function
		| Rdf.URI c -> (IncrProp c, 1) :: (IncrInvProp c, 1) :: res
		| _ -> res)
	      [] prop_list));
      jquery_all_from elt ".increment" (onclick (fun elt ev ->
	navigation#update_focus ~push_in_history:true
	  (insert_increment (dico_incrs#get (to_string (elt##id))))));
      jquery_set_innerHTML "#count-properties"
	(html_count_unit (List.length prop_list) 1000 "property" "properties")
    in
    jquery "#list-properties" (fun elt ->
      let sparql =
	"PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> " ^
          "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> " ^
          "PREFIX owl: <http://www.w3.org/2002/07/owl#> " ^
          "SELECT DISTINCT ?prop WHERE { { ?prop a rdf:Property } UNION { ?prop a owl:ObjectProperty } UNION { ?prop a owl:DatatypeProperty } " ^
	  sparql_constr (Rdf.Var "prop") property_constr ^
	  " } LIMIT 1000" in
      Sparql_endpoint.ajax_in [elt] ajax_pool endpoint sparql
	(fun results ->
	  if results.Sparql_endpoint.length > 0
	  then process elt results
	  else
	    let sparql = "SELECT DISTINCT ?prop WHERE { [] ?prop [] " ^ sparql_constr (Rdf.Var "prop") property_constr ^ " } LIMIT 200" in
	    Sparql_endpoint.ajax_in [elt] ajax_pool endpoint sparql
	      (fun results -> process elt results)
	      (fun code -> process elt Sparql_endpoint.empty_results))
	(fun code -> process elt Sparql_endpoint.empty_results))

  method private refresh_class_increments =
    let process elt results =
      let class_index = index_of_results_column "class" results in
      elt##innerHTML <- string
	(html_increment_frequency_list focus dico_incrs
	   (List.fold_left
	      (fun res -> function
		| (Rdf.URI c, freq) -> (IncrClass c, freq) :: res
		| _ -> res)
	      [] class_index));
      jquery_all_from elt ".increment" (onclick (fun elt ev ->
	navigation#update_focus ~push_in_history:true
	  (insert_increment (dico_incrs#get (to_string (elt##id))))));
      jquery_set_innerHTML "#count-classes"
	(html_count_unit (List.length class_index) max_classes "class" "classes")
    in
    jquery "#list-classes" (fun elt ->
(*
	  let sparql =
	    let vals = String.concat " " (List.map (fun (t,_) -> sparql_term t) focus_term_index) in
	    "SELECT DISTINCT ?class (COUNT(DISTINCT ?focus) AS ?freq) WHERE { VALUES ?focus { " ^ vals ^ " } ?focus a ?class } GROUP BY ?class ORDER BY DESC(?freq) ?class LIMIT " ^ string_of_int max_classes in
*)
      let sparql =
	let lgp = List.map (fun (t,_) -> sparql_triple t (Rdf.URI "a") (Rdf.Var "class")) focus_term_index in
	sparql_select ~dimensions:["class"] ~limit:max_classes (sparql_join [sparql_union lgp; sparql_constr (Rdf.Var "class") class_constr]) in
      Sparql_endpoint.ajax_in [elt] ajax_pool endpoint sparql
	(fun results ->
	  if results.Sparql_endpoint.length > 0
	  then process elt results
	  else
	    match query_class_opt with
	      | None -> process elt Sparql_endpoint.empty_results
	      | Some query ->
		let sparql = query ~constr:class_constr ~limit:max_classes in
		Sparql_endpoint.ajax_in [elt] ajax_pool endpoint sparql
		  (fun results -> process elt results)
		  (fun code -> process elt Sparql_endpoint.empty_results))
	(fun code -> process elt Sparql_endpoint.empty_results))
      
  method private refresh_property_increments =
    let process elt results_has results_isof =
      let index_has = index_of_results_column "prop" results_has in (* increasing *)
      let index_isof = index_of_results_column "prop" results_isof in (* increasing *)
      let index =
	let rec aux acc l1 l2 =
	  match l1, l2 with
	    | (Rdf.URI c1, freq1)::r1, (_, freq2)::r2 when freq1 <= freq2 -> aux ((IncrProp c1, freq1)::acc) r1 l2
	    | (_, freq1)::r1, (Rdf.URI c2, freq2)::r2 when freq1 > freq2 -> aux ((IncrInvProp c2, freq2)::acc) l1 r2
	    | (Rdf.URI c1, freq1)::r1, [] -> aux ((IncrProp c1, freq1)::acc) r1 []
	    | [], (Rdf.URI c2, freq2)::r2 -> aux ((IncrInvProp c2, freq2)::acc) [] r2
	    | [], [] -> acc
	    | _ -> acc (* assert false *) in
	aux [] index_has index_isof in
      elt##innerHTML <- string
	(html_increment_frequency_list focus dico_incrs
	   index);
      jquery_all_from elt ".increment" (onclick (fun elt ev ->
	navigation#update_focus ~push_in_history:true
	  (insert_increment (dico_incrs#get (to_string (elt##id))))));
      jquery_set_innerHTML "#count-properties"
	(html_count_unit (List.length index_has + List.length index_isof) max_properties "property" "properties")
    in	
    jquery "#list-properties" (fun elt ->
(*
      let vals = String.concat " " (List.map (fun (t,_) -> sparql_term t) focus_term_index) in
      let sparql_has = "SELECT DISTINCT ?prop (COUNT (DISTINCT ?focus) AS ?freq) WHERE { VALUES ?focus { " ^ vals ^ " } ?focus ?prop [] } GROUP BY ?prop ORDER BY DESC(?freq) ?prop LIMIT " ^ string_of_int max_properties in
      let sparql_isof = "SELECT DISTINCT ?prop (COUNT(DISTINCT ?focus) AS ?freq) WHERE { VALUES ?focus { " ^ vals ^ " } [] ?prop ?focus } GROUP BY ?prop ORDER BY DESC(?freq) ?prop LIMIT " ^ string_of_int max_properties in
*)
      let sparql_has =
	let lgp = List.map (fun (t,_) -> sparql_triple t (Rdf.Var "prop") (Rdf.Bnode "")) focus_term_index in
	sparql_select ~dimensions:["prop"] ~limit:max_properties (sparql_join [sparql_union lgp; sparql_constr (Rdf.Var "prop") property_constr]) in
      let sparql_isof =
	let lgp = List.map (fun (t,_) -> sparql_triple (Rdf.Bnode "") (Rdf.Var "prop") t) focus_term_index in
	sparql_select ~dimensions:["prop"] ~limit:max_properties (sparql_join [sparql_union lgp; sparql_constr (Rdf.Var "prop") property_constr]) in
      Sparql_endpoint.ajax_list_in [elt] ajax_pool endpoint [sparql_has; sparql_isof]
	(function
	  | [results_has; results_isof] ->
	    if results_has.Sparql_endpoint.length > 0 || results_isof.Sparql_endpoint.length > 0
	    then process elt results_has results_isof
	    else
	      ( match query_prop_has_opt, query_prop_isof_opt with
	      | None, None -> process elt Sparql_endpoint.empty_results Sparql_endpoint.empty_results
	      | Some query_has, Some query_isof ->
		let sparql_has = query_has ~constr:property_constr ~limit:max_properties in
		let sparql_isof = query_isof ~constr:property_constr ~limit:max_properties in
		Sparql_endpoint.ajax_list_in [elt] ajax_pool endpoint [sparql_has; sparql_isof]
		  (function
		    | [results_has; results_isof] -> process elt results_has results_isof
		    | _ -> assert false)
		  (fun code -> process elt Sparql_endpoint.empty_results Sparql_endpoint.empty_results)
	      | _ -> assert false )
	  | _ -> assert false)
	(fun code -> process elt Sparql_endpoint.empty_results Sparql_endpoint.empty_results))

  method private refresh_modifier_increments =
    jquery "#list-modifiers" (fun elt ->
      let modif_list = (*focus_modifier_increments focus in*)
	match focus with
	  | AtP1 _ -> [IncrOr; IncrMaybe; IncrNot]
	  | AtS1 (Det (An (modif, head), _), _) ->
	    let modifs =
	      if List.exists (function (Rdf.Number _, _) -> true | _ -> false) focus_term_index
	      then List.map (fun g -> IncrModifS2 (Aggreg (None,g))) [Total; Average; Maximum; Minimum]
	      else [] in
	    let modifs =
	      if List.exists (function (Rdf.Number _, _) | (Rdf.PlainLiteral _, _) | (Rdf.TypedLiteral _, _) -> true | _ -> false) focus_term_index
	      then IncrModifS2 (Aggreg (None,ListOf)) :: modifs
	      else modifs in
	    let modifs =
	      IncrModifS2 Any :: IncrModifS2 (Aggreg (None,NumberOf)) :: modifs in
	    let modifs =
	      match modif with
		| Aggreg (_,g) -> IncrModifS2 (Aggreg (Some Highest, g)) :: IncrModifS2 (Aggreg (Some Lowest, g)) :: modifs
		| _ -> IncrModifS2 (Order Highest) :: IncrModifS2 (Order Lowest) :: modifs in
	    modifs
	  | _ -> [] in
      elt##innerHTML <- string
	(html_increment_frequency_list focus dico_incrs
	   (List.map (fun incr -> (incr,1)) modif_list));
      jquery_all_from elt ".increment" (onclick (fun elt ev ->
	navigation#update_focus ~push_in_history:true
	  (insert_increment (dico_incrs#get (to_string (elt##id))))));
      jquery_set_innerHTML "#count-modifiers"
	(html_count_unit (List.length modif_list) max_int "modifier" "modifiers"))

  method refresh =
    jquery_input "#sparql-endpoint-input" (fun input -> input##value <- string endpoint);
    self#refresh_constrs;
    dico_foci <- new dico_foci;
    dico_incrs <- new dico_increments;
    self#refresh_lisql;
    ( match focus_term_opt with
      | None -> jquery "#increments" (fun elt -> elt##style##display <- string "none")
      | Some _ -> jquery "#increments" (fun elt -> elt##style##display <- string "block") );
    ( match query_opt with
      | None ->
	jquery "#sparql" (fun elt -> elt##style##display <- string "none");
	jquery "#results" (fun elt -> elt##style##display <- string "none");
	jquery_input "#pattern-terms" (fun input -> input##disabled <- bool true);
	jquery_all ".list-incrs" (fun elt -> elt##innerHTML <- string "");
	jquery_all ".count-incrs" (fun elt -> elt##innerHTML <- string "---");
	( match focus_term_opt with
	  | None -> ()
	  | Some (Rdf.Var v) ->
	    self#refresh_class_increments_init;
	    self#refresh_property_increments_init
	  | Some term ->
	    focus_term_index <- [(term,1)];
	    self#refresh_term_increments;
	    self#refresh_class_increments;
	    self#refresh_property_increments;
	    self#refresh_modifier_increments )
      | Some query ->
	let sparql = query ~constr:term_constr ~limit:max_results in
	jquery_set_innerHTML "#sparql-query" (html_pre sparql);
	jquery "#sparql" (fun elt -> elt##style##display <- string "block");
	jquery "#results" (fun elt -> elt##style##display <- string "block");
	jquery_input "#pattern-terms" (fun input -> input##disabled <- bool false);
	jquery "#increments" (fun elt_incrs ->
	  jquery "#results" (fun elt_res ->
	    Sparql_endpoint.ajax_in [elt_incrs; elt_res] ajax_pool endpoint sparql
	      (fun res ->
		results <- res;
		self#refresh_extension;
		( match focus_term_opt with
		  | None -> ()
		  | Some t ->
		    self#define_focus_term_index;
		    self#refresh_term_increments;
		    self#refresh_class_increments;
		    self#refresh_property_increments;
		    self#refresh_modifier_increments ))
	      (fun code ->
		results <- Sparql_endpoint.empty_results;
		self#refresh_extension);
	    () )))

  method is_home =
    focus = home_focus

  method set_term_constr constr =
    if not self#is_home
    then begin
      Firebug.console##log(string "set_term_constr!");
      term_constr <- constr;
      self#refresh
    end

  method set_class_constr constr =
    if self#is_home
    then begin
      class_constr <- constr;
      self#refresh_class_increments_init end
    else begin
      class_constr <- constr;
      self#refresh_class_increments
    end

  method set_property_constr constr =
    if self#is_home
    then begin
      property_constr <- constr;
      self#refresh_property_increments_init end
    else begin
      property_constr <- constr;
      self#refresh_property_increments
    end

  method pattern_changed
    ~(select : Dom_html.selectElement t)
    ~(input : Dom_html.inputElement t)
    ~(elt_list : Dom_html.element t)
    (k : constr -> unit)
    =
    let op = to_string (select##value) in
    let pat = to_string (input##value) in
    Firebug.console##log(string pat);
    try
      let constr = make_constr op pat in
      let matcher = compile_constr constr in
      let there_is_match = ref false in
      jquery_all_from elt_list "li" (fun elt_li ->
	jquery_from elt_li ".increment" (fun elt_incr ->
	  let incr = dico_incrs#get (to_string (elt_incr##id)) in
	  let t =
	    match term_of_increment incr with
	      | Some t -> t
	      | None ->
		let s = Opt.case (elt_incr##querySelector(string ".modifier"))
		  (fun () -> to_string (elt_incr##innerHTML))
		  (fun elt -> to_string (elt##innerHTML)) in
		Rdf.PlainLiteral (s, "") in
	  if matcher t
	  then begin elt_li##style##display <- string "list-item"; there_is_match := true end
	  else elt_li##style##display <- string "none"));
      let n = String.length pat in
      if (not !there_is_match && (pat = "" || pat.[n - 1] = ' ')) || (n >= 2 && pat.[n-1] = ' ' && pat.[n-2] = ' ')
      then begin
	Firebug.console##log(string "pattern: no match, call k");
	k constr
      end
    with Invalid_argument msg -> ()

  method set_limit n =
    limit <- n;
    self#refresh_extension

  method give_more =
    if offset + limit < results.Sparql_endpoint.length
    then self#set_limit (limit+10)

  method give_less =
    if limit > 10
    then self#set_limit (limit-10)

  method page_down =
    let offset' = offset + limit in
    if offset' < results.Sparql_endpoint.length
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

  method new_place endpoint focus =
    let p =
      {< endpoint = endpoint;
	 focus = focus;
	 offset = 0;
	 term_constr = True;
	 class_constr = True;
	 property_constr = True; >} in
    p#init;
    p

end

let history =
object (self)
  val mutable past : place list = []
  val mutable present : place = new place
  val mutable future : place list = []

  initializer present#set_navigation (self :> navigation)

  method present : place = present

  method push (p : place) : unit =
    past <- present::past;
    present <- p;
    future <- []

  method change_endpoint url =
    present#abort_all_ajax;
    let p = present#new_place url home_focus in
    p#set_navigation (self :> navigation);
    self#push p;
    p#refresh

  method update_focus ~push_in_history f =
    match f present#focus with
      | None -> ()
      | Some foc ->
	present#abort_all_ajax;
	let p = present#new_place present#endpoint foc in
	p#set_navigation (self :> navigation);
	if push_in_history then self#push p else present <- p;
	p#refresh

  method home =
    self#update_focus ~push_in_history:true
      (fun _ -> Some home_focus)

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

let _ =
  Firebug.console##log(string "Starting Sparklis");
  Dom_html.window##onload <- Dom.handler (fun ev ->
    jquery "#home" (onclick (fun elt ev -> history#home));
    jquery "#back" (onclick (fun elt ev -> history#back));
    jquery "#forward" (onclick (fun elt ev -> history#forward));
    jquery "#sparql-endpoint-button" (onclick (fun elt ev ->
      jquery_input "#sparql-endpoint-input" (fun input ->
	let url = to_string (input##value) in
	history#change_endpoint url)));

    jquery "#button-terms" (onclick (fun elt ev ->
      jquery_select "#select-terms" (fun select ->
	jquery_input "#pattern-terms" (fun input ->
	  let op = to_string (select##value) in
	  let pat = to_string (input##value) in
	  try
	    let constr = make_constr op pat in
	    if constr = True
	    then
	      Dom_html.window##alert(string "Invalid filter")
	    else
	      history#update_focus ~push_in_history:true
		(insert_elt_p1 (Constr constr))
	  with Invalid_argument msg ->
	    Dom_html.window##alert(string ("Invalid filter: " ^ msg))))));
    List.iter
      (fun (sel_select, sel_input, sel_list, k) ->
	jquery_select sel_select (fun select ->
	  jquery_input sel_input (fun input ->
	    jquery sel_list (fun elt_list ->
	      (oninput
		 (fun input ev -> history#present#pattern_changed ~select ~input ~elt_list k)
		 input)))))
      [("#select-terms", "#pattern-terms", "#list-terms", (fun constr -> history#present#set_term_constr constr));
       ("#select-classes", "#pattern-classes", "#list-classes", (fun constr -> history#present#set_class_constr constr));
       ("#select-properties", "#pattern-properties", "#list-properties", (fun constr -> history#present#set_property_constr constr));
       ("#select-modifiers", "#pattern-modifiers", "#list-modifiers", (fun constr -> ()))];
    
    jquery_all ".previous-results" (onclick (fun elt ev -> history#present#page_up));
    jquery_all ".next-results" (onclick (fun elt ev -> history#present#page_down));
    jquery_all ".limit-results" (fun elt ->
      Opt.iter (Dom_html.CoerceTo.select elt) (onchange (fun select ev ->
	Firebug.console##log(select##value);
	let limit = int_of_string (to_string (select##value)) in
	history#present#set_limit limit)));

    history#present#refresh;
    bool true)
