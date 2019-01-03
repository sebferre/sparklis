(*
  Copyright 2013-2017 Sébastien Ferré, IRISA, Université de Rennes 1

  This file is part of Sparklis.
*)

open Js
open Jsutils
open Lisql
open Lisql_annot

(* configuration elements *)

let config_logo_height = new Config.integer_input ~key:"logo_height" ~input_selector:"#input-logo-height" ~min:8 ~default:20 ()
       
(* generic dictionary with automatic generation of keys *)

class ['a] dico (prefix : string) =
object
  val mutable cpt = 0
  val ht : (string,'a) Hashtbl.t = Hashtbl.create 101
  val rev_ht : ('a,string) Hashtbl.t = Hashtbl.create 101

  method add (x : 'a) : string =
    try Hashtbl.find rev_ht x
    with Not_found ->
      let k = cpt <- cpt + 1; prefix ^ string_of_int cpt in
      Hashtbl.add ht k x;
      Hashtbl.add rev_ht x k;
      k

  method add_key (key : string) (x : 'a) : unit =
    Hashtbl.add ht key x;
    Hashtbl.add rev_ht x key

  method get (key : string) : 'a =
    try Hashtbl.find ht key
    with _ ->
      Firebug.console##log(string ("Missing element in dico: " ^ key));
      failwith "Osparqlis.dico#get"

  method get_key (x : 'a) : string option =
    try Some (Hashtbl.find rev_ht x)
    with Not_found -> None
end

(* HTML state with dictionaries for foci and increments in user interface *)

let focus_key_of_root = "root"
let focus_key_of_id (id : Lisql.id) : string = "id" ^ string_of_int id

let collapse_of_key key = "collapse-" ^ key
let key_of_collapse =
  let l = String.length "collapse-" in
  fun s -> String.sub s l (String.length s - l)

type results_view = Table | Slideshow
		      
class state (id_labelling : Lisql2nl.id_labelling) =
object
  method id_labelling = id_labelling
  val dico_foci : Lisql.focus dico = new dico "focus"
  val alias : (string,string) Hashtbl.t = Hashtbl.create 13
  method add_focus (focus : Lisql.focus) : string =
    let key = dico_foci#add focus in
    (if Lisql.is_root_focus focus then
      Hashtbl.add alias focus_key_of_root key);
    ( match Lisql.id_of_focus focus with
      | Some id -> Hashtbl.add alias (focus_key_of_id id) key
      | None -> () );
    key
  method get_focus (key : string) : Lisql.focus =
    let key =
      try Hashtbl.find alias key (* in case [key] is an alias *)
      with Not_found -> key in
    dico_foci#get key

  val dico_incrs : Lisql.increment dico = new dico "incr"
  method dico_incrs = dico_incrs

  val dico_results : (results_view * int * Lisql.id * Rdf.term) dico = new dico "cell"
  method dico_results = dico_results
end

(* LISQL constraints <--> user patterns *)

let string_is_float =
  let re = Regexp.regexp "^[+-]?(\\d+|\\d*[.]\\d+|\\d+[.]\\d*[eE][+-]?\\d+|[.]\\d+[eE][+-]?\\d+|\\d+[eE][+-]?\\d+)$" in
  (fun s -> Regexp.string_match re s 0 <> None)

let make_constr op pat =
  (* BEWARE: call [norm_constr] on result for any semantic use *)
  let open Lisql in
  let lpat = List.filter ((<>) "") (Regexp.split (Regexp.regexp "[ ]+") pat) in
  match op, lpat with
  | "true", _ -> True
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
  | _ -> True (* in case of undefined option *)
    
let option_of_constr =
  let open Lisql in
  function
  | True -> "true"
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
			 
  
(* pretty-printing of terms, NL in HTML *)

let html_pre text =
  let text = Regexp.global_replace (Regexp.regexp "<") text "&lt;" in
  let text = Regexp.global_replace (Regexp.regexp ">") text "&gt;" in  
  "<pre>" ^ text ^ "</pre>"

let html_span ?id ?classe ?title text =
  "<span" ^
    (match id with None -> "" | Some id -> " id=\"" ^ id ^ "\"") ^
    (match classe with None -> "" | Some cl -> " class=\"" ^ cl ^ "\"") ^
    (match title with None -> "" | Some tit -> " title=\"" ^ tit ^ "\"") ^
    ">" ^ text ^ "</span>"

let html_div ?classe ?title text =
  "<div" ^
    (match classe with None -> "" | Some cl -> " class=\"" ^ cl ^ "\"") ^
    (match title with None -> "" | Some tit -> " title=\"" ^ tit ^ "\"") ^
    ">" ^ text ^ "</div>"

let html_a url html =
  "<a target=\"_blank\" href=\"" ^ url ^ "\">" ^ html ^ "</a>"

let html_img ?id ?classe ?height ~alt ~title url =
  "<img" ^
    (match id with None -> "" | Some i -> " id=\"" ^ i ^ "\"") ^
    (match classe with None -> "" | Some c -> " class=\"" ^ c ^ "\"") ^
    " src=\"" ^ url ^ "\"" ^
    (match height with None -> "" | Some h -> " height=\"" ^ string_of_int h ^ "\"") ^
    " alt=\"" ^ alt ^ "\" title=\"" ^ title ^ "\">"

let html_option ~value label =
  "<option value=\"" ^ value ^ "\">" ^ label ^ "</option>"						
let html_video url =
  let mime =
    if Rdf.uri_has_ext url ["mp4"; "MP4"] then "video/mp4"
    else if Rdf.uri_has_ext url ["mov"; "MOV"] then "video/quicktime"
    else if Rdf.uri_has_ext url ["ogg"; "OGG"] then "video/ogg"
    else "video" in
  "<video width=\"320\" height=\"240\" controls>\
   <source src=\"" ^ url ^ "\" type=\"" ^ mime ^ "\">\
   Your browser does not support the video tag.\
   </video>"

let html_audio url =
  let mime =
    if Rdf.uri_has_ext url ["mp3"; "MP3"] then "audio/mpeg"
    else "audio" in
  "<audio controls>\
   <source src=\"" ^ url ^ "\" type=\"" ^ mime ^ "\">\
   Your browser does not support this audio format.\
   </audio>"

let html_glyphicon name = "<span class=\"glyphicon glyphicon-" ^ name ^ "\"></span>"

let html_open_new_window ~height uri =
  html_a uri (html_img ~classe:"open-new-window" ~height ~alt:"Open" ~title:Lisql2nl.config_lang#grammar#tooltip_open_resource "icon-open-new-window.png")

let html_delete ?id ~title () =
  html_img ?id ~height:16 ~alt:"Delete" ~title "icon-delete.png"

let html_literal s = html_span ~classe:"Literal" (escapeHTML s)
let html_uri ~classe uri s = html_span ~classe ~title:uri (escapeHTML s)
let html_function f = html_span ~classe:"function" (escapeHTML f)
let html_modifier m = html_span ~classe:"modifier" (escapeHTML m)

let html_logos uri =
  let logo_urls = Ontology.config_show_logo#value#info uri in
  let logo_urls =
    if Rdf.uri_is_image uri
    then uri :: logo_urls
    else logo_urls in
  let height = config_logo_height#value in
  String.concat
    ""
    (List.map
       (fun logo_url ->
	let name = Filename.basename logo_url in
	html_img ~classe:"uri-logo" ~height ~alt:"" ~title:name logo_url)
       logo_urls)
				
let html_word = function
  | `Thing -> Lisql2nl.config_lang#grammar#thing
  | `Relation -> html_modifier Lisql2nl.config_lang#grammar#relation
  | `Literal s -> html_literal s
  | `TypedLiteral (s,t) ->
    if Lisql2nl.config_show_datatypes#value
    then html_literal s ^ " (" ^ escapeHTML t ^ ")"
    else html_literal s
  | `Blank id -> html_span ~classe:"nodeID" (escapeHTML id) ^ " (bnode)"
  | `Entity (uri,s) -> html_logos uri ^ html_uri ~classe:"URI" uri s ^ " " ^ html_open_new_window ~height:12 uri
  | `Class (uri,s) -> html_logos uri ^ html_uri ~classe:"classURI" uri s
  | `Prop (uri,s) -> html_logos uri ^ html_uri ~classe:"propURI" uri s
  | `Nary (uri,s) -> html_logos uri ^ html_uri ~classe:"naryURI" uri (escapeHTML s)
  | `Func s -> html_span ~classe:"function" (escapeHTML s)
  | `Op op -> html_modifier op
  | `Undefined -> "___"
  | `FocusSpan -> html_span ~classe:"highlighted" "___"
  | `FocusName -> html_span ~classe:"focus-ng" "thing"

let html_input dt =
  let t, hint =
    match dt with
    | `IRI -> "url", "http://"
    | `String -> "text", ""
    | `Float -> "number", "0.0e+0"
    | `Integer -> "number", "0"
    | `Date -> "text", "yyyy-mm-dd"
    | `Time -> "text", "hh:mm:ss"
    | `DateTime -> "text", "yyyy-mm-ddThh:mm:ss"
    | `Duration -> "text", "PxYxMxDTxHxMx.xS"
  in
  "<input class=\"term-input\" type=\"" ^ t ^ "\" placeholder=\"" ^ hint ^ "\">"

let html_freq ~unit ~partial value =
  if value = 1
  then ""
  else
    let s = string_of_int value in
    let s = if partial then s ^ "+" else s in
    ( match unit with
      | `Results -> html_span ~classe:"frequency-results" ~title:"number of results matching this" s
      | `Entities -> html_span ~classe:"frequency-entities" ~title:"number of entities matching this" s
      | `Concepts | `Modifiers -> " <" ^ s ^ ">" (* should not happen *)
    )

let append_node_to_xml node xml =
  List.rev (node :: List.rev xml)
let append_node_to_xml_list node lxml =
  match List.rev lxml with
  | [] -> [[node]]
  | last::rest -> List.rev (append_node_to_xml node last :: rest)
    
let rec html_of_nl_xml ?(highlight=false) (state : state) (xml : Lisql2nl.xml) : string =
  let open Lisql2nl in
  match xml with
  | Enum (sep,lxml) :: DeleteCurrentFocus :: xml ->
    html_of_nl_xml ~highlight state (Enum (sep, append_node_to_xml_list DeleteCurrentFocus lxml) :: xml)
  | Coord (coord,lxml) :: DeleteCurrentFocus :: xml ->
    html_of_nl_xml ~highlight state (Coord (coord, append_node_to_xml_list DeleteCurrentFocus lxml) :: xml)
  | Focus (foc,xml1) :: DeleteCurrentFocus :: xml ->
    html_of_nl_xml ~highlight state (Focus (foc, append_node_to_xml DeleteCurrentFocus xml1) :: xml)
  | Highlight xml1 :: DeleteCurrentFocus :: xml ->
    html_of_nl_xml ~highlight state (Highlight (append_node_to_xml DeleteCurrentFocus xml1) :: xml)
  | Focus (foc1, xml1) :: Focus (foc2, xml2) :: xml when foc1 = foc2 -> html_of_nl_xml ~highlight state (Focus (foc1, xml1 @ xml2) :: xml)
  | Highlight xml1 :: Highlight xml2 :: xml -> html_of_nl_xml ~highlight state (Highlight (xml1 @ xml2) :: xml)
  | node :: xml -> html_of_nl_node ~highlight state node ^ (if xml=[] then "" else " " ^ html_of_nl_xml ~highlight state xml)
  | [] -> ""
and html_of_nl_node ?(highlight=false) (state : state) : Lisql2nl.node -> string = 
  let open Lisql2nl in
  function
    | Kwd s -> s
    | Word w -> html_word w
    | Input dt -> html_input dt
    | Selection xml_selop -> html_of_nl_xml ~highlight state xml_selop
    | Suffix (xml,suf) -> html_of_nl_xml ~highlight state xml ^ suf
    | Enum (sep,lxml) -> String.concat sep (List.map (html_of_nl_xml ~highlight state) lxml)
    | Quote (left, xml, right) -> left ^ html_of_nl_xml ~highlight state xml ^ right
    | Coord (coord,lxml) ->
      "<ul class=\"coordination\"><li>"
      ^ String.concat ("</li><li> " ^ html_highlight highlight (html_of_nl_xml ~highlight state coord ^ " "))
	(List.map (fun xml -> html_highlight highlight (html_of_nl_xml ~highlight state xml)) lxml)
      ^ "</li></ul>"
    | Focus (focus,xml) ->
      let id = state#add_focus focus in
      html_span ~id ~classe:"focus" (html_of_nl_xml ~highlight state xml)
    | Highlight xml ->
      html_highlight true (html_of_nl_xml ~highlight:true state xml)
    | Suspended xml ->
      html_span ~classe:"suspended" (html_of_nl_xml ~highlight state xml)
    | DeleteCurrentFocus ->
      html_delete ~id:"delete-current-focus" ~title:Lisql2nl.config_lang#grammar#tooltip_delete_current_focus ()
    | DeleteIncr ->
      html_delete ~title:Lisql2nl.config_lang#grammar#tooltip_remove_element_at_focus ()
and html_highlight h xml =
  if h
  then html_span ~classe:"highlighted" xml
  else xml

(* HTML of different AST elements *)

let html_term (t : Rdf.term) : string =
  html_word (Lisql2nl.word_of_term t)

let html_query (state : state) (query : annot elt_s) : string =
  html_of_nl_xml state
    (Lisql2nl.xml_of_elt_s
       Lisql2nl.config_lang#grammar
       ~id_labelling:state#id_labelling
       query)

let html_id_np (state : state) (id : int) : string =
  html_of_nl_xml state
    (Lisql2nl.xml_np_id
       Lisql2nl.config_lang#grammar
       ~id_labelling:state#id_labelling
       id)
let html_id_ng (state : state) (id : int) : string =
  html_of_nl_xml state
    (Lisql2nl.xml_ng_id
       Lisql2nl.config_lang#grammar
       ~id_labelling:state#id_labelling
       id)

(* HTML of increment lists *)

type compare_incr_data = (float * int) option * int * [`Words of string list | `Number of float]
(* (position, freqency) opt, rank, data *)

let compare_incr ~(use_freq : bool) (pf1_opt,r1,d1 : compare_incr_data) (pf2_opt,r2,d2 : compare_incr_data) : int =
  let compare3 () = (* sort according to data *)
    match d1, d2 with
    | `Number f1, `Number f2 -> Pervasives.compare f1 f2
    | `Number _, `Words _ -> 1 (* words before numbers *)
    | `Words _, `Number _ -> -1
    | `Words lw1, `Words lw2 ->
       if List.for_all (fun w1 -> List.mem w1 lw2) lw1 then -1
       else if List.for_all (fun w2 -> List.mem w2 lw1) lw2 then 1
       else Pervasives.compare lw1 lw2 in
  let compare2 () = (* sort by rank *)
    if r1 < r2 then -1
    else if r1 > r2 then 1
    else compare3 () in
  let compare1 () =
    match pf1_opt, pf2_opt with
    | None, None -> compare2 ()
    | None, Some _ -> compare2 ()
    | Some _, None -> compare2 ()
    | Some pf1, Some pf2 ->
       if use_freq
       then (* sort by position, then frequency *)
	 if pf1 < pf2 then -1
	 else if pf1 > pf2 then 1
	 else compare2 ()
       else (* sort by position *)
	 let p1, p2 = fst pf1, fst pf2 in
	 if p1 < p2 then -1
	 else if p1 > p2 then 1
	 else compare2 () in
  compare1 ()
	  
let html_count_unit freq (unit,units) =
  let count = freq.Lis.value in
  let s_count = string_of_int count in
  let s_count = if freq.Lis.partial then s_count ^ "+" else s_count in
  if count = 0 then Lisql2nl.config_lang#grammar#no ^ " " ^ unit
  else if count = 1 then s_count ^ " " ^ unit
  else s_count ^ " " ^ units

let freq_text_html_increment_frequency focus (state : state) (incr,freq_opt) : compare_incr_data * string * bool * string =
  let key = state#dico_incrs#add incr in
  let grammar = Lisql2nl.config_lang#grammar in
  let xml = Lisql2nl.xml_of_incr grammar ~id_labelling:state#id_labelling focus incr in
  let html = html_of_nl_xml state xml in
  let uri_opt = Lisql.uri_of_increment incr in
  let pf_opt, html_freq =
    match freq_opt with
    | None -> None, ""
    (*| Some {Lis.value=1} -> Some (position, -1), ""*)
    | Some {Lis.value; max_value; partial; unit} ->
       let position =
	 match uri_opt with
	 | None -> max_float
	 | Some uri ->
	    match Ontology.config_sort_by_position#value#info uri with
	    | [] -> max_float
	    | x::xs -> List.fold_left max x xs in
       let sort_frequency = -value in (* '-' opposite for decreasing frequency ordering *)
       let html_freq = html_freq ~unit ~partial value in
	     (*let s = match max_value with None -> s | Some max -> s ^ "/" ^ string_of_int max in*)
       Some (position, sort_frequency), html_freq in
  let data = 
    let text =
      String.lowercase
	(Lisql2nl.word_text_content
	   grammar
	   (Lisql2nl.word_of_incr grammar incr)) in
    try `Number (float_of_string text)
    with _ -> `Words (Regexp.split (Regexp.regexp "[- ,;:.()]+") text) in
  let rank, title_opt =
    match incr with
      | IncrSelection _ -> 0, None
      (* concept increments *)
      | IncrHierarchy _ -> 1, Some grammar#tooltip_hierarchy
      | IncrArg _ -> 2, None
      | IncrType _ -> 3, None
      | IncrLatLong _ -> 4, Some grammar#tooltip_geolocation
      | IncrRel _ -> 4, None
      | IncrPred _ -> 4, None
      | IncrTriple _ -> 7, None
      | IncrInWhichThereIs -> 8, None (* TODO: tooltip *)
      (* term increments *)
      | IncrAnything -> 1, None
      | IncrId _ -> 2, None
      | IncrInput _ -> 3, None
      | IncrTerm _ -> 4, None
      (* modifier increments *)
      | IncrName _ -> 1, Some grammar#tooltip_input_name
      | IncrOrder (Highest _) -> 2, Some grammar#tooltip_highest
      | IncrOrder (Lowest _) -> 3, Some grammar#tooltip_lowest
      | IncrOrder _ -> 4, None
      | IncrUnselect -> 5, Some grammar#tooltip_any
      | IncrForeachResult -> 6, Some grammar#tooltip_foreach_result
      | IncrForeachId _ -> 7, Some grammar#tooltip_foreach_id
      | IncrAggregId (Sample,_) -> 9, Some grammar#tooltip_aggreg_id
      | IncrAggregId _ -> 8, Some grammar#tooltip_aggreg_id

      | IncrAnd -> 10, None
      | IncrDuplicate -> 11, Some grammar#tooltip_duplicate_focus
      | IncrOr -> 12, Some grammar#tooltip_or
      | IncrChoice -> 13, Some grammar#tooltip_or
      | IncrMaybe -> 14, Some grammar#tooltip_optionally
      | IncrNot -> 15, Some grammar#tooltip_not
      | IncrThatIs -> 16, None
      | IncrSomethingThatIs -> 17, None

      | IncrForeach -> 18, Some grammar#tooltip_foreach
      | IncrAggreg Sample -> 20, Some grammar#tooltip_aggreg
      | IncrAggreg _ -> 19, Some grammar#tooltip_aggreg
      | IncrFuncArg _ -> 21, Some grammar#tooltip_func

      | IncrTriplify -> 22, Some grammar#tooltip_focus_on_property
      | IncrIn -> 23, None (* TODO: tooltip *) in
  let filterable =
    match incr with
    | IncrAnything
    | IncrSelection _
    | IncrHierarchy _
    | IncrTriple _
    | IncrTriplify -> false
    | _ -> true in
  let sort_data = (pf_opt, rank, data) in
  let is_selection_incr, html =
    match incr with
    | IncrSelection _ ->
       true, "<button id=\"" ^ key ^ "\" class=\"btn btn-default selection-increment\">" ^ html ^ "</button> "
    | _ ->
       let classe =
	 if filterable then "increment filterable-increment"
	 else "increment" in
       false, html_span ~id:key ~classe ?title:title_opt (html ^ html_freq) in
  sort_data, key, is_selection_incr, html

(* TODO: avoid to pass focus as argument, use NL generation on increments *)
let html_index focus (state : state) (index : Lis.incr_freq_index) ~(sort_by_frequency : bool): string * string * int =
  let sort_node_list nodes =
    List.sort
      (fun (`Node ((data1,_,_,_),_)) (`Node ((data2,_,_,_),_)) -> compare_incr ~use_freq:sort_by_frequency data1 data2)
      nodes in
  let rec aux buf_sel buf_tree ref_count nodes =
    let sorted_nodes = sort_node_list nodes in
    Buffer.add_string buf_tree "<ul>";
    List.iter
      (fun (`Node ((_,key,is_selection_incr,html), children)) ->
       if is_selection_incr
       then begin
	   Buffer.add_string buf_sel html end
       else begin
	 let check_id = collapse_of_key key in
	 Buffer.add_string buf_tree "<li class=\"col-xs-11\">";
	 if children = [] then begin
	     Buffer.add_string buf_tree "<label style=\"visibility:hidden;\">►&nbsp;</label>";
	     Buffer.add_string buf_tree html
	   end
	 else begin
	     Buffer.add_string buf_tree ("<input class=\"input-treeview\" type=\"checkbox\" id=\"" ^ check_id ^ "\">");
	     Buffer.add_string buf_tree ("<label for=\"" ^ check_id ^ "\" class=\"label-checked\">▼&nbsp;</label>");
	     Buffer.add_string buf_tree ("<label for=\"" ^ check_id ^ "\" class=\"label-unchecked\">►&nbsp;</label>");
	     Buffer.add_string buf_tree html;
	     aux buf_sel buf_tree ref_count children
	   end;
	 Buffer.add_string buf_tree "</li>";
	 incr ref_count end)
      sorted_nodes;
    Buffer.add_string buf_tree "</ul>"
  in
  let enriched_index_tree = index#map_tree (freq_text_html_increment_frequency focus state) in
  let buf_sel = Buffer.create 100 in
  let buf_tree = Buffer.create 1000 in
  let ref_count = ref 0 in
  aux buf_sel buf_tree ref_count enriched_index_tree;
  Buffer.contents buf_sel, Buffer.contents buf_tree, !ref_count

let html_list_constr (state : state) (lc : Lisql.constr list) : string =
  let grammar = Lisql2nl.config_lang#grammar in
  let id_labelling = state#id_labelling in
  String.concat
    ""
    (List.map
       (fun c ->
	let value = option_of_constr c in
	let label =
	  html_of_nl_xml state
	    (Lisql2nl.xml_of_constr grammar ~id_labelling c) in
	html_option ~value label)
       lc)

let html_list_sorting () : string =
  let grammar = Lisql2nl.config_lang#grammar in
  let ls = (* so far, static list of sorting options *)
    ["frequency", grammar#sorting_frequency;
     "alphanum", grammar#sorting_alphanum] in
  String.concat
    ""
    (List.map
       (fun (value,label) ->
	html_option ~value label)
       ls)
    
(* HTML of results *)

let html_cell_img ?height url =
  let label = Lexicon.name_of_uri url in
  html_img ?height ~alt:label ~title:label url ^ html_open_new_window ~height:16 url

let html_cell_video url =
  html_video url ^ html_open_new_window ~height:16 url

let html_cell_audio url =
  html_audio url ^ html_open_new_window ~height:16 url

let html_cell_contents (t : Rdf.term) =
  match t with
  | Rdf.URI uri ->
     if Rdf.uri_is_image uri then html_cell_img ~height:120 uri
     else if Rdf.uri_is_video uri then html_cell_video uri
     else if Rdf.uri_is_audio uri then html_cell_audio uri
     else html_word (Lisql2nl.word_of_term t)
  | _ -> html_word (Lisql2nl.word_of_term t)
			 
let html_cell state ~(view : results_view) ~(rank : int) ~(column : Lisql.id) t =
  let contents = html_cell_contents t in
  let key = state#dico_results#add (view,rank,column,t) in
  html_span ~id:key ~classe:"cell" contents

let html_table_of_results (state : state) ~partial ~first_rank ~focus_var results counts =
  let open Sparql_endpoint in
  assert (List.length results.vars = List.length counts);
  let focus_id = match focus_var with None -> -1 | Some v -> state#id_labelling#get_var_id v in
  let id_i_n_list =
    List.map2
      (fun (var,i) count -> (state#id_labelling#get_var_id var, i, count))
      results.vars counts in
  let buf = Buffer.create 1000 in
  Buffer.add_string buf ("<div class=\"table-responsive\"><table id=\"extension\" class=\"table table-bordered table-condensed table-hover\"><tr><th id=\"" ^ focus_key_of_root ^ "\" class=\"header\" title=\"" ^ Lisql2nl.config_lang#grammar#tooltip_header_hide_focus ^ "\"></th>");
  List.iter
    (fun (id,i,n) ->
      Buffer.add_string buf
	(if id = focus_id
	 then "<th class=\"header highlighted\">"
	 else "<th id=\"" ^ focus_key_of_id id ^ "\" class=\"header\" title=\"" ^ Lisql2nl.config_lang#grammar#tooltip_header_set_focus ^ "\">");
      Buffer.add_string buf
	(html_of_nl_xml state
	   (Lisql2nl.xml_ng_id ~isolated:true
	      Lisql2nl.config_lang#grammar
	      ~id_labelling:(state#id_labelling)
	      id));
      Buffer.add_string buf (html_freq ~unit:`Entities ~partial n);
      Buffer.add_string buf "</th>")
    id_i_n_list;
  Buffer.add_string buf "</tr>";
  let rank = ref first_rank in
  List.iter
    (fun binding ->
      Buffer.add_string buf "<tr>";
      Buffer.add_string buf "<td>";
      Buffer.add_string buf (string_of_int !rank);
      Buffer.add_string buf "</td>";
      List.iter
	(fun (id,i,n) ->
	  Buffer.add_string buf "<td>";
	  ( match binding.(i) with
	    | None -> ()
	    | Some t -> Buffer.add_string buf (html_cell state ~view:Table ~rank:(!rank) ~column:id t) );
	  Buffer.add_string buf "</td>")
	id_i_n_list;
      Buffer.add_string buf "</tr>";
      incr rank)
    results.bindings;
  Buffer.add_string buf "</table></div>";
  Buffer.contents buf


let html_slides state slides =
  let id_labelling = state#id_labelling in
  let buf = Buffer.create 1000 in
  let rank = ref 0 in
  List.iter
    (fun slide_data ->
     incr rank;
     let uri, fields = Lis.(slide_data.media_uri, slide_data.binding_fields) in
     Buffer.add_string buf "<div class=\"item";
     if !rank = 1 then Buffer.add_string buf " active";
     Buffer.add_string buf "\">";
     let slide_media =
       if Rdf.uri_is_image uri then
	 let label = Lexicon.name_of_uri uri in
	 html_img ~alt:label ~title:label uri
       else if Rdf.uri_is_video uri then
	 html_video uri
       else "Unsupported media" in
     Buffer.add_string buf slide_media;
     Buffer.add_string buf ("<div class=\"table-responsive\"><table class=\"table table-bordered table-condensed table-hover\">");
     List.iter
       (fun (var, term_opt) ->
	let id = id_labelling#get_var_id var in
	Buffer.add_string buf "<tr>";
	Buffer.add_string buf "<td>";
	Buffer.add_string
	  buf
	  (html_of_nl_xml
	     state
	     (Lisql2nl.xml_ng_id ~isolated:true
				 Lisql2nl.config_lang#grammar
				 ~id_labelling
				 id));
	Buffer.add_string buf "</td>";
	Buffer.add_string buf "<td>";
	( match term_opt with
	  | None -> ()
	  | Some t -> Buffer.add_string buf (html_cell state ~view:Slideshow ~rank:!rank ~column:id t) );
	Buffer.add_string buf "</td>";
	Buffer.add_string buf "</tr>")
       fields;
     Buffer.add_string buf "</table></div>";
     Buffer.add_string buf "</div>")
    slides;
  Buffer.contents buf
