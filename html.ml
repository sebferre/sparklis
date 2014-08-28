
open Js
open Jsutils
open Lisql

(* generic dictionary with automatic generation of keys *)

class ['a] dico (prefix : string) =
object
  val mutable cpt = 0
  val ht : (string,'a) Hashtbl.t = Hashtbl.create 100

  method add (x : 'a) : string =
    let k = cpt <- cpt + 1; prefix ^ string_of_int cpt in
    Hashtbl.add ht k x;
    k

  method add_key (key : string) (x : 'a) : unit =
    Hashtbl.add ht key x

  method get (key : string) : 'a =
    try Hashtbl.find ht key
    with _ ->
      Firebug.console##log(string ("Missing element in dico: " ^ key));
      failwith "Osparqlis.dico#get"
end

(* HTML state with dictionaries for foci and increments in user interface *)

let focus_key_of_root = "root"
let focus_key_of_id (id : Lisql.id) : string = "id" ^ string_of_int id

class state (lex : Lisql2nl.lexicon) =
object
  method lexicon = lex
  val dico_foci : Lisql.focus dico = new dico "focus"
  method add_focus (focus : Lisql.focus) : string =
    if Lisql.is_root_focus focus then dico_foci#add_key focus_key_of_root focus;
    ( match Lisql.id_of_focus focus with
      | Some id -> dico_foci#add_key (focus_key_of_id id) focus
      | None -> () );
    dico_foci#add focus
  method get_focus (key : string) : Lisql.focus = dico_foci#get key

  val dico_incrs : Lisql.increment dico = new dico "incr"
  method dico_incrs = dico_incrs

  val dico_results : (int * Lisql.id * Rdf.term) dico = new dico "cell"
  method dico_results = dico_results
end

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

let html_img ?id ?classe ~height ~alt ~title url =
  "<img" ^
    (match id with None -> "" | Some i -> " id=\"" ^ i ^ "\"") ^
    (match classe with None -> "" | Some c -> " class=\"" ^ c ^ "\"") ^
    " src=\"" ^ url ^ "\" height=\"" ^ string_of_int height ^ "\" alt=\"" ^ alt ^ "\" title=\"" ^ title ^ "\">"

let html_open_new_window ~height uri =
  html_a uri (html_img ~classe:"open-new-window" ~height ~alt:"Open" ~title:"Open resource in new window" "icon-open-new-window.png")

let html_delete ?id ~title () =
  html_img ?id ~height:16 ~alt:"Delete" ~title "icon-delete.png"

let html_literal s = html_span ~classe:"Literal" (escapeHTML s)
let html_uri ~classe uri s = html_span ~classe ~title:uri (escapeHTML s)
let html_modifier m = html_span ~classe:"modifier" (escapeHTML m)

let html_word = function
  | `Thing -> "thing"
  | `Relation -> html_modifier "relation"
  | `Literal s -> html_literal s
  | `TypedLiteral (s,t) -> html_literal s ^ " (" ^ escapeHTML t ^ ")"
  | `Blank id -> html_span ~classe:"nodeID" (escapeHTML id) ^ " (bnode)"
  | `Id (id,s) -> html_span ~classe:"lisqlID" ~title:("#" ^ string_of_int id) (escapeHTML s)
  | `Entity (uri,s) -> html_uri ~classe:"URI" uri s ^ " " ^ html_open_new_window ~height:12 uri
  | `Class (uri,s) -> html_uri ~classe:"classURI" uri s
  | `Prop (uri,s) -> html_uri ~classe:"propURI" uri s
  | `Op op -> html_modifier op
  | `DummyFocus -> html_span ~classe:"highlighted" "___"

let rec html_of_nl_xml ?(highlight=false) (state : state) (xml : Lisql2nl.xml) : string =
  let open Lisql2nl in
  match xml with
    | Focus (foc1, xml1) :: Focus (foc2, xml2) :: xml when foc1 = foc2 -> html_of_nl_xml ~highlight state (Focus (foc1, xml1 @ xml2) :: xml)
    | Highlight xml1 :: Highlight xml2 :: xml -> html_of_nl_xml ~highlight state (Highlight (xml1 @ xml2) :: xml)
    | node :: xml -> html_of_nl_node ~highlight state node ^ " " ^ html_of_nl_xml ~highlight state xml
    | [] -> ""
and html_of_nl_node ?(highlight=false) (state : state) : Lisql2nl.node -> string = 
  let open Lisql2nl in
  function
    | Kwd s -> s
    | Word w -> html_word w
    | Enum (sep,lxml) -> String.concat sep (List.map (html_of_nl_xml ~highlight state) lxml)
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
      html_delete ~id:"delete-current-focus" ~title:"Click on this red cross to delete the current focus" ()
    | DeleteIncr ->
      html_delete ~title:"Remove this query element at the query focus" ()
and html_highlight h xml =
  if h
  then html_span ~classe:"highlighted" xml
  else xml

(* HTML of focus *)

let html_focus (state : state) (focus : focus) : string = 
  html_of_nl_xml state
    (Lisql2nl.xml_s
       (Lisql2nl.map_s Lisql2nl.main_transf
	  (Lisql2nl.s_of_focus state#lexicon focus)))


(* HTML of increment lists *)

let html_count_unit count max unit units =
  if count = 0 then "No " ^ unit
  else if count = 1 then "1 " ^ unit
  else if count >= max then string_of_int count ^ "+ " ^ units
  else string_of_int count ^ " " ^ units

let html_increment_frequency focus (state : state) (incr,freq) =
  let key = state#dico_incrs#add incr in
  let text =
    html_of_nl_xml state
      (Lisql2nl.xml_incr state#lexicon focus incr) in
  let title_opt =
    match incr with
      | IncrTerm _ -> None
      | IncrId _ -> None
      | IncrType _ -> None
      | IncrRel _ -> None
      | IncrTriple _ -> None
      | IncrTriplify -> Some "Adds a focus on the property to refine it"
      | IncrIs -> None
      | IncrAnd -> None
      | IncrOr -> Some "Insert an alternative to the current focus"
      | IncrMaybe -> Some "Make the current focus optional"
      | IncrNot -> Some "Apply negation to the current focus"
      | IncrUnselect -> Some "Hide the focus column in the table of results"
      | IncrAggreg _ -> Some "Aggregate the focus column in the table of results, for each solution on other columns"
      | IncrOrder Highest -> Some "Sort the focus column in decreasing order"
      | IncrOrder Lowest -> Some "Sort the focus column in increasing order"
      | IncrOrder _ -> None in
  let text_freq =
    if freq = 1
    then ""
    else " [" ^ string_of_int freq ^ "]" in
  html_span ~id:key ~classe:"increment" ?title:title_opt (text ^ text_freq)

(* TODO: avoid to pass focus as argument, use NL generation on increments *)
let html_index focus (state : state) (index : Lisql.increment Lis.index) =
  let buf = Buffer.create 1000 in
  Buffer.add_string buf "<ul>";
  List.iter
    (fun incr_freq ->
      Buffer.add_string buf "<li>";
      Buffer.add_string buf (html_increment_frequency focus state incr_freq);
      Buffer.add_string buf "</li>")
    index;
  Buffer.add_string buf "</ul>";
  Buffer.contents buf

(* HTML of results *)

let html_cell_img ?(height = 120) url =
  let label = Lisql2nl.name_of_uri url in
  html_img ~height ~alt:label ~title:label url ^ html_open_new_window ~height:16 url

let html_cell_video url mime =
  "<video width=\"320\" height=\"240\" controls>\
  <source src=\"" ^ url ^ "\" type=\"" ^ mime ^ "\">\
  Your browser does not support the video tag.\
  </video>" ^
    html_open_new_window ~height:16 url

let html_cell_audio url mime =
  "<audio controls>\
  <source src=\"" ^ url ^ "\" type=\"" ^ mime ^ "\">\
  Your browser does not support this audio format.\
  </audio>" ^ 
    html_open_new_window ~height:16 url

let html_cell state ~(line : int) ~(column : Lisql.id) t =
  let contents =
    match t with
      | Rdf.URI uri ->
	if Rdf.uri_has_ext uri ["jpg"; "JPG"; "jpeg"; "JPEG"; "png"; "PNG"; "gif"; "GIF"] then
	  html_cell_img uri
	else if Rdf.uri_has_ext uri ["mp4"; "MP4"] then
	  html_cell_video uri "video/mp4"
	else if Rdf.uri_has_ext uri ["ogg"; "OGG"] then
	  html_cell_video uri "video/ogg"
	else if Rdf.uri_has_ext uri ["mp3"; "MP3"] then
	  html_cell_audio uri "audio/mpeg"
	else html_word (Lisql2nl.word_of_term t)
      | _ -> html_word (Lisql2nl.word_of_term t) in
  let key = state#dico_results#add (line,column,t) in
  html_span ~id:key ~classe:"cell" contents

let html_table_of_results (state : state) ~first_rank ~focus_var results =
  let open Sparql_endpoint in
  let focus_id = match focus_var with None -> -1 | Some v -> state#lexicon#get_var_id v in
  let id_i_list = List.map (fun (var,i) -> (state#lexicon#get_var_id var, i)) results.vars in
  let buf = Buffer.create 1000 in
  Buffer.add_string buf ("<table id=\"extension\"><tr><th id=\"" ^ focus_key_of_root ^ "\" class=\"header\" title=\"Click on this column header to hide the focus\"></th>");
  List.iter
    (fun (id,i) ->
      Buffer.add_string buf
	(if id = focus_id
	 then "<th class=\"header highlighted\">"
	 else "<th id=\"" ^ focus_key_of_id id ^ "\" class=\"header\" title=\"Click on this column header to set the focus on it\">");
      Buffer.add_string buf (escapeHTML (state#lexicon#get_id_label id));
      Buffer.add_string buf "</th>")
    id_i_list;
  Buffer.add_string buf "</tr>";
  let rank = ref first_rank in
  List.iter
    (fun binding ->
      Buffer.add_string buf "<tr>";
      Buffer.add_string buf "<td>";
      Buffer.add_string buf (string_of_int !rank);
      Buffer.add_string buf "</td>";
      List.iter
	(fun (id,i) ->
	  Buffer.add_string buf "<td>";
	  ( match binding.(i) with
	    | None -> ()
	    | Some t -> Buffer.add_string buf (html_cell state ~line:(!rank) ~column:id t) );
	  Buffer.add_string buf "</td>")
	id_i_list;
      Buffer.add_string buf "</tr>";
      incr rank)
    results.bindings;
  Buffer.add_string buf "</table>";
  Buffer.contents buf
