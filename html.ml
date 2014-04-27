
open Js
open Jsutils
open Lisql

(* pretty-printing of terms, NL in HTML *)

let name_of_uri uri =
  let uri = to_string (decodeURI (string uri)) in
  let s =
    match Regexp.search (Regexp.regexp "[^/#]+$") uri 0 with
      | Some (_,res) ->
	( match Regexp.matched_string res with "" -> uri | name -> name )
      | None -> uri in
  escapeHTML s

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

let html_suspended ~suspended html =
  if suspended
  then html_span ~classe:"suspended" html
  else html

let html_a url html =
  "<a target=\"_blank\" href=\"" ^ url ^ "\">" ^ html ^ "</a>"

let html_literal s = html_span ~classe:"Literal" (escapeHTML s)
let html_uri uri = html_span ~classe:"URI" ~title:uri (name_of_uri uri)
let html_class c = html_span ~classe:"classURI" ~title:c (name_of_uri c)
let html_prop p = html_span ~classe:"propURI" ~title:p (name_of_uri p)
let html_modifier m = html_span ~classe:"modifier" m

let rec html_term ?(link = false) = function
  | Rdf.URI uri ->
    (*if uri_is_image uri (* too heavy loading *)
    then
      if link
      then html_a uri (html_img uri)
      else html_img ~height:60 uri
    else*)
      if link
      then html_a uri (name_of_uri uri)
      else html_uri uri
  | Rdf.Number (f,s,dt) -> html_term ~link (Rdf.TypedLiteral (s,dt))
  | Rdf.TypedLiteral (s,dt) -> html_literal s ^ " (" ^ name_of_uri dt ^ ")"
  | Rdf.PlainLiteral (s,lang) -> html_literal s ^ (if lang="" then "" else " (" ^ lang ^ ")")
  | Rdf.Bnode id -> "_:" ^ id
  | Rdf.Var v -> "?" ^ v

let html_and ar_html =
  let html = ref ("<ul class=\"list-and\"><li>" ^ ar_html.(0) ^ "</li>") in
  for i=1 to Array.length ar_html - 1 do
    html := !html ^ " <li>and " ^ ar_html.(i) ^ "</li>"
  done;
  !html ^ "</ul>"
let html_or ?(suspended=None) ar_html =
  let susp_or = suspended <> None in
  let susp_elt i = suspended <> None && suspended <> Some i in
  let html = ref ("<ul class=\"list-or\"><li>" ^ html_suspended ~suspended:(susp_elt 0) ar_html.(0) ^ "</li>") in
  for i=1 to Array.length ar_html - 1 do
    html :=
      !html ^
      " <li>" ^ html_suspended ~suspended:susp_or (html_modifier "or") ^ " " ^
      html_suspended ~suspended:(susp_elt i) ar_html.(i) ^ "</li>"
  done;
  !html ^ "</ul>"
let html_maybe ?(suspended=false) html = html_suspended ~suspended (html_modifier "optionally") ^ " " ^ html
let html_not ?(suspended=false) html = html_suspended ~suspended (html_modifier "not") ^ " " ^ html
let html_return np = "Give me " ^ np
let html_dummy_focus = "<span class=\"in-current-focus\">___</span>"
let html_ellipsis = "..."

let html_current_focus html =
  html_span ~id:"current-focus" ~classe:"in-current-focus"
      (html ^ " <img src=\"icon-delete.png\" height=\"16\" alt=\"Delete\" id=\"delete-current-focus\" title=\"Click on this red cross to delete the current focus\">")

let html_word = function
  | `Thing -> "thing"
  | `Term t -> html_term t
  | `Class c -> html_class c
  | `Prop p -> html_prop p
  | `Literal l -> html_literal l
  | `Op op -> html_modifier op
  | `DummyFocus -> html_dummy_focus

let html_nl_focus dico (foc : nl_focus) (html : string) : string =
  match foc with
    | `NoFocus -> html
    | `Focus (focus, pos) ->
      let id = dico#add focus in
      let class_pos =
	match pos with
	  | `In -> "in-current-focus"
	  | `At -> "in-current-focus"
	  | `Out -> "out-current-focus"
	  | `Ex -> "ex-current-focus" in
      let html = "<span id=\"" ^ id ^ "\" class=\"focus " ^ class_pos ^ "\">" ^ html ^ "</span>" in
      if pos = `At
      then html_current_focus html
      else html

let rec html_s dico (foc, nl : nl_s) : string =
  let html =
    match nl with
      | `Return np -> html_return (html_np dico np) in
  html_nl_focus dico foc html			  
and html_np dico (foc, nl : nl_np) : string =
  let html =
    match nl with
      | `PN (w, rel) -> html_word w ^ html_rel_opt dico rel
      | `Qu (qu, adj, `Thing, (foc2, `That (_, `IsNP (_, `Qu ((`A | `The), `Nil, w, rel2))))) ->
	html_qu qu ^ html_adj adj ^ html_nl_focus dico foc2 (html_word w ^ html_rel_opt dico rel2)
      | `Qu (`A, `Nil, `Thing, rel) -> "something" ^ html_rel_opt dico rel
      | `Qu (qu, adj, w, rel) -> html_qu qu ^ html_adj adj ^ html_word w ^ html_rel_opt dico rel
      | `QuOneOf (_, [w]) -> html_word w
      | `QuOneOf (qu, lw) -> html_qu qu ^ "of " ^ String.concat ", " (List.map html_word lw)
      | `And ar -> html_and (Array.map (html_np dico) ar)
      | `Or (susp, ar) -> html_or ~suspended:susp (Array.map (html_np dico) ar)
      | `Maybe (suspended, np) -> html_maybe ~suspended (html_np dico np)
      | `Not (suspended, np) -> html_not ~suspended (html_np dico np) in
  html_nl_focus dico foc html
and html_qu : nl_qu -> string = function
  | `A -> "a "
  | `Any susp -> html_suspended ~suspended:susp (html_modifier "any ")
  | `The -> "the "
  | `All -> "all "
  | `One -> "one "
and html_adj : nl_adj -> string = function
  | `Nil -> ""
  | `Order w -> html_word w ^ " "
  | `Aggreg (susp, a, w) -> html_suspended ~suspended:susp (html_adj a ^ html_word w) ^ " "
  | `Adj (a, w) -> html_adj a ^ html_word w ^ " "
and html_rel_opt dico foc_nl =
  if foc_nl = top_rel
  then ""
  else " " ^ html_rel dico foc_nl
and html_rel dico (foc, nl : nl_rel) : string =
  match nl with (* transformations *)
    | `That (_, `And ar) -> html_rel dico (foc, `And (Array.map (fun (foc_i,nl_i) -> (foc_i, `That (`NoFocus, nl_i))) ar))
    | `That (_, `Or (susp,ar)) -> html_rel dico (foc, `Or (susp, Array.map (fun (foc_i,nl_i) -> (foc_i, `That (`NoFocus, nl_i))) ar))
    | _ ->
      let html =
	match nl with
	  | `Nil -> ""
	  | `That (_, `IsThere) -> html_ellipsis
	  | `That (_, `HasProp (p, (foc2, `Qu (`A, `Nil, `Thing, (foc3, `That (_,nl_vp)))))) ->
	    "whose " ^ html_nl_focus dico foc2 (html_word p ^ " " ^ html_vp dico (foc3,nl_vp))
	  | `That (_, `IsPP pp) -> html_pp dico pp
	  | `That vp -> "that " ^ html_vp dico vp
	  | `Of np -> "of " ^ html_np dico np
	  | `Ing (w, np) -> html_word w ^ " " ^ html_np dico np
	  | `And ar -> html_and (Array.map (html_rel dico) ar)
	  | `Or (susp, ar) -> html_or ~suspended:susp (Array.map (html_rel dico) ar) in
      html_nl_focus dico foc html
and html_vp dico (foc, nl : nl_vp) : string =
  let html =
    match nl with
      | `IsThere -> html_ellipsis
      | `IsNP np -> "is " ^ html_np dico np
      | `IsPP pp -> "is " ^ html_pp dico pp
      | `HasProp (w, (foc2, `Qu (qu, adj, `Thing, rel))) -> html_vp dico (foc, `Has (foc2, `Qu (qu, adj, w, rel)))
      | `HasProp (p, np) -> "has " ^ html_word p ^ " " ^ html_np dico np
      | `Has np -> "has " ^ html_np dico np
      | `VT (w, np) -> html_word w ^ " " ^ html_np dico np
      | `And ar -> html_and (Array.map (html_vp dico) ar)
      | `Or (susp, ar) -> html_or ~suspended:susp (Array.map (html_vp dico) ar)
      | `Maybe (suspended, vp) -> html_maybe ~suspended (html_vp dico vp)
      | `Not (suspended, vp) -> html_not ~suspended (html_vp dico vp)
      | `DummyFocus -> html_dummy_focus in
  html_nl_focus dico foc html
and html_pp dico : nl_pp -> string = function
  | `Prep (prep,w) -> html_word prep ^ " " ^ html_word w
  | `PrepBin (prep1,w1,prep2,w2) -> html_word prep1 ^ " " ^ html_word w1 ^ " " ^ html_word prep2 ^ " " ^ html_word w2

let html_focus dico focus = html_s dico (s_of_focus focus)


(* HTML of increment lists *)

let html_count_unit count max unit units =
  if count = 0 then "No " ^ unit
  else if count = 1 then "1 " ^ unit
  else if count >= max then string_of_int count ^ "+ " ^ units
  else string_of_int count ^ " " ^ units

let html_increment_frequency focus dico_incrs (incr,freq) =
  let key = dico_incrs#add incr in
  let text =
    match incr with
      | IncrTerm t -> html_term t
      | IncrClass c ->
	( match focus with
	  | AtS1 (Det (Term _, _), _) -> "a " ^ html_class c
	  | AtS1 (Det (An (_, Thing), _), _) -> "a " ^ html_class c
	  | AtS1 (Det (An (_, Class c0), _), _) when c0 = c ->
	    (*"<del>a " ^ html_class c ^ "</del>"*)
	    "a " ^ html_class c ^ " <img src=\"icon-delete.png\" height=\"16\" alt=\"Delete\" title=\"Remove this class at the head of the focus\">"
	  | AtS1 _ -> "that is a " ^ html_class c
	  | AtP1 (IsThere, _) -> "that is a " ^ html_class c
	  | _ -> "and that is a " ^ html_class c )
      | IncrProp p ->
	let prefix =
	  match focus with
	    | AtS1 _ -> "that has a "
	    | AtP1 (IsThere, _) -> "that has a "
	    | _ -> "and that has a " in
	prefix ^ html_prop p
      | IncrInvProp p ->
	let prefix =
	  match focus with
	    | AtS1 _ -> "that is the "
	    | AtP1 (IsThere, _) -> "that is the "
	    | _ -> "and that is the " in
	prefix ^ html_prop p ^ " of"
      | IncrAnd -> "and " ^ html_ellipsis
      | IncrOr -> html_modifier "or " ^ html_ellipsis (*html_or [|html_dummy_focus; html_ellipsis|]*)
      | IncrMaybe -> html_maybe html_dummy_focus
      | IncrNot -> html_not html_dummy_focus
      | IncrUnselect -> html_np dico_incrs#dico_foci (head_of_modif `NoFocus `DummyFocus top_rel (Unselect,Unordered))
      | IncrAggreg g -> html_np dico_incrs#dico_foci (head_of_modif `NoFocus `DummyFocus top_rel (Aggreg (g,Unordered),Unordered))
      | IncrOrder order -> html_np dico_incrs#dico_foci (head_of_modif `NoFocus `DummyFocus top_rel (Select,order))
  in
  let text_freq =
    if freq = 1
    then ""
    else " [" ^ string_of_int freq ^ "]" in
  "<span class=\"increment\" id=\"" ^ key ^ "\">" ^ text ^ text_freq ^ "</span>"

(* TODO: avoid to pass focus as argument, use NL generation on increments *)
let html_index focus dico_incrs (index : Lisql.increment Lis.index) =
  let buf = Buffer.create 1000 in
  Buffer.add_string buf "<ul>";
  List.iter
    (fun incr_freq ->
      Buffer.add_string buf "<li>";
      Buffer.add_string buf (html_increment_frequency focus dico_incrs incr_freq);
      Buffer.add_string buf "</li>")
    index;
  Buffer.add_string buf "</ul>";
  Buffer.contents buf

(* HTML of results *)

let html_img ?(height = 120) url =
  "<img src=\"" ^ url ^ "\" alt=\"" ^ name_of_uri url ^ "\" height=\"" ^ string_of_int height ^ "\">"

let html_video url mime =
  "<video width=\"320\" height=\"240\" controls>\
  <source src=\"" ^ url ^ "\" type=\"" ^ mime ^ "\">\
  Your browser does not support the video tag.\
  </video>"

let html_audio url mime =
  "<audio controls>\
  <source src=\"" ^ url ^ "\" type=\"" ^ mime ^ "\">\
  Your browser does not support this audio format.\
  </audio>"

let html_cell t =
  match t with
    | Rdf.URI uri ->
      if Rdf.uri_has_ext uri ["jpg"; "JPG"; "jpeg"; "JPEG"; "png"; "PNG"; "gif"; "GIF"] then
	html_a uri (html_img uri)
      else if Rdf.uri_has_ext uri ["mp4"; "MP4"] then
	html_video uri "video/mp4"
      else if Rdf.uri_has_ext uri ["ogg"; "OGG"] then
	html_video uri "video/ogg"
      else if Rdf.uri_has_ext uri ["mp3"; "MP3"] then
	html_audio uri "audio/mpeg"
      else html_term ~link:true t
    | _ -> html_term ~link:true t

let html_table_of_results ~first_rank ~focus_var results =
  let open Sparql_endpoint in
  let buf = Buffer.create 1000 in
  Buffer.add_string buf "<table id=\"extension\"><tr><th></th>";
  List.iter
    (fun (var,i) ->
      Buffer.add_string buf
	(if var = focus_var
	 then "<th class=\"in-current-focus\">"
	 else "<th>");
      Buffer.add_string buf var;
      Buffer.add_string buf "</th>")
    results.vars;
  Buffer.add_string buf "</tr>";
  let li = List.map snd results.vars in
  let rank = ref first_rank in
  List.iter
    (fun binding ->
      Buffer.add_string buf "<tr>";
      Buffer.add_string buf "<td>";
      Buffer.add_string buf (string_of_int !rank);
      Buffer.add_string buf "</td>";
      List.iter
	(fun i ->
	  Buffer.add_string buf "<td>";
	  ( match binding.(i) with
	    | None -> ()
	    | Some t -> Buffer.add_string buf (html_cell t) );
	  Buffer.add_string buf "</td>")
	li;
      Buffer.add_string buf "</tr>";
      incr rank)
    results.bindings;
  Buffer.add_string buf "</table>";
  Buffer.contents buf
