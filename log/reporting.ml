
(* utilities *)

let re_comma = Str.regexp ",";;

let split_line ?bound line =
  match bound with
    | None -> Str.split re_comma line
    | Some n -> Str.bounded_split re_comma line n;;

let iter_lines f file =
  let ch = open_in file in
  try while true do
      f (input_line ch)
    done with _ -> ();;

let process_output_to_list2 command =
  let chan = Unix.open_process_in command in
  let res = ref ([] : string list) in
  let rec process_otl_aux () =  
    let e = input_line chan in
    res := e::!res;
    process_otl_aux () in
  try process_otl_aux ()
  with End_of_file ->
    let stat = Unix.close_process_in chan in
    (List.rev !res, stat);;

let cmd_to_list command =
  let (l,_) = process_output_to_list2 command in
  l;;

(* hitlog *)

let get_ns =
  let ht = Hashtbl.create 13 in
  fun ip ->
    try Hashtbl.find ht ip
    with Not_found ->
      let ns =
	match cmd_to_list ("dig -x " ^ ip ^ " +short") with
	  | [] -> "unknown"
	  | x::_ -> x in
      Hashtbl.add ht ip ns;
      ns;;

let process_hitlog () =
  let out = open_out "data/hitlog_processed.txt" in
  print_endline "Processing data/hitlog.txt > result in data/hitlog_processed.txt";
  iter_lines
    (fun line ->
      print_string "."; flush stdout;
      ( match split_line line with
	| dt::ip::_ -> output_string out dt; output_string out "  "; output_string out (get_ns ip)
	| _ -> output_string out "*** wrong format ***");
      output_string out "\n")
    "data/hitlog.txt";
  print_newline ();
  close_out out;;

(* querylog *)

open Lisql

let rec size_s = function
  | Return np -> size_s1 np
and size_s1 = function
  | Det (det, rel_opt) -> size_s2 det + size_p1_opt rel_opt
  | AnAggreg (idg,mg,g,relg_opt,np) -> 1 + size_modif_s2 mg + size_p1_opt relg_opt + size_s1 np
  | NAnd ar -> Array.fold_left (fun res np -> res + 1 + size_s1 np) (-1) ar
  | NOr ar -> Array.fold_left (fun res np -> res + 1 + size_s1 np) (-1) ar
  | NMaybe np -> 1 + size_s1 np
  | NNot np -> 1 + size_s1 np
and size_s2 = function
  | Term t -> 1
  | An (id,m,head) -> size_modif_s2 m + size_head head
  | The id -> 1
and size_head = function
  | Thing -> 0
  | Class uri -> 1
and size_modif_s2 (project,order) = size_project project + size_order order
and size_project = function
  | Unselect -> 1
  | Select -> 0
and size_order = function
  | Unordered -> 0
  | _ -> 1
and size_p1_opt = function
  | None -> 0
  | Some vp -> size_p1 vp
and size_p1 = function
  | Is np -> 1 + size_s1 np
  | Type uri -> 1
  | Rel (uri,_,np) -> 1 + size_s1 np
  | Triple (_,np1,np2) -> 1 + size_s1 np1 + size_s1 np2
  | Search _ -> 1
  | Filter _ -> 1
  | And ar -> Array.fold_left (fun res vp -> res + size_p1 vp) 0 ar
  | Or ar -> Array.fold_left (fun res vp -> res + 1 + size_p1 vp) (-1) ar
  | Maybe vp -> 1 + size_p1 vp
  | Not vp -> 1 + size_p1 vp
  | IsThere -> 0


let rec print_s = function
  | Return np -> "Give me " ^ print_s1 np
and print_s1 = function
  | Det (det, rel_opt) -> print_s2 det ^ print_p1_opt rel_opt
  | AnAggreg (idg,mg,g,relg_opt,np) -> "a " ^ print_modif_s2 mg ^ print_aggreg g ^ " " ^ print_id idg ^ print_p1_opt relg_opt ^ " [" ^ print_s1 np ^ "]"
  | NAnd ar -> print_and (Array.map print_s1 ar)
  | NOr ar -> print_or (Array.map print_s1 ar)
  | NMaybe np -> print_maybe (print_s1 np)
  | NNot np -> print_not (print_s1 np)
and print_s2 = function
  | Term t -> print_term t
  | An (id,m,head) -> "a " ^ print_modif_s2 m ^ print_head head ^ " " ^ print_id id
  | The id -> print_id id
and print_head = function
  | Thing -> "thing"
  | Class uri -> print_uri uri
and print_id id = "#" ^ string_of_int id
and print_modif_s2 (project,order) = print_project project ^ print_order order
and print_project = function
  | Unselect -> "hidden "
  | Select -> ""
and print_order = function
  | Unordered -> ""
  | Highest -> "highest "
  | Lowest -> "lowest "
and print_aggreg = function
  | NumberOf -> "number of"
  | ListOf -> "list of"
  | Total -> "total"
  | Average -> "average"
  | Maximum -> "maximum"
  | Minimum -> "minimum"
and print_p1_opt = function
  | None -> ""
  | Some vp -> " that " ^ print_p1 vp
and print_p1 = function
  | Is np -> "is " ^ print_s1 np
  | Type uri -> "is a " ^ print_uri uri
  | Rel (uri,Fwd,np) -> "has " ^ print_uri uri ^ " " ^ print_s1 np
  | Rel (uri,Bwd,np) -> "is the " ^ print_uri uri ^ " of " ^ print_s1 np
  | Triple (S,npp,npo) -> "has relation " ^ print_s1 npp ^ " to " ^ print_s1 npo
  | Triple (O,nps,npp) -> "has relation " ^ print_s1 npp ^ " from " ^ print_s1 nps
  | Triple (P,nps,npo) -> "is a relation from " ^ print_s1 nps ^ " to " ^ print_s1 npo
  | Search constr -> print_constr constr
  | Filter constr -> print_constr constr
  | And ar -> print_and (Array.map print_p1 ar)
  | Or ar -> print_or (Array.map print_p1 ar)
  | Maybe vp -> print_maybe (print_p1 vp)
  | Not vp -> print_not (print_p1 vp)
  | IsThere -> "..."
and print_constr = function
  | True -> "is true"
  | MatchesAll lw -> "matches all of " ^ String.concat ", " lw
  | MatchesAny lw -> "matches any of " ^ String.concat ", " lw
  | After w -> "is after " ^ w
  | Before w -> "is before " ^ w
  | FromTo (w1,w2) -> "is from " ^ w1 ^ " to " ^ w2
  | HigherThan w1 -> "is higher than " ^ w1
  | LowerThan w2 -> "is lower than " ^ w2
  | Between (w1,w2) -> "is between " ^ w1 ^ " and " ^ w2
  | HasLang w -> "has language " ^ w
  | HasDatatype w -> "has datatype " ^ w
and print_and ar = "(" ^ String.concat " and " (Array.to_list ar) ^ ")"
and print_or ar = "(" ^ String.concat " or " (Array.to_list ar) ^ ")"
and print_maybe s = "maybe " ^ s
and print_not s = "not " ^ s
and print_term = function
  | Rdf.URI uri -> print_uri uri
  | Rdf.Number (_,s,dt) -> s ^ " (" ^ dt ^ ")"
  | Rdf.TypedLiteral (s,uri) -> s ^ "(" ^ print_uri uri ^ ")"
  | Rdf.PlainLiteral (s,lang) -> s ^ " (" ^ lang ^ ")"
  | Rdf.Bnode id -> "_:" ^ id
  | Rdf.Var v -> "?" ^ v
and print_uri uri =
  try
    let _pos = Str.search_forward (Str.regexp "[^/#]+$") uri 0 in
    match Str.matched_string uri with "" -> uri | name -> name
  with _ -> uri

let process_querylog () =
  let out_txt = open_out "data/querylog_processed.txt" in
  let out_ttl = open_out "data/querylog_processed.ttl" in
  print_endline "Processing data/querylog.txt > result in data/querylog_processed.txt/.ttl";
  output_string out_ttl "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n";
  output_string out_ttl "@prefix : <http://example.com/> .\n";
  iter_lines
    (fun line ->
      print_string "."; flush stdout;
      ( match split_line ~bound:4 line with
	| dt::ip::endpoint::query::_ ->
	  let ast_query = Permalink.to_query query in
	  let s_query = print_s ast_query in
	  let size_query = size_s ast_query in
	  let ns_ip = get_ns ip in
	  begin
	    output_string out_txt dt; output_string out_txt "  ";
	    output_string out_txt ns_ip; output_string out_txt "\t";
	    output_string out_txt endpoint; output_string out_txt "\t";
	    output_string out_txt s_query; output_string out_txt "\n"
	  end;
	  begin
	    output_string out_ttl "[] a :Step ; ";
	    output_string out_ttl ":timestamp \""; output_string out_ttl dt; output_string out_ttl "\"^^xsd:dateTime ; ";
	    output_string out_ttl ":date \""; output_string out_ttl (try String.sub dt 0 10 with _ -> ""); output_string out_ttl "\"^^xsd:date ; ";
	    output_string out_ttl ":userIP \""; output_string out_ttl ns_ip; output_string out_ttl "\" ; ";
	    output_string out_ttl ":endpoint \""; output_string out_ttl endpoint; output_string out_ttl "\" ; ";
	    output_string out_ttl ":query \""; output_string out_ttl s_query; output_string out_ttl "\" ; ";
	    output_string out_ttl ":querySize "; output_string out_ttl (string_of_int size_query); output_string out_ttl " .\n"
	  end
	| _ -> output_string out_txt "*** wrong format ***"))
    "data/querylog.txt";
  print_newline ();
  close_out out_txt;
  close_out out_ttl;
  ignore (Sys.command ("java -jar /local/ferre/soft/rdf2rdf.jar " ^ "data/querylog_processed.ttl" ^ " " ^ "data/querylog_processed.rdf"));;

let _ =
  process_hitlog ();
  process_querylog ();;
