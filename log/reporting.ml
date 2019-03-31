
(* utilities *)

let split_fragment str =
  try
    let i = String.rindex str '#' in
    String.sub str 0 i, String.sub str (i+1) (String.length str - (i+1))
  with _ -> str, ""

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

let re_timestamp = Str.regexp "\\([0-9][0-9][0-9][0-9]\\)-\\([0-9][0-9]\\)-\\([0-9][0-9]\\)T\\([0-9][0-9]\\):\\([0-9][0-9]\\):\\([0-9][0-9]\\)"

let seconds_of_timestamp dt =
  if Str.string_match re_timestamp dt 0 then
    ( match List.map (fun i -> int_of_string (Str.matched_group i dt)) [1;2;3;4;5;6] with
    | [year; mon; mday; hour; min; sec] ->
      let open Unix in
      let tm = { tm_year = year - 1900; tm_mon = mon-1; tm_mday = mday; tm_hour = hour; tm_min = min; tm_sec = sec; tm_wday = 0; tm_yday = 0; tm_isdst = false } in
      int_of_float (fst (mktime tm))
    | _ -> assert false )
  else failwith "seconds_of_timestamp: bad timestamp format"
  
let timestamp_diff dt1 dt2 =
  let s1 = seconds_of_timestamp dt1 in
  let s2 = seconds_of_timestamp dt2 in
  s1 - s2
    
(* hitlog *)

let get_ns =
  let ht = Hashtbl.create 13 in
  print_endline "Reading table mapping IPs to namespaces";
  iter_lines
    (fun line ->
      match split_line ~bound:2 line with
	| [ip; ns] -> Hashtbl.replace ht ip ns
	| _ -> ())
    "data/table_ip_namespace.txt";
  fun ip ->
    try Hashtbl.find ht ip
    with Not_found ->
      let ns =
	match cmd_to_list ("dig -x " ^ ip ^ " +short") with
	| [] -> "unknown"
	| x::_ -> x in
      Hashtbl.add ht ip ns;
      ignore (Sys.command (Printf.sprintf "echo \"%s,%s\" >> data/table_ip_namespace.txt" ip ns));
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

let sum f l = List.fold_left (fun res x -> res + f x) 0 l
let sum_array f ar = Array.fold_left (fun res x -> res + f x) 0 ar
  
let rec size_s = function
  | Return (_,np) -> size_s1 np
  | SAggreg (_,dims,aggregs) -> sum size_dim dims + sum size_aggreg aggregs
  | SExpr (_,name,id,modif,expr,rel_opt) -> 1 + size_modif_s2 modif + size_expr expr + size_p1_opt rel_opt
  | SFilter (_,id,expr) -> 1 + size_expr expr
  | Seq (_,l) -> sum size_s l
and size_dim = function
  | ForEachResult _ -> 1
  | ForEach (_,id,modif,rel_opt,id2) -> 1 + size_modif_s2 modif + size_p1_opt rel_opt + 1
  | ForTerm (_,t,id2) -> 1 + 1
and size_aggreg = function
  | TheAggreg (_,id,modif,g,rel_opt,id2) -> 1 + size_modif_s2 modif + 1 + size_p1_opt rel_opt + 1
and size_expr = function
  | Undef _ -> 1
  | Const (_,t) -> 1
  | Var (_,id) -> 1
  | Apply (_,func,le) -> 1 + sum size_expr le
and size_s1 = function
  | Det (_,det,rel_opt) -> size_s2 det + size_p1_opt rel_opt
  | AnAggreg (_,idg,mg,g,relg_opt,np) -> 1 + size_modif_s2 mg + size_p1_opt relg_opt + size_s1 np
  | NAnd (_,l) -> sum (fun np -> 1 + size_s1 np) l - 1
  | NOr (_,l) -> sum (fun np -> 1 + size_s1 np) l - 1
  | NMaybe (_,np) -> 1 + size_s1 np
  | NNot (_,np) -> 1 + size_s1 np
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
  | Is (_,np) -> 1 + size_s1 np
  | Type (_,uri) -> 1
  | Rel (_,uri,_,np) -> 1 + size_s1 np
  | Triple (_,_,np1,np2) -> 1 + size_s1 np1 + size_s1 np2
  | Search _ -> 1
  | Filter _ -> 1
  | And (_,l) -> sum size_p1 l
  | Or (_,l) -> sum (fun vp -> 1 + size_p1 vp) l - 1
  | Maybe (_,vp) -> 1 + size_p1 vp
  | Not (_,vp) -> 1 + size_p1 vp
  | IsThere _ -> 0

type query_feature = [ `Term | `The | `Class | `ThatIs | `ThatIsA | `ThatHas | `ThatIsOf | `ThatHasARelation | `Filter | `And | `Or | `Maybe | `Not
		     | `ForEachResult | `ForEach | `ForTerm | `Aggreg of aggreg | `ExprName | `Undef | `Const | `Var | `Func of func | `Any | `Order ]

let string_of_feature : query_feature -> string = function
  | `Term -> "RDF term"
  | `The -> "anaphora"
  | `Class -> "class"
  | `ThatIs -> "copula"
  | `ThatIsA -> "typing"
  | `ThatHas -> "forward relation"
  | `ThatIsOf -> "backward relation"
  | `ThatHasARelation -> "undefinite relation"
  | `Filter -> "filter"
  | `And -> "conjunction"
  | `Or -> "disjunction"
  | `Maybe -> "optional"
  | `Not -> "negation"
  | `ForEachResult -> "for each result"
  | `ForEach -> "for each"
  | `ForTerm -> "for some term"
  | `Aggreg g -> "aggregation"
  | `ExprName -> "expression name"
  | `Undef -> "undefined"
  | `Const -> "constant"
  | `Var -> "variable"
  | `Func f -> "function"
  | `Any -> "hidden column"
  | `Order -> "ordering"

let collect f l = List.concat (List.map f l)
    
let rec features_s : 'a elt_s -> query_feature list = function
  | Return (_,np) -> features_s1 np
  | SAggreg (_,dims,aggregs) -> collect features_dim dims @ collect features_aggreg aggregs
  | SExpr (_,name,id,modif,expr,rel_opt) -> (if name="" then [] else [`ExprName]) @ features_modif_s2 modif @ features_expr expr @ features_p1_opt rel_opt
  | SFilter (_,id,expr) -> features_expr expr
  | Seq (_,l) -> collect features_s l
and features_dim = function
  | ForEachResult _ -> [`ForEachResult]
  | ForEach (_,id,modif,rel_opt,id2) -> `ForEach :: features_modif_s2 modif @ features_p1_opt rel_opt
  | ForTerm (_,t,id2) -> `ForTerm :: []
and features_aggreg = function
  | TheAggreg (_,id,modif,g,rel_opt,id2) -> `Aggreg g :: features_modif_s2 modif @ features_p1_opt rel_opt
and features_expr = function
  | Undef _ -> [`Undef]
  | Const _ -> [`Const]
  | Var _ -> [`Var]
  | Apply (_,func,le) -> `Func func :: collect features_expr le
and features_s1 = function
  | Det (_,det, rel_opt) -> features_s2 det @ features_p1_opt rel_opt
  | AnAggreg (_,idg,mg,g,relg_opt,np) -> `Aggreg g :: features_modif_s2 mg @ features_p1_opt relg_opt @ features_s1 np
  | NAnd (_,l) -> `And :: collect features_s1 l
  | NOr (_,l) -> `Or :: collect features_s1 l
  | NMaybe (_,np) -> `Maybe :: features_s1 np
  | NNot (_,np) -> `Not :: features_s1 np
and features_s2 = function
  | Term t -> [`Term]
  | An (id,m,head) -> features_modif_s2 m @ features_head head
  | The id -> [`The]
and features_head = function
  | Thing -> []
  | Class uri -> [`Class]
and features_modif_s2 (project,order) = features_project project @ features_order order
and features_project = function
  | Unselect -> [`Any]
  | Select -> []
and features_order = function
  | Unordered -> []
  | _ -> [`Order]
and features_p1_opt = function
  | None -> []
  | Some vp -> features_p1 vp
and features_p1 = function
  | Is (_,np) -> `ThatIs :: features_s1 np
  | Type (_,uri) -> `ThatIsA :: []
  | Rel (_,uri,Fwd,np) -> `ThatHas :: features_s1 np
  | Rel (_,uri,Bwd,np) -> `ThatIsOf :: features_s1 np
  | Triple (_,_,np1,np2) -> `ThatHasARelation :: features_s1 np1 @ features_s1 np2
  | Search _ -> [`Filter]
  | Filter _ -> [`Filter]
  | And (_,l) -> collect features_p1 l
  | Or (_,l) -> `Or :: collect features_p1 l
  | Maybe (_,vp) -> `Maybe :: features_p1 vp
  | Not (_,vp) -> `Not :: features_p1 vp
  | IsThere _ -> []

let rec undup_features = function
  | [] -> []
  | x::l ->
    if List.mem x l
    then undup_features l
    else x :: undup_features l

let rec print_s = function
  | Return (_,np) -> "give me " ^ print_s1 np
  | SAggreg (_,dims,aggregs) -> "give me " ^ String.concat ", " (List.map print_dim dims) ^ ", " ^ String.concat " and " (List.map print_the_aggreg aggregs)
  | SExpr (_,name,id,modif,expr,rel_opt) -> "give me " ^ (if name="" then "" else name ^ " = ") ^ print_id id ^ " " ^ print_expr expr ^ print_p1_opt rel_opt
  | SFilter (_,id,expr) -> "where " ^ print_id id ^ " " ^ print_expr expr
  | Seq (_,l) -> print_and (List.map print_s l)
and print_dim = function
  | ForEachResult _ -> "for each result"
  | ForEach (_,id,modif,rel_opt,id2) -> "for each " ^ print_modif_s2 modif ^ print_id id2 ^ print_p1_opt rel_opt ^ " as " ^ print_id id
  | ForTerm (_,t,id2) -> "for " ^ print_id id2 ^ " = " ^ print_term t
and print_the_aggreg = function
  | TheAggreg (_,id,modif,g,rel_opt,id2) -> "the " ^ print_modif_s2 modif ^ print_aggreg g ^ " " ^ print_id id ^ print_p1_opt rel_opt ^ " of " ^ print_id id2
and print_expr = function
  | Undef _ -> "_"
  | Const (_,t) -> print_term t
  | Var (_,id) -> print_id id
  | Apply (_,func,le) -> print_func func ^ "(" ^ String.concat ", " (List.map print_expr le) ^ ")"
and print_s1 = function
  | Det (_,det,rel_opt) -> print_s2 det ^ print_p1_opt rel_opt
  | AnAggreg (_,idg,mg,g,relg_opt,np) -> "a " ^ print_modif_s2 mg ^ print_aggreg g ^ " " ^ print_id idg ^ print_p1_opt relg_opt ^ " [" ^ print_s1 np ^ "]"
  | NAnd (_,l) -> print_and (List.map print_s1 l)
  | NOr (_,l) -> print_or (List.map print_s1 l)
  | NMaybe (_,np) -> print_maybe (print_s1 np)
  | NNot (_,np) -> print_not (print_s1 np)
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
  | Highest _ -> "highest "
  | Lowest _ -> "lowest "
and print_aggreg = function
  | NumberOf -> "number"
  | ListOf -> "list"
  | Sample -> "sample"
  | Total _ -> "sum"
  | Average _ -> "average"
  | Maximum _ -> "maximum"
  | Minimum _ -> "minimum"
and print_func f =
  try List.assoc f Permalink.list_func_atom with _ -> "unknown_func"
and print_p1_opt = function
  | None -> ""
  | Some vp -> " that " ^ print_p1 vp
and print_p1 = function
  | Is (_,np) -> "is " ^ print_s1 np
  | Type (_,uri) -> "is a " ^ print_uri uri
  | Rel (_,uri,Fwd,np) -> "has " ^ print_uri uri ^ " " ^ print_s1 np
  | Rel (_,uri,Bwd,np) -> "is the " ^ print_uri uri ^ " of " ^ print_s1 np
  | Triple (_,S,npp,npo) -> "has relation " ^ print_s1 npp ^ " to " ^ print_s1 npo
  | Triple (_,O,nps,npp) -> "has relation " ^ print_s1 npp ^ " from " ^ print_s1 nps
  | Triple (_,P,nps,npo) -> "is a relation from " ^ print_s1 nps ^ " to " ^ print_s1 npo
  | Search (_,constr) -> print_constr constr
  | Filter (_,constr) -> print_constr constr
  | And (_,l) -> print_and (List.map print_p1 l)
  | Or (_,l) -> print_or (List.map print_p1 l)
  | Maybe (_,vp) -> print_maybe (print_p1 vp)
  | Not (_,vp) -> print_not (print_p1 vp)
  | IsThere _ -> "..."
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
and print_and l = "(" ^ String.concat " and " l ^ ")"
and print_or l = "(" ^ String.concat " or " l ^ ")"
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

let escape_string s =
  let s = Str.global_replace (Str.regexp "\\\\") "" s in
  let s = Str.global_replace (Str.regexp "\"") "\\\"" s in
  let s = Str.global_replace (Str.regexp "[\n\r]") "\t" s in
  s

let rec output_object_list out_ttl pr = function
  | [] -> failwith "output_object_list: empty list"
  | [x] -> pr x
  | x::l -> pr x; output_string out_ttl ", "; output_object_list out_ttl pr l

let process_querylog () =
  let out_txt = open_out "data/querylog_processed.txt" in
  let out_ttl = open_out "data/querylog_processed.ttl" in
  let out_dat = open_out "data/querylog_processed.dat" in (* sessions as time series *)
  let current_session = ref ("<ip>","<session>","<endpoint>") in
  let current_session_on = ref false in
  let current_session_start = ref 0 in
  let current_session_last_elapsed = ref 0 in
  let current_session_max_size_query = ref 0 in
  let nb_sessions = ref 0 in
  let nb_step = ref 0 in
  print_endline "Processing data/querylog.txt > result in data/querylog_processed.txt/.ttl";
  ignore (Sys.command "sort -k2,1 -t , < data/querylog.txt > data/querylog_grouped.txt");
  output_string out_txt "# session\ttimestamp\tendpoint\tquery\n";
  output_string out_ttl "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n";
  output_string out_ttl "@prefix : <http://example.com/> .\n";
  iter_lines
    (fun line ->
      print_string "."; flush stdout;
      ( match split_line ~bound:4 line with
      | dt::ip_session::endpoint::query::_ ->
	(try
	   let seconds = seconds_of_timestamp dt in
	  (*let days = (seconds - seconds_of_timestamp "2014-10-29T00:00:00") / 60 / 60 / 24 in*)
	  let ip, session = split_fragment ip_session in
	  let ast_query = Permalink.to_query query in
	  let s_query = print_s ast_query in
	  let size_query = size_s ast_query in
	  let features_query = undup_features (features_s ast_query) in
	  let ns_ip = get_ns ip in
	  begin
	  (*let public_endpoint =
	      try let _ = Str.search_forward (Str.regexp "\\(dbpedia\\|bio2rdf\\)") endpoint 0 in true
	      with _ -> false in
	    if public_endpoint then*)
	      begin output_string out_txt (if session = "" then Digest.to_hex (Digest.string ip) else session); output_string out_txt "\t";
		output_string out_txt dt; output_string out_txt "\t";
		output_string out_txt ns_ip; output_string out_txt "\t";
		output_string out_txt endpoint; output_string out_txt "\t";
		output_string out_txt s_query; output_string out_txt "\n"
	      end
	  end;
	  begin
	    incr nb_step;
	    output_string out_ttl (":step" ^ string_of_int !nb_step ^ " a :Step ; ");
	    output_string out_ttl ":timestamp \""; output_string out_ttl dt; output_string out_ttl "\"^^xsd:dateTime ; ";
	    output_string out_ttl ":date \""; output_string out_ttl (try String.sub dt 0 10 with _ -> ""); output_string out_ttl "\"^^xsd:date ; ";
	    output_string out_ttl ":userIP \""; output_string out_ttl ip; output_string out_ttl "\" ; ";
	    if ns_ip <> "unknown" then begin output_string out_ttl ":user \""; output_string out_ttl ns_ip; output_string out_ttl "\" ; " end;
	    if session <> "" then begin output_string out_ttl ":sessionID \""; output_string out_ttl session; output_string out_ttl "\" ; " end;
	    output_string out_ttl ":endpoint \""; output_string out_ttl (escape_string endpoint); output_string out_ttl "\" ; ";
	    output_string out_ttl ":query \""; output_string out_ttl (escape_string s_query); output_string out_ttl "\" ; ";
	    if features_query <> [] then
	      begin
		output_string out_ttl ":queryFeature ";
		output_object_list out_ttl
		  (fun x -> output_string out_ttl ("\"" ^ x ^ "\""))
		  (List.map string_of_feature features_query);
		output_string out_ttl " ; "
	      end;
	    output_string out_ttl ":querySize "; output_string out_ttl (string_of_int size_query); output_string out_ttl " .\n"
	  end;
	  begin
	    if (ip,session,endpoint) <> !current_session || size_query = 0 then
	      begin
		current_session := (ip,session,endpoint);
		current_session_on := (size_query = 0 (* && session <> ""*) (* && ns_ip = "nat-vpn.it.teithe.gr." *));
		current_session_start := seconds;
		current_session_last_elapsed := 0;
		current_session_max_size_query := 0
	      end;
	    let elapsed_time = seconds - !current_session_start in
	    let elapsed_time =
	      let delta = elapsed_time - !current_session_last_elapsed in
	      if delta > 60 then
		begin (* compress lazy time *)
		  current_session_start := seconds - 60 - !current_session_last_elapsed;
		  !current_session_last_elapsed + 60
		end
		(*begin (* start a new timeseries *)
		  current_session_on := (size_query = 0);
		  current_session_start := dt;
		  if !current_session_on then output_string out_dat "\n";
		  0
		  end*)
	      else elapsed_time in
	    if size_query / (elapsed_time+1) >= 1 then current_session_on := false; (* use of permalink *)
	    if !current_session_on then
	      begin
		if !current_session_last_elapsed = 0 && elapsed_time <> 0 then (* first step after 0 *)
		  begin
		    incr nb_sessions;
		    output_string out_dat ("\n# " ^ String.concat "\t" [dt; session; ns_ip; ip; endpoint] ^ "\n"); (* as comment *)
		    output_string out_dat ("0\t0\t" ^ "1" (*string_of_int days*) ^ "\t\"Give me a thing\"\n") (* step 0 *)
		  end;
		let is_max_size_query = size_query > !current_session_max_size_query in
		if elapsed_time <> 0 (* && is_max_query_size *) then (* for any step except 0 *)
		  begin
		    output_string out_dat (string_of_int elapsed_time ^ "\t" ^ string_of_int size_query ^ "\t" ^ (if is_max_size_query then "0" else "1") (*string_of_int days*) ^ "\t\"" ^ s_query ^ "\"\n")
		  end;
	      end;
	    current_session_last_elapsed := elapsed_time;
	    current_session_max_size_query := max !current_session_max_size_query size_query
	  end
	 with _ -> output_string out_txt ("*** wrong format *** : " ^ line ^ "\n"))
      | _ -> output_string out_txt ("*** wrong format *** : " ^ line ^ "\n")))
    "data/querylog_grouped.txt";
  print_string (string_of_int !nb_sessions ^ " sessions");
  print_newline ();
  close_out out_txt;
  close_out out_ttl;
  (*  ignore (Sys.command ("java -jar /local/ferre/soft/rdf2rdf.jar data/querylog_processed.ttl data/querylog_processed.rdf"));;*)
  ignore (Sys.command ("rapper -i turtle data/querylog_processed.ttl -o rdfxml > data/querylog_processed.rdf"));;
  
let _ =
  process_hitlog ();
  process_querylog ();;
