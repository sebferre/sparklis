
type term = string
type expr = string
type pattern = string
type selector = string
type query = string

let split_uri (uri : Rdf.uri) : (string * string) option (* namespace, local name *) =
  match Regexp.search (Regexp.regexp "[A-Za-z0-9_]+$") uri 0 with
    | Some (i,res) ->
      let localname = Regexp.matched_string res in
      let len_namespace = String.length uri - String.length localname in
      if len_namespace > 0 && (uri.[len_namespace - 1] = '/' || uri.[len_namespace - 1] = '#')
      then Some (String.sub uri 0 len_namespace, localname)
      else None
    | None -> None

let prologue =
object (self)
  val mutable cpt = 0 (* prefix counter *)
  val mutable map : (string * string) list = [] (* mapping from namespace to prefix *)
  initializer self#reset

  method reset : unit =
    cpt <- 0;
    map <- (* default namespaces (reverse order of declarations) *)
      [("http://purl.org/dc/terms/", "dcterms:");
       ("http://purl.org/dc/elements/1.1/", "dc:");
       ("http://dbpedia.org/property/", "dbp:");
       ("http://dbpedia.org/ontology/", "dbo:");
       ("http://dbpedia.org/resource/", "dbr:");
       ("http://dbpedia.org/class/yago/", "yago:");
       ("http://xmlns.com/foaf/0.1/", "foaf:");
       ("http://rdfs.org/ns/void#", "void:");
       ("http://www.w3.org/2004/02/skos/core#", "skos:");
       ("http://www.w3.org/2002/07/owl#", "owl:"); 
       ("http://www.w3.org/2000/01/rdf-schema#", "rdfs:");
       ("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:");
       ("http://www.w3.org/2001/XMLSchema#", "xsd:")]

  method qname_of_uri (uri : Rdf.uri) : string option (* prefix, local name *) =
    match split_uri uri with
      | None -> None
      | Some (ns,ln) ->
	let prefix =
	  try List.assoc ns map
	  with _ ->
	    cpt <- cpt+1;
	    let prefix = "n" ^ string_of_int cpt ^ ":" in
	    map <- (ns,prefix)::map;
	    prefix in
	Some (prefix ^ ln)

  method add_declarations_to_query (query : string) : string =
    let buf = Buffer.create 1000 in
    List.fold_right (* iter in reverse order *)
      (fun (ns,pre) () ->
	if Regexp.search (Regexp.regexp_string pre) query 0 <> None
	then begin
	  Buffer.add_string buf "PREFIX ";
	  Buffer.add_string buf pre;
	  Buffer.add_string buf " <";
	  Buffer.add_string buf ns;
	  Buffer.add_string buf ">\n"
	end)
      map ();
    Buffer.add_string buf query;
    Buffer.contents buf

end

let uri (uri : Rdf.uri) : term =
  match prologue#qname_of_uri uri with
    | None -> "<" ^ uri ^ ">"
    | Some qname -> qname

let bnode (name : string) : term = if name="" then "[]" else "_:" ^ name
    
let var (v : Rdf.var) : term = "?" ^ v

let string (s : string) : term =
  if String.contains s '\n' || String.contains s '"'
  then "\"\"\"" ^ s ^ "\"\"\""
  else "\"" ^ s ^ "\""

let rec term : Rdf.term -> term = function
  | Rdf.URI u -> uri u
  | Rdf.Number (f,s,dt) -> if dt="" then term (Rdf.PlainLiteral (s,"")) else term (Rdf.TypedLiteral (s,dt))
  | Rdf.TypedLiteral (s,dt) -> string s ^ "^^" ^ uri dt
  | Rdf.PlainLiteral (s,lang) -> string s ^ (if lang = "" then "" else "@" ^ lang)
  | Rdf.Bnode name -> bnode name
  | Rdf.Var v -> var v

let conv_numeric (t : term) : expr = "xsd:double(" ^ t ^ ")"

let indent : int -> string -> string =
  let re = Regexp.regexp_string "\n" in
  fun w p -> Regexp.global_replace re p ("\n" ^ String.make w ' ')

let expr_func (f : string) (l_expr : expr list) : expr = f ^ "(" ^ String.concat "," l_expr ^ ")"
let expr_infix (op : string) (l_expr : expr list) : expr = "(" ^ String.concat op l_expr ^ ")"
let expr_regex (expr : expr) (pat : string) : expr = "REGEX(" ^ expr ^ ", \"" ^ pat ^ "\", 'i')"
let expr_comp (relop : string) (expr1 : expr) (expr2 : expr) : expr = expr1 ^ " " ^ relop ^ " " ^ expr2

type aggreg =
| DistinctCOUNT | DistinctCONCAT | SAMPLE | ID
| SUM of string option | AVG of string option | MAX of string option | MIN of string option

let expr_aggreg (g : aggreg) (expr1 : expr) : expr =
  let make_aggreg prefix_g expr suffix_g = prefix_g ^ expr ^ suffix_g in
  let make_conv conv_opt expr = match conv_opt with None -> expr | Some conv -> conv ^ "(" ^ expr ^ ")" in
  match g with
  | DistinctCOUNT -> make_aggreg "COUNT(DISTINCT " expr1 ")"
  | DistinctCONCAT -> make_aggreg "GROUP_CONCAT(DISTINCT " expr1 " ; separator=', ')"
  | SUM conv_opt -> make_aggreg "SUM(" (make_conv conv_opt expr1) ")"
  | AVG conv_opt -> make_aggreg "AVG(" (make_conv conv_opt expr1) ")"
  | MAX conv_opt -> make_aggreg "MAX(" (make_conv conv_opt expr1) ")"
  | MIN conv_opt -> make_aggreg "MIN(" (make_conv conv_opt expr1) ")"
  | SAMPLE -> make_aggreg "SAMPLE(" expr1 ")"
  | ID -> make_aggreg "" expr1 ""


let log_true : expr = "true"
let log_false : expr = "false"
let log_not (e : expr) : expr =
  if e = log_true then log_false
  else if e = log_false then log_true
  else "!( " ^ indent 3 e ^ " )"
let log_and (le : expr list) : expr = 
  if List.mem log_false le then log_false
  else
    let le = List.filter ((<>) log_true) le in
    match le with
      | [] -> log_true
      | [e] -> e
      | _ -> "(  " ^ String.concat "\n&& " (List.map (indent 3) le) ^ " )"
let log_or (le : expr list) : expr =
  if List.mem log_true le then log_true
  else
    let le = List.filter ((<>) log_false) le in
    match le with
      | [] -> log_false
      | [e] -> e
      | _ -> "(  " ^ String.concat "\n|| " (List.map (indent 3) le) ^ " )"

let empty : pattern = ""
let something (s : term) : pattern = s ^ " a [] ."
let rdf_type (s : term) (c : term) : pattern = s ^ " a " ^ c ^ " ."
let triple (s : term) (p : term) (o : term) : pattern = s ^ " " ^ p ^ " " ^ o ^ " ."
let bind (e : expr) (v : Rdf.var) : pattern = "BIND (" ^ e ^ " AS " ^ var v ^ ")"
let filter (e : expr) : pattern =
  if e = log_true then empty
  else "FILTER ( " ^ indent 9 e ^ " )"
let join (lp : pattern list) : pattern =
  String.concat "\n" (List.filter ((<>) empty) lp)
let union (lp : pattern list) : pattern =
  if List.mem empty lp then invalid_arg "Sparql.union: empty pattern";
  match lp with
    | [] -> invalid_arg "Sparql.union: empty list"
    | [p] -> p
    | p::lp1 -> "{ " ^ indent 2 p ^ " }\nUNION " ^ String.concat "\nUNION " (List.map (fun p -> "{ " ^ indent 8 p ^ " }") lp1)
let optional (p : pattern) : pattern =
  if p = empty then invalid_arg "Sparql.optional: empty pattern";
  "OPTIONAL { " ^ indent 11 p ^ " }"
let not_exists (p : pattern) : expr = "NOT EXISTS { " ^ indent 13 p ^ " }"

let subquery (q : query) : pattern = "{ " ^ indent 2 q ^ " }"

let search_label (t : term) (l : term) : pattern =
  t ^ " rdfs:label " ^ l ^ " ." (* ^ sparql_constr l (HasLang "en") *)
let search_contains (l : term) (w : string) : pattern =
  l ^ " bif:contains " ^ string w ^ " ."


let ask (pattern : pattern) : query =
  "ASK\nWHERE { " ^ indent 8 pattern ^ " }"

type order = ASC | DESC

type projection_def = [`Bare | `Expr of expr | `Aggreg of aggreg * expr]
type projection = projection_def * Rdf.var

let projection_def : projection_def -> expr = function
  | `Bare -> ""
  | `Expr e -> e
  | `Aggreg (g,e) -> expr_aggreg g e

let projection (def,v : projection) : selector =
  match def with
  | `Bare -> (var v)
  | _ ->
    let s_def = projection_def def in
    let s_var = var v in
    if s_def = s_var
    then s_var
    else "(" ^ s_def ^ " AS " ^ s_var ^ ")"

let select
    ?(distinct=false)
    ~(projections : projection list)
    ?(groupings : Rdf.var list = [])
    ?(having : expr = log_true)
    ?(ordering : (order * Rdf.var) list = [])
    ?(limit : int option)
    (pattern : pattern) : query =
  if projections = []
  then ask pattern
  else
    let sel = String.concat " " (List.map projection projections) in
    let s = "SELECT " ^ (if distinct then "DISTINCT " else "") ^ sel ^ "\nWHERE { " ^ indent 8 pattern ^ " }" in
    let s =
      if groupings = []
      then s
      else s ^ "\nGROUP BY " ^ String.concat " " (List.map var groupings) in
    let s =
      if having = log_true
      then s
      else s ^ "\nHAVING ( " ^ indent 9 having ^ " )" in
    let s =
      if ordering = []
      then s
      else s ^ "\nORDER BY " ^ String.concat " "
	(List.map
	   (function
	     | (ASC,v) -> "ASC(" ^ var v ^ ")"
	     | (DESC,v) -> "DESC(" ^ var v ^ ")")
	   ordering) in
    let s = match limit with None -> s | Some n -> s ^ "\nLIMIT " ^ string_of_int n in
    s

let select_from_service url query =
  "SELECT * FROM { SERVICE <" ^ url ^ "> { " ^ query ^ " }}"

type subquery =
  { projections : projection list;
    pattern : pattern;
    groupings : Rdf.var list;
    having : expr;
    limit : int option }
    
let subquery_having (sq : subquery) (e : expr) : subquery =
  { sq with having = log_and [sq.having; e] }

let query_of_subquery : subquery -> query = function
  | { projections; pattern; groupings; having; limit} ->
    select ~distinct:true ~projections ~groupings ~having ?limit pattern

let pattern_of_subquery (sq : subquery) : pattern =
  if sq.having = log_true
  then subquery (query_of_subquery sq)
  else join [subquery (query_of_subquery {sq with having=log_true}); (* because HAVING not allowed in subqueries *)
	     filter sq.having]


(* formulas *)
      
type formula =
  | Pattern of pattern (* binding *)
  | Subquery of subquery (* sub-queries *)
  | Filter of expr (* non-binding *)
  | True (* empty binding *)
  | False (* no binding *)
  | Or of pattern * expr (* mixed unions *)

let rec formula_and (f1 : formula) (f2 : formula) : formula =
  match f1, f2 with
    | False, _
    | _, False -> False
    | True, _ -> f2
    | _, True -> f1
(*
    | Subquery sq1, Filter e2 -> Subquery (subquery_having sq1 e2) (* kind of unsafe *)
    | Filter e1, Subquery sq2 -> Subquery (subquery_having sq2 e1) (* kind of unsafe *)
*)
    | Subquery sq1, _ -> formula_and (Pattern (pattern_of_subquery sq1)) f2
    | _, Subquery sq2 -> formula_and f1 (Pattern (pattern_of_subquery sq2))
    | Pattern p1, Pattern p2 -> Pattern (join [p1;p2])
    | Pattern p1, Filter e2 -> Pattern (join [p1; filter e2])
    | Filter e1, Pattern p2 -> Pattern (join [p2; filter e1])
    | Filter e1, Filter e2 -> Filter (log_and [e1;e2])
    | Pattern p1, Or (p2,e2) -> Pattern (union [join [p1;p2]; join [p1; filter e2]])
    | Filter e1, Or (p2,e2) -> Or (join [p2; filter e1], log_and [e1; e2])
    | Or (p1,e1), Pattern p2 -> Pattern (union [join [p1;p2]; join [p2; filter e1]])
    | Or (p1,e1), Filter e2 -> Or (join [p1; filter e2], log_and [e1; e2])
    | Or (p1,e1), Or (p2,e2) -> Or (union [join [p1; p2]; join [p1; filter e2]; join [p2; filter e1]], log_and [e1;e2])

let formula_and_list (lf : formula list) : formula =
  List.fold_left formula_and True lf

let formula_or_list (lf : formula list) : formula =
  let lp, le, btrue =
    List.fold_right
      (fun f (lp,le,btrue) ->
	match f with
	  | Pattern p -> (p::lp,le,btrue)
	  | Subquery sq -> (pattern_of_subquery sq::lp,le,btrue)
	  | Filter e -> (lp,e::le,btrue)
	  | True -> (lp,le,true)
	  | False -> (lp,le,btrue)
	  | Or (p,e) -> (p::lp,e::le,btrue))
      lf ([],[],false) in
  match lp, le, btrue with
    | [], [], false -> False
    | [], _, true -> True
    | _::_, [], false -> Pattern (union lp)
    | [], _::_, false -> Filter (log_or le)
    | _::_, _, true -> Or (union lp, log_true)
    | _::_, _::_, false -> Or (union lp, log_or le)


let formula_optional : formula -> formula = function
  | Pattern p -> Pattern (optional p)
  | Subquery sq -> Pattern (optional (pattern_of_subquery sq))
  | Filter e -> True
  | True -> True
  | False -> True
  | Or (p,_) -> Or (p, log_true)

let formula_not : formula -> formula = function
  | Pattern p -> Filter (not_exists p)
  | Subquery sq -> Filter (not_exists (pattern_of_subquery sq))
  | Filter e -> Filter (log_not e)
  | True -> False
  | False -> True
  | Or (p,e) -> Filter (log_and [not_exists p; log_not e])

let formula_bind (x : term) : formula -> formula = function
  | Pattern p -> Pattern p
  | Subquery sq -> Subquery sq
  | Filter e -> Pattern (join [something x; filter e])
  | True -> True (*Pattern (something x)*)
  | False -> False
  | Or (p,e) -> Pattern (union [p; join [something x; filter e]])

let expr_of_formula : formula -> expr = function
  | Filter e -> e
  | _ -> log_true (* TODO: dummy default *)

let pattern_of_formula : formula -> pattern = function
  | Pattern p -> p
  | Subquery sq -> pattern_of_subquery sq
  | Filter e -> filter e (* tentative *)
  | True -> empty
  | False -> filter log_false (* tentative *)
  | Or (p,e) -> union [p; filter e] (* tentative *)

(* views *)

type view = Rdf.var list * (?limit:int -> unit -> formula)

let view_defs view = fst view
  
let empty_view : view = ([], (fun ?limit () -> True))

let join_views (views : view list) : view =
  let list_defs, list_form = List.split views in
  Common.list_to_set (List.concat list_defs),
  (fun ?limit () ->
    formula_and_list
      (List.map (fun f -> f ?limit ()) list_form))
  
let query_of_view ?distinct ?ordering ?limit (lv, f : view) : query =
  match f ?limit () with
  | Subquery sq ->
    select
      ?distinct
      ~projections:sq.projections (*List.filter (fun (_,v) -> List.mem v lv) sq.projections*)
      ~groupings:sq.groupings
      ~having:sq.having
      ?ordering
      ?limit
      sq.pattern
  | form ->
    select
      ?distinct
      ~projections:(List.map (fun v -> (`Bare,v)) lv)
      ?ordering
      ?limit
      (pattern_of_formula form)

