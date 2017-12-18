(*
  Copyright 2013-2017 Sébastien Ferré, IRISA, Université de Rennes 1

  This file is part of Sparklis.
*)

module S : (* private use of strings to represent SPARQL strings *)
sig
  type +'a sparql = private string
  val sparql : string -> 'a sparql
  val (^^) : 'a sparql -> 'b sparql -> 'c sparql
  val (^<) : string -> 'a sparql -> 'b sparql
  val (^>) : 'a sparql -> string -> 'b sparql
  val concat : string -> 'a sparql list -> 'b sparql
  val indent : int -> 'a sparql -> 'a sparql
end =
struct
  type +'a sparql = string
  let sparql s = s
  let (^^) s1 s2 = s1 ^ s2
  let (^<) s1 s2 = s1 ^ s2
  let (^>) s1 s2 = s1 ^ s2
  let concat sep ls = String.concat sep ls
  let indent =
    let re = Regexp.regexp_string "\n" in
    fun w paragraph -> (Regexp.global_replace re : string -> string -> string) paragraph ("\n" ^ String.make w ' ')
end

include S

type var = [`Var] sparql
type term = [`Var|`Term] sparql
type expr = [`Var|`Term|`Expr] sparql
type pred = [`Var|`Term|`Path] sparql
type pattern = [`Pattern] sparql
type selector = [`Var|`Selector] sparql
type ordering = [`Ordering] sparql
type query = [`Query] sparql

type converter = expr -> expr

let split_uri (uri : Rdf.uri) : (string * string) option (* namespace, local name *) =
  try match Regexp.search (Regexp.regexp "[A-Za-z0-9_]+$") uri 0 with
    | Some (i,res) ->
      let localname = Regexp.matched_string res in
      let len_namespace = String.length uri - String.length localname in
      if len_namespace > 0 && (uri.[len_namespace - 1] = '/' || uri.[len_namespace - 1] = '#')
      then Some (String.sub uri 0 len_namespace, localname)
      else None
    | None -> None
  with _ -> Jsutils.firebug "Sparql.split_uri failed"; None

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
    | None -> sparql ("<" ^ uri ^ ">")
    | Some qname -> sparql qname

let qname (qn : string) : term = sparql qn

let bnode (name : string) : term = sparql (if name="" then "[]" else "_:" ^ name)
    
let var (v : Rdf.var) : var = sparql ("?" ^ v)

let string (s : string) : term =
  if String.contains s '\n' || String.contains s '"'
  then sparql ("\"\"\"" ^ s ^ "\"\"\"")
  else sparql ("\"" ^ s ^ "\"")

let rec term : Rdf.term -> term = function
  | Rdf.URI u -> uri u
  | Rdf.Number (f,s,dt) -> if dt="" then term (Rdf.PlainLiteral (s,"")) else term (Rdf.TypedLiteral (s,dt))
  | Rdf.TypedLiteral (s,dt) -> string s ^^ sparql "^^" ^^ uri dt
  | Rdf.PlainLiteral (s,lang) -> string s ^^ sparql (if lang = "" then "" else "@" ^ lang)
  | Rdf.Bnode name -> bnode name
  | Rdf.Var v -> (var v :> term)

    
type aggreg =
| DistinctCOUNT | DistinctCONCAT | SAMPLE | ID
| SUM of converter | AVG of converter | MAX of converter | MIN of converter

let term_aggreg (g : aggreg) (term : term) : term = (* assuming aggregates are terms (not expr) to simplify compilation of HAVING clauses *)
  let make_aggreg prefix_g expr suffix_g : term = prefix_g ^< expr ^> suffix_g in
  match g with
  | DistinctCOUNT -> make_aggreg "COUNT(DISTINCT " term ")"
  | DistinctCONCAT -> make_aggreg "GROUP_CONCAT(DISTINCT " term " ; separator='  /  ')"
  | SUM conv -> make_aggreg "SUM(" (conv (term :> expr)) ")"
  | AVG conv -> make_aggreg "AVG(" (conv (term :> expr)) ")"
  | MAX conv -> make_aggreg "MAX(" (conv (term :> expr)) ")"
  | MIN conv -> make_aggreg "MIN(" (conv (term :> expr)) ")"
  | SAMPLE -> make_aggreg "SAMPLE(" term ")"
  | ID -> make_aggreg "" term ""

let expr_func (f : string) (l_expr : expr list) : expr = f ^< "(" ^< concat "," l_expr ^> ")"
let expr_infix (op : string) (l_expr : expr list) : expr = "(" ^< concat (" " ^ op ^ " ") l_expr ^> ")"
let expr_regex (expr : expr) (pat : string) : expr = "REGEX(" ^< expr ^> ", \"" ^ pat ^ "\", 'i')"
let expr_comp (relop : string) (expr1 : expr) (expr2 : expr) : expr = expr1 ^^ (" " ^ relop ^ " ") ^< expr2

let conv_numeric (e : expr) : expr = expr_func "xsd:double" [e]

let log_true : expr = sparql "true"
let log_false : expr = sparql "false"
let log_not (e : expr) : expr =
  if e = log_true then log_false
  else if e = log_false then log_true
  else "!( " ^< indent 3 e ^> " )"
let log_and (le : expr list) : expr = 
  if List.mem log_false le then log_false
  else
    let le = List.filter ((<>) log_true) (Common.list_to_set le) in
    match le with
      | [] -> log_true
      | [e] -> e
      | _ -> "(  " ^< concat "\n&& " (List.map (indent 3) le) ^> " )"
let log_or (le : expr list) : expr =
  if List.mem log_true le then log_true
  else
    let le = List.filter ((<>) log_false) (Common.list_to_set le) in
    match le with
      | [] -> log_false
      | [e] -> e
      | _ -> "(  " ^< concat "\n|| " (List.map (indent 3) le) ^> " )"

let path_seq (p1 : pred) (p2 : pred) : pred = p1 ^^ "/" ^< p2
let path_alt (p1 : pred) (p2 : pred) : pred = "(" ^< p1 ^^ "|" ^< p2 ^> ")"
let path_transitive (p : pred) : pred = "(" ^< p ^> ")*"
								   
let empty : pattern = sparql ""
let something (s : term) : pattern = s ^> " a [] ."
let rdf_type (s : term) (c : term) : pattern = s ^^ " a " ^< c ^> " ."
let triple (s : term) (p : pred) (o : term) : pattern = s ^^ " " ^< p ^^ " " ^< o ^> " ."
let bind (e : expr) (v : var) : pattern = "BIND (" ^< e ^^ " AS " ^< v ^> ")"
let filter (e : expr) : pattern =
  if e = log_true then empty
  else "FILTER ( " ^< indent 9 e ^> " )"
let join (lp : pattern list) : pattern =
  concat "\n" (List.filter ((<>) empty) (Common.list_to_set lp))
let union (lp : pattern list) : pattern =
  if List.mem empty lp then invalid_arg "Sparql.union: empty pattern";
  match Common.list_to_set lp with
    | [] -> invalid_arg "Sparql.union: empty list"
    | [p] -> p
    | p::lp1 -> "{ " ^< indent 2 p ^^ " }\nUNION " ^< concat "\nUNION " (List.map (fun p -> "{ " ^< indent 8 p ^> " }") lp1)
let optional (p : pattern) : pattern =
  if p = empty then invalid_arg "Sparql.optional: empty pattern";
  "OPTIONAL { " ^< indent 11 p ^> " }"
let not_exists (p : pattern) : expr = "NOT EXISTS { " ^< indent 13 p ^> " }"
let graph (g : term) (p : pattern) : pattern = "GRAPH " ^< g ^^ "\n    { " ^< indent 6 p ^> " }"

let subquery (q : query) : pattern = "{ " ^< indent 2 q ^> " }"

let service (s : term) (p : pattern) : pattern = "SERVICE " ^< s ^^ " { " ^< p ^> " }"
  
let search_label (t : term) (l : term) : pattern =
  t ^^ " rdfs:label " ^< l ^> " ." (* ^ sparql_constr l (HasLang "en") *)
let search_contains (l : term) (w : string) : pattern =
  l ^^ " bif:contains " ^< string w ^> " ."


let ask (pattern : pattern) : query =
  "ASK\nWHERE { " ^< indent 8 pattern ^> " }"

type order = ASC of converter | DESC of converter

let ordering (order : order) (term : term) : ordering =
  match order with
  | ASC conv -> "ASC(" ^< conv (term :> expr) ^> ")"
  | DESC conv -> "DESC(" ^< conv (term :> expr) ^> ")"


type projection_def = [`Bare | `Expr of expr | `Aggreg of aggreg * term]
type projection = projection_def * Rdf.var

let projection_def : projection_def -> expr = function
  | `Bare -> sparql ""
  | `Expr e -> e
  | `Aggreg (g,t) -> (term_aggreg g t :> expr)

let projection (def,v : projection) : selector =
  match def with
  | `Bare -> (var v :> selector)
  | _ ->
    let e_def = projection_def def in
    if e_def = (var v :> expr)
    then (var v :> selector)
    else "(" ^< e_def ^^ " AS " ^< var v ^> ")"

let select
    ?(distinct=false)
    ~(projections : projection list)
    ?(froms : Rdf.uri list = [])
    ?(groupings : var list = [])
    ?(having : expr = log_true)
    ?(orderings : (order * var) list = [])
    ?(limit : int option)
    (pattern : pattern) : query =
  if projections = []
  then ask pattern
  else
    let sel = concat " " (List.map projection projections) in
    let s = "SELECT " ^< (if distinct then "DISTINCT " else "") ^< sel in
    let s =
      List.fold_left
	(fun s from -> s ^^ "\nFROM " ^< uri from)
	s froms in
    let s = s ^^ "\nWHERE { " ^< indent 8 pattern ^> " }" in
    let s =
      if groupings = [] || not (List.exists (function (`Aggreg _,_) -> true | _ -> false) projections)
      then s
      else s ^^ "\nGROUP BY " ^< concat " " groupings in
    let s =
      if having = log_true
      then s
      else s ^^ "\nHAVING ( " ^< indent 9 having ^> " )" in
    let s =
      if orderings = []
      then s
      else s ^^ "\nORDER BY " ^< concat " " (List.map (fun (order,v) -> ordering order (v :> term)) orderings) in
    let s = match limit with None -> s | Some n -> s ^> "\nLIMIT " ^ string_of_int n in
    s

let select_from_service url query : query =
  "SELECT * FROM { SERVICE <" ^< url ^< "> { " ^< query ^> " }}"


(* formulas *)

type formula =
  | Pattern of pattern (* binding *)
  | Subquery of subquery (* sub-queries *)
  | Filter of expr (* non-binding *)
  | True (* empty binding *)
  | False (* no binding *)
  | Or of pattern * expr (* mixed unions *)
and subquery =
  { projections : projection list;
    formula : formula;
    groupings : Rdf.var list;
    having : expr;
    limit : int option }

let make_subquery ~projections ?(groupings = []) ?(having = log_true) ?limit formula =
  { projections; formula; groupings; having; limit}

let subquery_having (sq : subquery) (e : expr) : subquery =
  { sq with having = log_and [sq.having; e] }

let rec pattern_of_formula : formula -> pattern = function
  | Pattern p -> p
  | Subquery sq -> pattern_of_subquery sq
  | Filter e -> filter e (* tentative *)
  | True -> empty
  | False -> filter log_false (* tentative *)
  | Or (p,e) -> union [p; filter e] (* tentative *)
and query_of_subquery : subquery -> query = function
  | { projections; formula; groupings; having; limit} ->
    select ~distinct:true ~projections ~groupings:(List.map var groupings) ~having ?limit (pattern_of_formula formula)
and pattern_of_subquery (sq : subquery) : pattern =
  if List.for_all (function (`Bare,_) -> true | _ -> false) sq.projections && sq.limit = None
  then pattern_of_formula sq.formula
  else subquery (query_of_subquery sq)

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
    | Subquery sq1, Subquery sq2
      when Common.equal_lists_as_sets sq1.groupings sq2.groupings
	&& sq1.formula = sq2.formula -> Subquery (join_subqueries [sq1; sq2])
    (* TODO: improve as mergeable subqueries may not be contiguous in formula list *)
    | Subquery sq1, _ -> formula_and (Pattern (pattern_of_subquery sq1)) f2
    | _, Subquery sq2 -> formula_and f1 (Pattern (pattern_of_subquery sq2))
    | Pattern p1, Pattern p2 -> Pattern (join [p1;p2])
    | Pattern p1, Filter e2 -> Pattern (join [p1; filter e2])
    | Filter e1, Pattern p2 -> Pattern (join [p2; filter e1])
    | Filter e1, Filter e2 -> Filter (log_and [e1; e2])
    | Pattern p1, Or (p2,e2) -> Pattern (union [join [p1;p2]; join [p1; filter e2]])
    | Filter e1, Or (p2,e2) -> Or (join [p2; filter e1], log_and [e1; e2])
    | Or (p1,e1), Pattern p2 -> Pattern (union [join [p1;p2]; join [p2; filter e1]])
    | Or (p1,e1), Filter e2 -> Or (join [p1; filter e2], log_and [e1; e2])
    | Or (p1,e1), Or (p2,e2) -> Or (union [join [p1; p2]; join [p1; filter e2]; join [p2; filter e1]], log_and [e1;e2])
and formula_and_list (lf : formula list) : formula =
  List.fold_left formula_and True lf
and join_subqueries (lsq : subquery list) : subquery =
  { projections = Common.list_to_set (List.concat (List.map (fun sq -> sq.projections) lsq));
    formula = formula_and_list (List.map (fun sq -> sq.formula) lsq);
    groupings = Common.list_to_set (List.concat (List.map (fun sq -> sq.groupings) lsq));
    having = log_and (List.map (fun sq -> sq.having) lsq);
    limit = (match lsq with [] -> None | sq::_ -> sq.limit) }


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

let rec formula_graph (g : term) : formula -> formula = function
  | Pattern p -> Pattern (graph g p)
  | Subquery sq -> Subquery {sq with formula = formula_graph g sq.formula}
  | Filter e -> Pattern (graph g (filter e))
  | True -> Pattern (graph g empty)
  | False -> False
  | Or (p,e) -> Pattern (graph g (union [p; filter e])) (* TODO: avoid union? *)
    
let expr_of_formula : formula -> expr = function
  | Filter e -> e
  | _ -> log_true (* TODO: dummy default *)


(* views *)

type view = ?limit:int -> unit -> subquery

let empty_view =
  (fun ?limit () -> make_subquery ~projections:[] True)

let simple_view (lx : Rdf.var list) (form : formula) : view =
  (fun ?limit () -> make_subquery
    ~projections:(List.map (fun x -> (`Bare,x)) lx)
    ~groupings:lx
    form)

let join_views (views : view list) : view =
  (fun ?limit () -> join_subqueries (List.map (fun view -> view ?limit ()) views))

let formula_of_view ?limit (view : view) : formula =
  Subquery (view ?limit ())

let is_empty_view view =
  let sq = view () in
  sq.formula = True
