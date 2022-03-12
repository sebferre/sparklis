(*
   Copyright 2013 Sébastien Ferré, IRISA, Université de Rennes 1, ferre@irisa.fr

   This file is part of Sparklis.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Regexp = Js_of_ocaml.Regexp

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

type var_kind = [`Var]
type term_kind = [var_kind|`Term]
type expr_kind = [term_kind|`Expr]
type pred_kind = [term_kind|`Path]
type pattern_kind = [`Pattern]
type selector_kind = [var_kind|`Selector]
type ordering_kind = [`Ordering]
type query_kind = [`Query]

type var = var_kind sparql
type term = term_kind sparql
type expr = expr_kind sparql
type pred = pred_kind sparql
type pattern = pattern_kind sparql
type selector = selector_kind sparql
type ordering = ordering_kind sparql
type query = query_kind sparql

type 'a any_var = ([<var_kind] as 'a) sparql
type 'a any_term = ([<term_kind] as 'a) sparql
type 'a any_expr = ([<expr_kind] as 'a) sparql
type 'a any_pred = ([<pred_kind] as 'a) sparql
type 'a any_pattern = ([<pattern_kind] as 'a) sparql
type 'a any_selector = ([<selector_kind] as 'a) sparql
type 'a any_ordering = ([<ordering_kind] as 'a) sparql
type 'a any_query = ([<query_kind] as 'a) sparql

			
type converter = expr -> expr

let js_sparql_map : string Jsutils.js_map = Jsutils.(js_map `String)

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
      [("http://jena.apache.org/text#", "text:");
       ("http://www.irisa.fr/LIS/ferre/vocab/nary#", "nary:");
       ("https://schema.org/","sdo:");
       ("http://schema.org/","schema:");
       ("http://www.wikidata.org/prop/statement/value/","psv:");
       ("http://www.wikidata.org/prop/statement/","ps:");
       ("http://www.wikidata.org/prop/","p:");
       ("http://www.wikidata.org/prop/direct/","wdt:");
       ("http://wikiba.se/ontology#","wikibase:");
       ("http://purl.org/dc/terms/", "dcterms:");
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



let term_uri (uri : Rdf.uri) : term =
  match prologue#qname_of_uri uri with
  | None -> sparql ("<" ^ uri ^ ">")
  | Some qname -> sparql qname

let qname (qn : string) : term = sparql qn

let bnode (name : string) : term = sparql (if name="" then "[]" else "_:" ^ name)
    
let var (v : Rdf.var) : var = sparql ("?" ^ v)

let string : string -> term =
  let re_backslash = Regexp.regexp_string "\\" in
  let re_doublequote = Regexp.regexp_string "\"" in
  let re_linefeed = Regexp.regexp_string "\n" in
  let re_carriagereturn = Regexp.regexp_string "\r" in
  let escape s =
    let s = Regexp.global_replace re_backslash s "\\\\" in
    let s = Regexp.global_replace re_doublequote s "\\\"" in
    let s = Regexp.global_replace re_linefeed s "\\n" in
    let s = Regexp.global_replace re_carriagereturn s "\\r" in
    s in
  fun s -> sparql ("\"" ^ escape s ^ "\"")

let rec term : Rdf.term -> term = function
  | Rdf.URI u -> term_uri u
  | Rdf.Number (f,s,dt) -> if dt="" then term (Rdf.PlainLiteral (s,"")) else term (Rdf.TypedLiteral (s,dt))
  | Rdf.TypedLiteral (s,dt) -> string s ^^ sparql "^^" ^^ term_uri dt
  | Rdf.PlainLiteral (s,lang) -> string s ^^ sparql (if lang = "" then "" else "@" ^ lang)
  | Rdf.Bnode name -> bnode name
  | Rdf.Var v -> (var v :> term)

    
type aggreg =
| COUNT | DistinctCOUNT | DistinctCONCAT | SAMPLE | ID
| SUM of converter | AVG of converter | MAX of converter | MIN of converter

let term_aggreg (g : aggreg) (term : _ any_term) : term = (* assuming aggregates are terms (not expr) to simplify compilation of HAVING clauses *)
  let make_aggreg prefix_g expr suffix_g : term = prefix_g ^< expr ^> suffix_g in
  match g with
  | COUNT -> make_aggreg "COUNT(" term ")"
  | DistinctCOUNT -> make_aggreg "COUNT(DISTINCT " term ")"
  | DistinctCONCAT -> make_aggreg "GROUP_CONCAT(DISTINCT " term " ; separator='  /  ')"
  | SUM conv -> make_aggreg "SUM(" (conv (term :> expr)) ")"
  | AVG conv -> make_aggreg "AVG(" (conv (term :> expr)) ")"
  | MAX conv -> make_aggreg "MAX(" (conv (term :> expr)) ")"
  | MIN conv -> make_aggreg "MIN(" (conv (term :> expr)) ")"
  | SAMPLE -> make_aggreg "SAMPLE(" term ")"
  | ID -> make_aggreg "" term ""

let expr_func (f : string) (l_expr : _ any_expr list) : expr = f ^< "(" ^< concat "," l_expr ^> ")"
let expr_infix (op : string) (l_expr : _ any_expr list) : expr = "(" ^< concat (" " ^ op ^ " ") l_expr ^> ")"
let expr_regex (expr : _ any_expr) (pat : string) : expr = "REGEX(" ^< expr ^^ ", " ^< string pat ^> ", 'i')"
let expr_comp (relop : string) (expr1 : _ any_expr) (expr2 : _ any_expr) : expr = expr1 ^^ (" " ^ relop ^ " ") ^< expr2
let expr_in (e : _ any_expr) (le : _ any_expr list) : expr = e ^^ " IN (" ^< concat ", " le ^> ")"
let expr_not_in (e : _ any_expr) (le : _ any_expr list) : expr = e ^^ " NOT IN (" ^< concat ", " le ^> ")"
let expr_coalesce (le : _ any_expr list) : expr = "COALESCE(" ^< concat ", " le ^> ")"

let conv_numeric (e : _ any_expr) : expr = expr_func "xsd:double" [expr_func "str" [e]]

let log_true : expr = sparql "true"
let log_false : expr = sparql "false"
let log_not (e : _ any_expr) : expr =
  if e = log_true then log_false
  else if e = log_false then log_true
  else "!( " ^< indent 3 e ^> " )"
let log_and (le : _ any_expr list) : expr = 
  if List.mem log_false le then log_false
  else
    let le = List.filter ((<>) log_true) (Common.list_to_set le) in
    match le with
      | [] -> log_true
      | [e] -> e
      | _ -> "(  " ^< concat "\n&& " (List.map (indent 3) le) ^> " )"
let log_or (le : _ any_expr list) : expr =
  if List.mem log_true le then log_true
  else
    let le = List.filter ((<>) log_false) (Common.list_to_set le) in
    match le with
      | [] -> log_false
      | [e] -> e
      | _ -> "(  " ^< concat "\n|| " (List.map (indent 3) le) ^> " )"

let path_uri (uri : Rdf.uri) : pred =
  match prologue#qname_of_uri uri with
  | Some "rdf:item" -> sparql "rdf:rest*/rdf:first"
  | Some qname -> sparql qname
  | None -> sparql ("<" ^ uri ^ ">")
let path_seq (p1 : _ any_pred) (p2 : _ any_pred) : pred =
  if Rdf.config_wikidata_mode#value
  then
    let s1, s2 = (p1 : _ any_pred :> string), (p2 : _ any_pred :> string) in
    let n1, n2 = String.length s1, String.length s2 in
    if n1 > 2 && String.sub s1 0 2 = "p:"
       && n2 > 3 && String.sub s2 0 3 = "ps:"
    then (sparql ("wdt:" ^ String.sub s1 2 (n1-2)) : pred)
    else p1 ^^ "/" ^< p2
  else p1 ^^ "/" ^< p2
let path_alt (lp : _ any_pred list) : pred =
  match lp with
  | [] -> assert false
  | [p] -> p
  | _ -> "(" ^< concat "|" lp ^> ")"
let path_transitive (p : _ any_pred) : pred =
  (*if Common.has_suffix (p : 'a sparql :> string) "medDRA_parent" (* PEGASE-specific *)
     || Common.has_suffix (p : 'a sparql :> string) "SNOMED_parent"
  then p ^> "_star" (* materialized transitive closure. TODO: add predicate to declare them in a more general way *)
  else*) "(" ^< p ^> ")*"
let path_inverse (p : _ any_pred) : pred = "^(" ^< p ^> ")"
let path_interv (p : _ any_pred) (min : int) (max : int) : pred =
  "(" ^< p ^> (if min=0 && max=1
	       then ")?"
	       else "){" ^ string_of_int min ^ "," ^ string_of_int max ^ "}")
					   
let empty : pattern = sparql ""
let something (s : _ any_term) : pattern =
  if Rdf.config_wikidata_mode#value
  then s ^> " wdt:P31 [] ."
  else s ^> " a [] ."
let rdf_type (s : _ any_term) (c : _ any_term) : pattern =
  if Rdf.config_wikidata_mode#value
  then s ^^ " wdt:P31 " ^< c ^> " ."
  else s ^^ " a " ^< c ^> " ."
let triple (s : _ any_term) (p : _ any_pred) (o : _ any_term) : pattern = s ^^ " " ^< p ^^ " " ^< o ^> " ."
let bnode_triples (lpo : (_ any_pred * _ any_term) list) : term =
  "[ " ^< concat " ; " (List.map (fun (p,o) -> p ^^ " " ^< o) lpo) ^> " ]"
let bnode_triples_as_pattern lpo : pattern =
  bnode_triples lpo ^> " ."
let bind (e : _ any_expr) (v : var) : pattern = "BIND (" ^< e ^^ " AS " ^< v ^> ")"
let values (v : _ any_var) (l : _ any_term list) : pattern =
  "VALUES " ^< v ^^ " { " ^< concat " " l ^> "}"
let values_tuple (vs : _ any_var list) (lt : _ any_term list list) : pattern =
  "VALUES (" ^< concat " " vs ^^ ") { " ^< concat " " (List.map (fun t -> "(" ^< concat " " t ^> ")") lt) ^> "}"
let filter (e : _ any_expr) : pattern =
  if e = log_true then empty
  else "FILTER ( " ^< indent 9 e ^> " )"
let join (lp : _ any_pattern list) : pattern =
  let lp = List.filter ((<>) empty) lp in
  let lp = Common.list_to_set lp in
  concat "\n" lp
let union (lp : _ any_pattern list) : pattern =
  let lp = List.filter ((<>) empty) lp in
  match Common.list_to_set lp with
  | [] -> empty (* WARNING: should mean no solution *)
  | [p] -> p
  | p::lp1 -> "{ " ^< indent 2 p ^^ " }\nUNION " ^< concat "\nUNION " (List.map (fun p -> "{ " ^< indent 8 p ^> " }") lp1)
let optional (p : _ any_pattern) : pattern =
  if p = empty then empty (*invalid_arg "Sparql.optional: empty pattern" *)
  else "OPTIONAL { " ^< indent 11 p ^> " }"
let exists (p : _ any_pattern) : expr =
  if p = empty then sparql "true"
  else "EXISTS { " ^< indent 9 p ^> " }"
let not_exists (p : _ any_pattern) : expr =
  if p = empty then sparql "false"
  else "NOT EXISTS { " ^< indent 13 p ^> " }"
let graph (g : _ any_term) (p : _ any_pattern) : pattern =
  "GRAPH " ^< g ^^ "\n    { " ^< indent 6 p ^> " }"

let subquery (q : _ any_query) : pattern = "{ " ^< indent 2 q ^> " }"

let service (s : _ any_term) (p : _ any_pattern) : pattern = "SERVICE " ^< s ^^ " { " ^< p ^> " }"
  
let search_label (t : _ any_term) (l : _ any_term) : pattern =
  t ^^ " rdfs:label " ^< l ^> " ." (* ^ sparql_constr l (HasLang "en") *)
				
let bif_contains (l : _ any_term) (w : string) : pattern =
  l ^^ " bif:contains " ^< string w ^> " ."
let text_query (s : _ any_term) (q : string) : pattern =
  s ^^ " text:query " ^< string q ^> " ."

let ask (pattern : _ any_pattern) : query =
  "ASK\nWHERE { " ^< indent 8 pattern ^> " }"

type order = ASC of converter | DESC of converter

let ordering (order : order) (term : _ any_term) : ordering =
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
    ?(groupings : _ any_var list = [])
    ?(having : _ any_expr = log_true)
    ?(orderings : (order * var) list = [])
    ?(limit : int option)
    (pattern : _ any_pattern) : query =
  if projections = []
  then ask pattern
  else
    let sel = concat " " (List.map projection projections) in
    let s = "SELECT " ^< (if distinct then "DISTINCT " else "") ^< sel in
    let s =
      List.fold_left
	(fun s from -> s ^^ "\nFROM " ^< term_uri from)
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
      else s ^^ "\nORDER BY " ^< concat " " (List.map (fun (order,v) -> ordering order v) orderings) in
    let s = match limit with None -> s | Some n -> s ^> "\nLIMIT " ^ string_of_int n in
    s

let select_from_service url query : query =
  "SELECT * FROM { SERVICE <" ^< url ^< "> { " ^< query ^> " }}"

let wikidata_lat_long (x : _ any_term) (lat : _ any_var) (long : _ any_var) : pattern =
  join
    [ triple
	x
	(path_seq (qname "p:P625") (qname "psv:P625"))
	(bnode_triples
	   [ qname "wikibase:geoLatitude", lat;
	     qname "wikibase:geoLongitude", long ]) ]
    (* no more necessary it seems
      filter (log_and
		[ expr_comp "=" (expr_func "datatype" [lat]) (qname "xsd:decimal");
		  expr_comp "=" (expr_func "datatype" [long]) (qname "xsd:decimal") ]) ] *)

							     
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

let formula_is_binding = function
  | Pattern _ -> true
  | Subquery _ -> true
  | Filter _ -> false
  | True -> false
  | False -> false
  | Or _ -> true
    
let formula_term_in_term_list (t : _ any_term) (lt : _ any_term list) : formula =
  let s_t = (t : _ sparql :> string) in
  if s_t<>"" && s_t.[0]='?'
  then Pattern (values (sparql s_t :> var) lt)
  else Filter (expr_in t lt)

let make_subquery ~projections ?(groupings = []) ?(having = log_true) ?limit formula =
  { projections; formula; groupings; having; limit}

let subquery_having (sq : subquery) (e : _ any_expr) : subquery =
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

let formula_bind (x : _ any_term) : formula -> formula = function
  | Pattern p -> Pattern p
  | Subquery sq -> Subquery sq
  | Filter e -> Pattern (join [something x; filter e])
  | True -> True (*Pattern (something x)*)
  | False -> False
  | Or (p,e) -> Pattern (union [p; join [something x; filter e]])

let rec formula_graph (g : _ any_term) : formula -> formula = function
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
