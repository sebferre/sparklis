
type term = string
type expr = string
type pattern = string
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
      [("http://www.w3.org/2002/07/owl#", "owl:"); 
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
  
  method declarations : string =
    let buf = Buffer.create 500 in
    List.fold_right
      (fun (ns,pre) () ->
	Buffer.add_string buf "PREFIX ";
	Buffer.add_string buf pre;
	Buffer.add_string buf " <";
	Buffer.add_string buf ns;
	Buffer.add_string buf ">\n")
      map ();
    Buffer.contents buf

end

let uri (uri : Rdf.uri) : term =
  match prologue#qname_of_uri uri with
    | None -> "<" ^ uri ^ ">"
    | Some qname -> qname

let var (v : Rdf.var) : term = "?" ^ v

let string (s : string) : term =
  if String.contains s '\n' || String.contains s '"'
  then "\"\"\"" ^ s ^ "\"\"\""
  else "\"" ^ s ^ "\""

let rec term : Rdf.term -> term = function
  | Rdf.URI u -> uri u
  | Rdf.Number (f,s,dt) -> term (Rdf.TypedLiteral (s,dt))
  | Rdf.TypedLiteral (s,dt) -> string s ^ "^^" ^ uri dt
  | Rdf.PlainLiteral (s,lang) -> string s ^ (if lang = "" then "" else "@" ^ lang)
  | Rdf.Bnode name -> if name="" then "[]" else "_:" ^ name
  | Rdf.Var v -> var v

let term_numeric (t : Rdf.term) : expr = "STRDT(str(" ^ term t ^ "),xsd:double)"

let expr_func (f : string) (expr : expr) : expr = f ^ "(" ^ expr ^ ")"
let expr_regex (expr : expr) (pat : string) : expr = "REGEX(" ^ expr ^ ", \"" ^ pat ^ "\", 'i')"
let expr_comp (relop : string) (expr1 : expr) (expr2 : expr) : expr = expr1 ^ " " ^ relop ^ " " ^ expr2

let log_true : expr = "true"
let log_false : expr = "false"
let log_not (e : expr) : expr =
  if e = log_true then log_false
  else if e = log_false then log_true
  else "!(" ^ e ^ ")"
let log_and (le : expr list) : expr = 
  if List.mem log_false le then log_false
  else "(" ^ String.concat "\n && " (List.filter ((<>) log_true) le) ^ ")"
let log_or (le : expr list) : expr =
  if List.mem log_true le then log_true
  else "(" ^ String.concat "\n || " (List.filter ((<>) log_false) le) ^ ")"

let empty : pattern = ""
let something s = term s ^ " a [] ."
let rdf_type s c = term s ^ " a " ^ term c ^ " ."
let triple s p o = term s ^ " " ^ term p ^ " " ^ term o ^ " ."
let filter (e : expr) : pattern =
  if e = log_true then empty
  else "FILTER (" ^ e ^ ")"
let join (lp : pattern list) : pattern =
  String.concat "\n" (List.filter ((<>) empty) lp)
let union (lp : pattern list) : pattern =
  if List.mem empty lp then invalid_arg "Sparql.union: empty pattern";
  match lp with
    | [] -> invalid_arg "Sparql.union: empty list"
    | [p] -> p
    | _ -> String.concat "\n UNION " (List.map (fun p -> "{ " ^ p ^ " }") lp)
let optional (p : pattern) : pattern =
  if p = empty then invalid_arg "Sparql.optional: empty pattern";
  "OPTIONAL { " ^ p ^ " }"
let not_exists (p : pattern) : expr = "NOT EXISTS { " ^ p ^ " }"


let search_label (t : Rdf.term) (l : Rdf.term) : pattern =
  term t ^ " rdfs:label " ^ term l ^ " ." (* ^ sparql_constr l (HasLang "en") *)
let search_contains (l : Rdf.term) (w : string) : pattern =
  term l ^ " bif:contains " ^ string w ^ " ."


let ask (pattern : pattern) : query =
  prologue#declarations ^ "ASK WHERE {\n" ^ pattern ^ "\n}"

type aggreg = DistinctCOUNT | DistinctCONCAT | SUM | AVG | MAX | MIN
type order = ASC | DESC

let select
    ?(distinct=false)
    ~(dimensions : Rdf.var list)
    ?(aggregations : (aggreg * Rdf.var * Rdf.var) list = [])
    ?(ordering : (order * Rdf.var) list = [])
    ?(limit : int option)
    (pattern : pattern) : query =
  if dimensions = [] && aggregations = []
  then ask pattern
  else
    let make_aggreg prefix_g v suffix_g vg = "(" ^ prefix_g ^ var v ^ suffix_g ^ " AS " ^ var vg ^ ")" in
    let sel =
      String.concat " " (List.map var dimensions) ^ " " ^
	String.concat " "
	(List.map
	   (fun (g,v,vg) ->
	     match g with
	       | DistinctCOUNT -> make_aggreg "COUNT(DISTINCT " v ")" vg
	       | DistinctCONCAT -> make_aggreg "GROUP_CONCAT(DISTINCT " v (" ; separator=', ')") vg
	       | SUM -> make_aggreg "SUM(" v ")" vg
	       | AVG -> make_aggreg "AVG(" v ")" vg
	       | MAX -> make_aggreg "MAX(" v ")" vg
	       | MIN -> make_aggreg "MIN(" v ")" vg)
	   aggregations) in
    let s = "SELECT " ^ (if distinct then "DISTINCT " else "") ^ sel ^ " WHERE {\n" ^ pattern ^ "\n}" in
    let s =
      if aggregations = [] || dimensions = []
      then s
      else s ^ "\nGROUP BY " ^ String.concat " " (List.map var dimensions) in
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
    prologue#declarations ^ s

type formula =
  | Pattern of pattern (* binding *)
  | Filter of expr (* non-binding *)
  | True (* empty binding *)
  | False (* no binding *)
  | Or of pattern * expr (* mixed unions *)

let formula_and (f1 : formula) (f2 : formula) : formula =
  match f1, f2 with
    | False, _
    | _, False -> False
    | True, _ -> f2
    | _, True -> f1
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

(*
let formula_or (f1 : formula) (f2 : formula) : formula =
  match f1, f2 with
    | False, _ -> f2
    | _, False -> f1
    | True, True -> True
    | True, Pattern p2 -> Or (p2, log_true)
    | Pattern p1, True -> Or (p1, log_true)
    | True, Filter _ -> True
    | Filter _, True -> True
    | True, Or (p2,_) -> Or (p2, log_true)
    | Or (p1,_), True -> Or (p1, log_true)
    | Pattern p1, Pattern p2 -> Pattern (union [p1;p2])
    | Filter e1, Filter e2 -> Filter (log_or [e1;e2])
    | Pattern p1, Filter e2 -> Or (p1,e2)
    | Filter e1, Pattern p2 -> Or (p2,e1)
    | Or (p1,e1), Pattern p2 -> Or (union [p1;p2], e1)
    | Or (p1,e1), Filter e2 -> Or (p1, log_or [e1;e2])
    | Pattern p1, Or (p2,e2) -> Or (union [p1;p2], e2)
    | Filter e1, Or (p2,e2) -> Or (p2, log_or [e1;e2])
    | Or (p1,e1), Or (p2,e2) -> Or (union [p1;p2], log_or [e1;e2])
*)

let formula_or_list (lf : formula list) : formula =
  let lp, le, btrue =
    List.fold_right
      (fun f (lp,le,btrue) ->
	match f with
	  | Pattern p -> (p::lp,le,btrue)
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

(*  List.fold_left formula_or False lf *)

let formula_optional : formula -> formula = function
  | Pattern p -> Pattern (optional p)
  | Filter e -> True
  | True -> True
  | False -> True
  | Or (p,_) -> Or (p, log_true)

let formula_not : formula -> formula = function
  | Pattern p -> Filter (not_exists p)
  | Filter e -> Filter (log_not e)
  | True -> False
  | False -> True
  | Or (p,e) -> Filter (log_and [not_exists p; log_not e])

let formula_bind (x : Rdf.term) : formula -> formula = function
  | Pattern p -> Pattern p
  | Filter e -> Pattern (join [something x; filter e])
  | True -> True (*Pattern (something x)*)
  | False -> False
  | Or (p,e) -> Pattern (union [p; join [something x; filter e]])

let pattern_of_formula : formula -> pattern = function
  | Pattern p -> p
  | Filter e -> filter e (* tentative *)
  | True -> empty
  | False -> filter log_false (* tentative *)
  | Or (p,e) -> union [p; filter e] (* tentative *)
