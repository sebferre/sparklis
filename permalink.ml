
open Rdf
open Lisql

(* versioning *)

type version =  (* must be extended whenever abstract syntax changes *)
  | VInit (* initial permalink version *)
  | VId (* addition of LISQL ids in existential determiners (constructor An) *)

let current_version = VId (* must be changed whenever abstract syntax changes *)

(* current-version printing *)

let print_version = function
  | VInit -> "VInit"
  | VId -> "VId"

let print_int i = Printf.sprintf "%d" i
let print_float f = Printf.sprintf "%F" f
let print_string s = Printf.sprintf "%S" s
let print_atom f = f

let print_nary f args = f ^ "(" ^ String.concat "," args ^ ")"

let print_un f x1 = print_nary f [x1]
let print_bin f x1 x2 = print_nary f [x1;x2]
let print_ter f x1 x2 x3 = print_nary f [x1;x2;x3]
let print_list pr f lx = print_nary f (List.map pr lx)
let print_ar pr f ar = print_nary f (List.map pr (Array.to_list ar))

let print_opt pr = function None -> print_atom "None" | Some x -> print_un "Some" (pr x)

let rec print s =
  "[" ^ print_version current_version ^ "]" ^ print_s s
and print_s = function
  | Return np -> print_un "Return" (print_s1 np)
and print_p1 = function
  | Is np -> print_un "Is" (print_s1 np)
  | Type c -> print_un "Type" (print_uri c)
  | Rel (p,m,np) -> print_ter "Rel" (print_uri p) (print_modif_p2 m) (print_s1 np)
  | Triple (arg,np1,np2) -> print_ter "Triple" (print_arg arg) (print_s1 np1) (print_s1 np2)
  | Search c -> print_un "Search" (print_constr c)
  | Filter c -> print_un "Filter" (print_constr c)
  | And ar -> print_ar print_p1 "And" ar
  | Or ar -> print_ar print_p1 "Or" ar
  | Maybe f -> print_un "Maybe" (print_p1 f)
  | Not f -> print_un "Not" (print_p1 f)
  | IsThere -> print_atom "IsThere"
and print_modif_p2 = function
  | Fwd -> print_atom "Fwd"
  | Bwd -> print_atom "Bwd"
and print_s1 = function
  | Det (det, rel_opt) -> print_bin "Det" (print_s2 det) (print_opt print_p1 rel_opt)
  | AnAggreg (id,modif,g,rel_opt,np) -> print_nary "AnAggreg" [print_id id; print_modif modif; print_aggreg g; print_opt print_p1 rel_opt; print_s1 np]
  | NAnd ar -> print_ar print_s1 "NAnd" ar
  | NOr ar -> print_ar print_s1 "NOr" ar
  | NMaybe f -> print_un "NMaybe" (print_s1 f)
  | NNot f -> print_un "NNot" (print_s1 f)
and print_s2 = function
  | Term t -> print_un "Term" (print_term t)
  | An (id,modif,head) -> print_ter "An" (print_id id) (print_modif modif) (print_head head)
  | The id -> print_un "The" (print_id id)
and print_head = function
  | Thing -> print_atom "Thing"
  | Class c -> print_un "Class" (print_uri c)
and print_arg = function
  | S -> print_atom "S"
  | P -> print_atom "P"
  | O -> print_atom "O"
and print_modif = function
  | p, o -> print_bin "Modif" (print_project p) (print_order o)
and print_project = function
  | Unselect -> print_atom "Unselect"
  | Select -> print_atom "Select"
(*  | Aggreg (g,o) -> print_bin "Aggreg" (print_aggreg g) (print_order o) *)
and print_aggreg = function
  | NumberOf -> print_atom "NumberOf"
  | ListOf -> print_atom "ListOf"
  | Total -> print_atom "Total"
  | Average -> print_atom "Average"
  | Maximum -> print_atom "Maximum"
  | Minimum -> print_atom "Minimum"
and print_order = function
  | Unordered -> print_atom "Unordered"
  | Highest -> print_atom "Highest"
  | Lowest -> print_atom "Lowest"
and print_constr = function
  | True -> print_atom "True"
  | MatchesAll lw -> print_list print_string "MatchesAll" lw
  | MatchesAny lw -> print_list print_string "MatchesAny" lw
  | After s -> print_un "After" (print_string s)
  | Before s -> print_un "Before" (print_string s)
  | FromTo (s1,s2) -> print_bin "FromTo" (print_string s1) (print_string s2)
  | HigherThan s -> print_un "HigherThan" (print_string s)
  | LowerThan s -> print_un "LowerThan" (print_string s)
  | Between (s1,s2) -> print_bin "Between" (print_string s1) (print_string s2)
  | HasLang s -> print_un "HasLang" (print_string s)
  | HasDatatype s -> print_un "HasDatatype" (print_string s)
and print_term = function
  | URI uri -> print_un "URI" (print_uri uri)
  | Number (f,s,dt) -> print_ter "Number" (print_float f) (print_string s) (print_string dt)
  | TypedLiteral (s,dt) -> print_bin "TypedLiteral" (print_string s) (print_uri dt)
  | PlainLiteral (s,lang) -> print_bin "PlainLiteral" (print_string s) (print_string lang)
  | Bnode s -> print_un "Bnode" (print_string s)
  | Var v -> print_un "Var" (print_var v)
and print_uri uri = print_string uri
and print_var v = print_string v
and print_id id = print_int id

let of_query (q : elt_s) : string = print q

(* multi-version parsing *)

open Genlex

let lexer = make_lexer ["[";"]";"("; ")"; ","]

let parse_version = parser
  | [< 'Ident "VInit" >] -> VInit
  | [< 'Ident "VId" >] -> VId

let parse_int ~version = parser [< 'Int i >] -> i
let parse_float ~version = parser [< 'Float f >] -> f
let parse_string ~version = parser [< 'String s >] -> s
let parse_atom ~version f = parser [< 'Ident id when id = f >] -> ()

let parse_un ~version f ps1 = parser [< 'Ident id when id = f; 'Kwd "("; x1 = ps1 ~version; 'Kwd ")" >] -> x1
let parse_bin ~version f ps1 ps2 = parser [< 'Ident id when id = f; 'Kwd "("; x1 = ps1 ~version; 'Kwd ","; x2 = ps2 ~version; 'Kwd ")" >] -> x1, x2
let parse_ter ~version f ps1 ps2 ps3 = parser [< 'Ident id when id = f; 'Kwd "("; x1 = ps1 ~version; 'Kwd ","; x2 = ps2 ~version; 'Kwd ","; x3 = ps3 ~version; 'Kwd ")" >] -> x1, x2, x3
let parse_quin ~version f ps1 ps2 ps3 ps4 ps5 = parser [< 'Ident id when id = f; 'Kwd "("; x1 = ps1 ~version; 'Kwd ","; x2 = ps2 ~version; 'Kwd ","; x3 = ps3 ~version; 'Kwd ","; x4 = ps4 ~version; 'Kwd ","; x5 = ps5 ~version; 'Kwd ")" >] -> x1, x2, x3, x4, x5

let parse_opt ps ~version = parser [< _ = parse_atom ~version "None" >] -> None | [< x = parse_un ~version "Some" ps >] -> Some x

let rec parse_list ps ~version f = parser
  | [< 'Ident id when id = f; 'Kwd "("; args = parse_args ps ~version >] -> args
and parse_args ps ~version = parser
  | [< x = ps ~version; xs = parse_args_aux ps ~version >] -> x::xs
  | [< >] -> []
and parse_args_aux ps ~version = parser
  | [< 'Kwd ","; xs = parse_args ps ~version >] -> xs
  | [< 'Kwd ")" >] -> []

let parse_ar ps ~version f = parser
  | [< xs = parse_list ps ~version f >] -> Array.of_list xs

let rec parse = parser
  | [< 'Kwd "["; version = parse_version; 'Kwd "]"; s = parse_s ~version >] -> s
  | [< s = parse_s ~version:VInit >] -> s
and parse_s ~version = parser
  | [< np = parse_un ~version "Return" parse_s1 >] -> Return np
and parse_p1 ~version = parser
  | [< np = parse_un ~version "Is" parse_s1 >] -> Is np
  | [< c = parse_un ~version "Type" parse_uri >] -> Type c
  | [< p, m, np = parse_ter ~version "Rel" parse_uri parse_modif_p2 parse_s1 >] -> Rel (p,m,np)
  | [< p, np = parse_bin ~version "Has" parse_uri parse_s1 >] -> Rel (p,Fwd,np) (* for backward compatibility *)
  | [< p, np = parse_bin ~version "IsOf" parse_uri parse_s1 >] -> Rel (p,Bwd,np) (* for backward compatibility *)
  | [< arg, np1, np2 = parse_ter ~version "Triple" parse_arg parse_s1 parse_s1 >] -> Triple (arg,np1,np2)
  | [< c = parse_un ~version "Search" parse_constr >] -> Search c
  | [< c = parse_un ~version "Filter" parse_constr >] -> Filter c
  | [< c = parse_un ~version "Constr" parse_constr >] -> Filter c (* for backward compatibility *)
  | [< ar = parse_ar parse_p1 ~version "And" >] -> And ar
  | [< ar = parse_ar parse_p1 ~version "Or" >] -> Or ar
  | [< f = parse_un ~version "Maybe" parse_p1 >] -> Maybe f
  | [< f = parse_un ~version "Not" parse_p1 >] -> Not f
  | [< _ = parse_atom ~version "IsThere" >] -> IsThere
and parse_modif_p2 ~version = parser
  | [< _ = parse_atom "Fwd" >] -> Fwd
  | [< _ = parse_atom "Bwd" >] -> Bwd
and parse_s1 ~version = parser
  | [< det, rel_opt = parse_bin ~version "Det" parse_s2 (parse_opt parse_p1) >] -> Det (det, rel_opt)
  | [< id, modif, g, rel_opt, np = parse_quin ~version "AnAggreg" parse_id parse_modif parse_aggreg (parse_opt parse_p1) parse_s1 >] -> AnAggreg (id,modif,g,rel_opt,np)
  | [< ar = parse_ar parse_s1 ~version "NAnd" >] -> NAnd ar
  | [< ar = parse_ar parse_s1 ~version "NOr" >] -> NOr ar
  | [< f = parse_un ~version "NMaybe" parse_s1 >] -> NMaybe f
  | [< f = parse_un ~version "NNot" parse_s1 >] -> NNot f
and parse_s2 ~version = parser
  | [< t = parse_un ~version "Term" parse_term >] -> Term t
  | [< det_an = parse_s2_an ~version >] -> det_an
  | [< id = parse_un ~version "The" parse_id >] -> The id
and parse_s2_an ~version =
  match version with
    | VInit -> (parser [< modif, head = parse_bin ~version "An" parse_modif parse_head >] -> An (Lisql.factory#new_id, modif, head))
    | VId -> (parser [< id, modif, head = parse_ter ~version "An" parse_id parse_modif parse_head >] -> An (id, modif, head))
and parse_head ~version  = parser
  | [< _ = parse_atom ~version "Thing" >] -> Thing
  | [< c = parse_un ~version "Class" parse_uri >] -> Class c
and parse_arg ~version = parser
  | [< _ = parse_atom ~version "S" >] -> S
  | [< _ = parse_atom ~version "P" >] -> P
  | [< _ = parse_atom ~version "O" >] -> O
and parse_modif ~version = parser
  | [< p, o = parse_bin ~version "Modif" parse_project parse_order >] -> (p,o)
and parse_project ~version = parser
  | [< _ = parse_atom ~version "Unselect" >] -> Unselect
  | [< _ = parse_atom ~version "Select" >] -> Select
  | [< g, o = parse_bin ~version "Aggreg" parse_aggreg parse_order >] -> Select (* Aggreg (g,o) is lost *)
and parse_aggreg ~version = parser
  | [< _ = parse_atom ~version "NumberOf" >] -> NumberOf
  | [< _ = parse_atom ~version "ListOf" >] -> ListOf
  | [< _ = parse_atom ~version "Total" >] -> Total
  | [< _ = parse_atom ~version "Average" >] -> Average
  | [< _ = parse_atom ~version "Maximum" >] -> Maximum
  | [< _ = parse_atom ~version "Minimum" >] -> Minimum
and parse_order ~version = parser
  | [< _ = parse_atom ~version "Unordered" >] -> Unordered
  | [< _ = parse_atom ~version "Highest" >] -> Highest
  | [< _ = parse_atom ~version "Lowest" >] -> Lowest
and parse_constr ~version = parser
  | [< _ = parse_atom ~version "True" >] -> True
  | [< lw = parse_list parse_string ~version "MatchesAll" >] -> MatchesAll lw
  | [< lw = parse_list parse_string ~version "MatchesAny" >] -> MatchesAny lw
  | [< s = parse_un ~version "After" parse_string >] -> After s
  | [< s = parse_un ~version "Before" parse_string >] -> Before s
  | [< s1, s2 = parse_bin ~version "FromTo" parse_string parse_string >] -> FromTo (s1,s2)
  | [< s = parse_un ~version "HigherThan" parse_string >] -> HigherThan s
  | [< s = parse_un ~version "LowerThan" parse_string >] -> LowerThan s
  | [< s1, s2 = parse_bin ~version "Between" parse_string parse_string >] -> Between (s1,s2)
  | [< s = parse_un ~version "HasLang" parse_string >] -> HasLang s
  | [< s = parse_un ~version "HasDatatype" parse_string >] -> HasDatatype s
and parse_term ~version = parser
  | [< uri = parse_un ~version "URI" parse_uri >] -> URI uri
  | [< f, s, dt = parse_ter ~version "Number" parse_float parse_string parse_string >] -> Number (f,s,dt)
  | [< s, dt = parse_bin ~version "TypedLiteral" parse_string parse_uri >] -> TypedLiteral (s,dt)
  | [< s, lang = parse_bin ~version "PlainLiteral" parse_string parse_string >] -> PlainLiteral (s,lang)
  | [< id = parse_un ~version "Bnode" parse_string >] -> Bnode id
  | [< v = parse_un ~version "Var" parse_var >] -> Var v
and parse_uri ~version = parser [< s = parse_string ~version >] -> s
and parse_var ~version = parser [< s = parse_string ~version >] -> s
and parse_id ~version = parser [< i = parse_int ~version >] -> i

let to_query (str : string) : elt_s = parse (lexer (Stream.of_string str))
