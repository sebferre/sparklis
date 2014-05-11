
open Rdf
open Lisql

(* printing *)

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

let rec print_s = function
  | Return np -> print_un "Return" (print_s1 np)
and print_p1 = function
  | Is np -> print_un "Is" (print_s1 np)
  | Type c -> print_un "Type" (print_uri c)
  | Has (p,np) -> print_bin "Has" (print_uri p) (print_s1 np)
  | IsOf (p,np) -> print_bin "IsOf" (print_uri p) (print_s1 np)
  | Triple (arg,np1,np2) -> print_ter "Triple" (print_arg arg) (print_s1 np1) (print_s1 np2)
  | Search c -> print_un "Search" (print_constr c)
  | Filter c -> print_un "Filter" (print_constr c)
  | And ar -> print_ar print_p1 "And" ar
  | Or ar -> print_ar print_p1 "Or" ar
  | Maybe f -> print_un "Maybe" (print_p1 f)
  | Not f -> print_un "Not" (print_p1 f)
  | IsThere -> print_atom "IsThere"
and print_s1 = function
  | Det (det, rel_opt) -> print_bin "Det" (print_s2 det) (print_opt print_p1 rel_opt)
  | NAnd ar -> print_ar print_s1 "NAnd" ar
  | NOr ar -> print_ar print_s1 "NOr" ar
  | NMaybe f -> print_un "NMaybe" (print_s1 f)
  | NNot f -> print_un "NNot" (print_s1 f)
and print_s2 = function
  | Term t -> print_un "Term" (print_term t)
  | An (modif,head) -> print_bin "An" (print_modif modif) (print_head head)
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
  | Aggreg (g,o) -> print_bin "Aggreg" (print_aggreg g) (print_order o)
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

let of_query (q : elt_s) : string = print_s q

(* parsing *)

open Genlex

let lexer = make_lexer ["("; ")"; ","]

let parse_float = parser [< 'Float f >] -> f
let parse_string = parser [< 'String s >] -> s
let parse_atom f = parser [< 'Ident id when id = f >] -> ()

let parse_un f ps1 = parser [< 'Ident id when id = f; 'Kwd "("; x1 = ps1; 'Kwd ")" >] -> x1
let parse_bin f ps1 ps2 = parser [< 'Ident id when id = f; 'Kwd "("; x1 = ps1; 'Kwd ","; x2 = ps2; 'Kwd ")" >] -> x1, x2
let parse_ter f ps1 ps2 ps3 = parser [< 'Ident id when id = f; 'Kwd "("; x1 = ps1; 'Kwd ","; x2 = ps2; 'Kwd ","; x3 = ps3; 'Kwd ")" >] -> x1, x2, x3
let parse_opt ps = parser [< _ = parse_atom "None" >] -> None | [< x = parse_un "Some" ps >] -> Some x

let rec parse_list ps f = parser
  | [< 'Ident id when id = f; 'Kwd "("; args = parse_args ps >] -> args
and parse_args ps = parser
  | [< x = ps; xs = parse_args_aux ps >] -> x::xs
  | [< >] -> []
and parse_args_aux ps = parser
  | [< 'Kwd ","; xs = parse_args ps >] -> xs
  | [< 'Kwd ")" >] -> []

let parse_ar ps f = parser
  | [< xs = parse_list ps f >] -> Array.of_list xs

let rec parse_s = parser
  | [< np = parse_un "Return" parse_s1 >] -> Return np
and parse_p1 = parser
  | [< np = parse_un "Is" parse_s1 >] -> Is np
  | [< c = parse_un "Type" parse_uri >] -> Type c
  | [< p, np = parse_bin "Has" parse_uri parse_s1 >] -> Has (p,np)
  | [< p, np = parse_bin "IsOf" parse_uri parse_s1 >] -> IsOf (p,np)
  | [< arg, np1, np2 = parse_ter "Triple" parse_arg parse_s1 parse_s1 >] -> Triple (arg,np1,np2)
  | [< c = parse_un "Search" parse_constr >] -> Search c
  | [< c = parse_un "Filter" parse_constr >] -> Filter c
  | [< c = parse_un "Constr" parse_constr >] -> Filter c (* for backward compatibility *)
  | [< ar = parse_ar parse_p1 "And" >] -> And ar
  | [< ar = parse_ar parse_p1 "Or" >] -> Or ar
  | [< f = parse_un "Maybe" parse_p1 >] -> Maybe f
  | [< f = parse_un "Not" parse_p1 >] -> Not f
  | [< _ = parse_atom "IsThere" >] -> IsThere
and parse_s1 = parser
  | [< det, rel_opt = parse_bin "Det" parse_s2 (parse_opt parse_p1) >] -> Det (det, rel_opt)
  | [< ar = parse_ar parse_s1 "NAnd" >] -> NAnd ar
  | [< ar = parse_ar parse_s1 "NOr" >] -> NOr ar
  | [< f = parse_un "NMaybe" parse_s1 >] -> NMaybe f
  | [< f = parse_un "NNot" parse_s1 >] -> NNot f
and parse_s2 = parser
  | [< t = parse_un "Term" parse_term >] -> Term t
  | [< modif, head = parse_bin "An" parse_modif parse_head >] -> An (modif, head)
and parse_head = parser
  | [< _ = parse_atom "Thing" >] -> Thing
  | [< c = parse_un "Class" parse_uri >] -> Class c
and parse_arg = parser
  | [< _ = parse_atom "S" >] -> S
  | [< _ = parse_atom "P" >] -> P
  | [< _ = parse_atom "O" >] -> O
and parse_modif = parser
  | [< p, o = parse_bin "Modif" parse_project parse_order >] -> (p,o)
and parse_project = parser
  | [< _ = parse_atom "Unselect" >] -> Unselect
  | [< _ = parse_atom "Select" >] -> Select
  | [< g, o = parse_bin "Aggreg" parse_aggreg parse_order >] -> Aggreg (g,o)
and parse_aggreg = parser
  | [< _ = parse_atom "NumberOf" >] -> NumberOf
  | [< _ = parse_atom "ListOf" >] -> ListOf
  | [< _ = parse_atom "Total" >] -> Total
  | [< _ = parse_atom "Average" >] -> Average
  | [< _ = parse_atom "Maximum" >] -> Maximum
  | [< _ = parse_atom "Minimum" >] -> Minimum
and parse_order = parser
  | [< _ = parse_atom "Unordered" >] -> Unordered
  | [< _ = parse_atom "Highest" >] -> Highest
  | [< _ = parse_atom "Lowest" >] -> Lowest
and parse_constr = parser
  | [< _ = parse_atom "True" >] -> True
  | [< lw = parse_list parse_string "MatchesAll" >] -> MatchesAll lw
  | [< lw = parse_list parse_string "MatchesAny" >] -> MatchesAny lw
  | [< s = parse_un "After" parse_string >] -> After s
  | [< s = parse_un "Before" parse_string >] -> Before s
  | [< s1, s2 = parse_bin "FromTo" parse_string parse_string >] -> FromTo (s1,s2)
  | [< s = parse_un "HigherThan" parse_string >] -> HigherThan s
  | [< s = parse_un "LowerThan" parse_string >] -> LowerThan s
  | [< s1, s2 = parse_bin "Between" parse_string parse_string >] -> Between (s1,s2)
  | [< s = parse_un "HasLang" parse_string >] -> HasLang s
  | [< s = parse_un "HasDatatype" parse_string >] -> HasDatatype s
and parse_term = parser
  | [< uri = parse_un "URI" parse_uri >] -> URI uri
  | [< f, s, dt = parse_ter "Number" parse_float parse_string parse_string >] -> Number (f,s,dt)
  | [< s, dt = parse_bin "TypedLiteral" parse_string parse_uri >] -> TypedLiteral (s,dt)
  | [< s, lang = parse_bin "PlainLiteral" parse_string parse_string >] -> PlainLiteral (s,lang)
  | [< id = parse_un "Bnode" parse_string >] -> Bnode id
  | [< v = parse_un "Var" parse_var >] -> Var v
and parse_uri = parser [< s = parse_string >] -> s
and parse_var = parser [< s = parse_string >] -> s

let to_query (str : string) : elt_s = parse_s (lexer (Stream.of_string str))
