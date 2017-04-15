
open Rdf
open Lisql

(* versioning *)

type version =  (* must be extended whenever abstract syntax changes *)
  | VInit (* initial permalink version *)
  | VId (* addition of LISQL ids in existential determiners (constructor An) *)

let current_version = VId (* must be changed whenever abstract syntax changes *)

(* shared by printing and parsing *)

let list_func_atom =
  [ `Str, "Str";
    `Lang, "Lang";
    `Datatype, "Dataype";
    `IRI, "IRI";
    `STRDT, "STRDT";
    `STRLANG, "STRLANG";
    `Strlen, "Strlen";
    `Substr2, "Substr2";
    `Substr3, "Substr3";
    `Strbefore, "Strbefore";
    `Strafter, "Strafter";
    `Concat, "Concat";
    `UCase, "UCase";
    `LCase, "LCase";
    `Encode_for_URI, "Encore_for_URI";
    `Replace, "Replace";
    `Integer, "Integer";
    `Decimal, "Decimal";
    `Double, "Double";
    `Indicator, "Indicator";
    `Add, "Add";
    `Sub, "Sub";
    `Mul, "Mul";
    `Div, "Div";
    `Neg, "Neg";
    `Abs, "Abs";
    `Round, "Round";
    `Ceil, "Ceil";
    `Floor, "Floor";
    `Random2, "Random2";
    `Date, "Date";
    `Time, "Time";
    `Year, "Year";
    `Month, "Month";
    `Day, "Day";
    `Hours, "Hours";
    `Minutes, "Minutes";
    `Seconds, "Seconds";
    `TODAY, "TODAY";
    `NOW, "NOW";
    `And, "BoolAnd";
    `Or, "BoolOr";
    `Not, "BoolNot";
    `EQ, "EQ";
    `NEQ, "NEQ";
    `GT, "GT";
    `GEQ, "GEQ";
    `LT, "LT";
    `LEQ, "LEQ";
    `BOUND, "BOUND";
    `IF, "IF";
    `IsIRI, "IsIRI";
    `IsBlank, "IsBlank";
    `IsLiteral, "IsLiteral";
    `IsNumeric, "IsNumeric";
    `StrStarts, "StrStarts";
    `StrEnds, "StrEnds";
    `Contains, "Contains";
    `LangMatches, "LangMatches";
    `REGEX, "REGEX"    
  ]
let list_num_conv_atom =
  [ (`Integer, false), "Integer";
    (`Integer, true), "IntegerStr";
    (`Decimal, false), "Decimal";
    (`Decimal, true), "DecimalStr";
    (`Double, false), "Double";
    (`Double, true), "DoubleStr";
  ]

let atom_of_func func =
  try List.assoc func list_func_atom
  with _ -> invalid_arg "Permalink.atom_of_func"
let func_of_atom atom =
  try fst (List.find (fun (_,a) -> a=atom) list_func_atom)
  with _ -> invalid_arg "Permalink.func_of_atom"

let atom_of_num_conv conv =
  try List.assoc conv list_num_conv_atom
  with _ -> invalid_arg "Permalink.atom_of_num_conv"
let num_conv_of_atom atom =
  try fst (List.find (fun (_,a) -> a=atom) list_num_conv_atom)
  with _ -> invalid_arg "Permalink.num_conv_of_atom"


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
let print_lr pr f lr = print_nary f (List.map pr lr)

let print_opt pr = function None -> print_atom "None" | Some x -> print_un "Some" (pr x)

(* printing elements: annotations are ignored *)
  
let rec print s =
  "[" ^ print_version current_version ^ "]" ^ print_s s
and print_s = function
  | Return (_,np) -> print_un "Return" (print_s1 np)
  | SAggreg (_,dims,aggregs) -> print_bin "SAggreg" (print_list print_dim "Dims" dims) (print_list print_aggreg "Aggregs" aggregs)
  | SExpr (_,"",id,modif,expr,rel_opt) -> print_nary "SExpr" [print_id id; print_modif modif; print_expr expr; print_opt print_p1 rel_opt]
  | SExpr (_,name,id,modif,expr,rel_opt) -> print_nary "SExprNamed" [print_string name; print_id id; print_modif modif; print_expr expr; print_opt print_p1 rel_opt]
  | SFilter (_,id,expr) -> print_bin "SFilter" (print_id id) (print_expr expr)
  | Seq (_,lr) -> print_lr print_s "Seq" lr
and print_dim = function
  | ForEachResult _ -> print_atom "ForeachResult"
  | ForEach (_,id,modif,rel_opt,id2) -> print_nary "Foreach" [print_id id; print_modif modif; print_opt print_p1 rel_opt; print_id id2]
  | ForTerm (_,t,id2) -> print_nary "Forterm" [print_term t; print_id id2]
and print_aggreg = function
  | TheAggreg (_,id,modif,g,rel_opt,id2) -> print_nary "TheAggreg" [print_id id; print_modif modif; print_aggreg_op g; print_opt print_p1 rel_opt; print_id id2]
and print_expr = function
  | Undef _ -> print_atom "Undef"
  | Const (_,t) -> print_un "Const" (print_term t)
  | Var (_,id) -> print_un "Var" (print_id id)
  | Apply (_,func,args) -> print_bin "Apply" (print_func func) (print_list print_apply_arg "Args" args)
  | Choice (_,le) -> print_list print_expr "Choice" le
and print_apply_arg = function
  | None, expr -> print_expr expr
  | Some conv, expr -> print_bin "Conv" (print_num_conv conv) (print_expr expr)
and print_p1 = function
  | Is (_,np) -> print_un "Is" (print_s1 np)
  | Type (_,c) -> print_un "Type" (print_uri c)
  | Rel (_,p,m,np) -> print_ter "Rel" (print_uri p) (print_modif_p2 m) (print_s1 np)
  | Triple (_,arg,np1,np2) -> print_ter "Triple" (print_arg arg) (print_s1 np1) (print_s1 np2)
  | LatLong (_,plat,plong,id1,id2) -> print_nary "LatLong" [print_uri plat; print_uri plong; print_id id1; print_id id2]
  | Search (_,c) -> print_un "Search" (print_constr c)
  | Filter (_,c) -> print_un "Filter" (print_constr c)
  | And (_,lr) -> print_lr print_p1 "And" lr
  | Or (_,lr) -> print_lr print_p1 "Or" lr
  | Maybe (_,f) -> print_un "Maybe" (print_p1 f)
  | Not (_,f) -> print_un "Not" (print_p1 f)
  | In (_,npg,f) -> print_bin "In" (print_s1 npg) (print_p1 f)
  | InWhichThereIs (_,np) -> print_un "InWhichThereIs" (print_s1 np)
  | IsThere _ -> print_atom "IsThere"
and print_modif_p2 = function
  | Fwd -> print_atom "Fwd"
  | Bwd -> print_atom "Bwd"
and print_s1 = function
  | Det (_,det,rel_opt) -> print_bin "Det" (print_s2 det) (print_opt print_p1 rel_opt)
  | AnAggreg (_,id,modif,g,rel_opt,np) -> print_nary "AnAggreg" [print_id id; print_modif modif; print_aggreg_op g; print_opt print_p1 rel_opt; print_s1 np]
  | NAnd (_,lr) -> print_lr print_s1 "NAnd" lr
  | NOr (_,lr) -> print_lr print_s1 "NOr" lr
  | NMaybe (_,f) -> print_un "NMaybe" (print_s1 f)
  | NNot (_,f) -> print_un "NNot" (print_s1 f)
  | NIn (_,npg,f) -> print_bin "NIn" (print_s1 npg) (print_s1 f)
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
and print_aggreg_op = function
  | NumberOf -> print_atom "NumberOf"
  | ListOf -> print_atom "ListOf"
  | Sample -> print_atom "Sample"
  | Total conv_opt -> print_un "TotalConv" (print_opt print_num_conv conv_opt)
  | Average conv_opt -> print_un "AverageConv" (print_opt print_num_conv conv_opt)
  | Maximum conv_opt -> print_un "MaximumConv" (print_opt print_num_conv conv_opt)
  | Minimum conv_opt  -> print_un "MinimumConv" (print_opt print_num_conv conv_opt)
and print_func = function
  | func -> print_atom (atom_of_func func)
and print_num_conv = function
  | conv -> print_atom (atom_of_num_conv conv)
and print_order = function
  | Unordered -> print_atom "Unordered"
  | Highest conv_opt -> print_un "HighestConv" (print_opt print_num_conv conv_opt)
  | Lowest conv_opt -> print_un "LowestConv" (print_opt print_num_conv conv_opt)
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

let of_query (q : 'a elt_s) : string = print q

(* multi-version parsing: unit annotations are used *)

open Genlex

let lexer = make_lexer ["[";"]";"("; ")"; ","]

let syntax_error msg = raise (Stream.Error msg)

let parse_version = parser
  | [< 'Ident "VInit" >] -> VInit
  | [< 'Ident "VId" >] -> VId
  | [<>] -> syntax_error "invalid version"

let parse_int ~version = parser [< 'Int i >] -> i
let parse_float ~version = parser [< 'Float f >] -> f
let parse_string ~version = parser [< 'String s >] -> s
let parse_atom ~version f = parser [< 'Ident id when id = f >] -> ()

let parse_un ~version f ps1 = parser [< 'Ident id when id = f; 'Kwd "(" ?? "missing ("; x1 = ps1 ~version; 'Kwd ")" ?? "missing )" >] -> x1
let parse_bin ~version f ps1 ps2 = parser [< 'Ident id when id = f; 'Kwd "(" ?? "missing ("; x1 = ps1 ~version; 'Kwd "," ?? "missing , 1/2"; x2 = ps2 ~version; 'Kwd ")" ?? "missing )" >] -> x1, x2
let parse_ter ~version f ps1 ps2 ps3 = parser [< 'Ident id when id = f; 'Kwd "(" ?? "missing (" ; x1 = ps1 ~version; 'Kwd "," ?? "missing , 1/3"; x2 = ps2 ~version; 'Kwd "," ?? "missing , 2/3"; x3 = ps3 ~version; 'Kwd ")" ?? "missing )" >] -> x1, x2, x3
let parse_quad ~version f ps1 ps2 ps3 ps4 = parser [< 'Ident id when id = f; 'Kwd "(" ?? "missing ("; x1 = ps1 ~version; 'Kwd "," ?? "missing , 1/4"; x2 = ps2 ~version; 'Kwd "," ?? "missing , 2/4"; x3 = ps3 ~version; 'Kwd "," ?? "missing , 3/4"; x4 = ps4 ~version; 'Kwd ")" ?? "missing )" >] -> x1, x2, x3, x4
let parse_quin ~version f ps1 ps2 ps3 ps4 ps5 = parser [< 'Ident id when id = f; 'Kwd "(" ?? "missing ("; x1 = ps1 ~version; 'Kwd "," ?? "missing , 1/5"; x2 = ps2 ~version; 'Kwd "," ?? "missing , 2/5"; x3 = ps3 ~version; 'Kwd "," ?? "missing , 3/5"; x4 = ps4 ~version; 'Kwd "," ?? "missing , 4/5"; x5 = ps5 ~version; 'Kwd ")" ?? "missing )" >] -> x1, x2, x3, x4, x5

let parse_opt ps ~version = parser
  | [< () = parse_atom ~version "None" >] -> None
  | [< x = parse_un ~version "Some" ps >] -> Some x
  | [<>] -> syntax_error "invalid option"

let rec parse_list ps ~version f = parser
  | [< 'Ident id when id = f; 'Kwd "(" ?? "missing ("; args = parse_args ps ~version >] -> args
and parse_args ps ~version = parser
  | [< 'Kwd ")" >] -> []
  | [< x = ps ~version; xs = parse_args_aux ps ~version >] -> x::xs
  | [<>] -> syntax_error "invalid args"
and parse_args_aux ps ~version = parser
  | [< 'Kwd ")" >] -> []
  | [< 'Kwd ","; x = ps ~version; xs = parse_args_aux ps ~version >] -> x::xs
  | [<>] -> syntax_error "invalid args_aux"

let parse_lr ps ~version f = parser
  | [< xs = parse_list ps ~version f >] -> xs

let rec parse = parser
  | [< 'Kwd "["; version = parse_version; 'Kwd "]" ?? "missing ]"; s = parse_s ~version >] -> s
  | [< s = parse_s ~version:VInit >] -> s
and parse_s ~version = parser
    | [< np = parse_un ~version "Return" parse_s1 >] -> Return ((),np)
    | [< dims, aggregs = parse_bin ~version "SAggreg" (fun ~version -> parse_list parse_dim ~version "Dims") (fun ~version -> parse_list parse_aggreg ~version "Aggregs") >] -> SAggreg ((),dims,aggregs)
    | [< id, modif, expr, rel_opt = parse_quad ~version "SExpr" parse_id parse_modif parse_expr (parse_opt parse_p1) >] -> SExpr ((), "", id, modif, expr, rel_opt)
    | [< name, id, modif, expr, rel_opt = parse_quin ~version "SExprNamed" parse_string parse_id parse_modif parse_expr (parse_opt parse_p1) >] -> SExpr ((), name, id, modif, expr, rel_opt)
    | [< id, expr = parse_bin ~version "SFilter" parse_id parse_expr >] -> SFilter ((), id, expr)
    | [< lr = parse_lr parse_s ~version "Seq" >] -> Seq ((),lr)
    | [<>] -> syntax_error "invalid s"
and parse_dim ~version = parser
    | [< () = parse_atom ~version "ForeachResult" >] -> ForEachResult ()
    | [< id, modif, rel_opt, id2 = parse_quad ~version "Foreach" parse_id parse_modif (parse_opt parse_p1) parse_id >] -> ForEach ((), id, modif, rel_opt, id2)
    | [< t, id2 = parse_bin ~version "Forterm" parse_term parse_id >] -> ForTerm ((), t, id2)
    | [<>] -> syntax_error "invalid dim"
and parse_aggreg ~version = parser
    | [< id, modif, g, rel_opt, id2 = parse_quin ~version "TheAggreg" parse_id parse_modif parse_aggreg_op (parse_opt parse_p1) parse_id >] -> TheAggreg ((), id, modif, g, rel_opt, id2)
    | [<>] -> syntax_error "invalid aggreg"
and parse_expr ~version = parser
    | [< () = parse_atom ~version "Undef" >] -> Undef ()
    | [< t = parse_un ~version "Const" parse_term >] -> Const ((), t)
    | [< id = parse_un ~version "Var" parse_id >] -> Var ((), id)
    | [< func, args = parse_bin ~version "Apply" parse_func (fun ~version -> parse_list parse_apply_arg ~version "Args") >] -> Apply ((), func, args)
    | [< le = parse_list parse_expr ~version "Choice" >] -> Choice ((), le)
    | [<>] -> syntax_error "invalid expr"
and parse_apply_arg ~version = parser
    | [< conv, expr = parse_bin ~version "Conv" parse_num_conv parse_expr >] -> (Some conv, expr)
    | [< expr = parse_expr ~version >] -> (None, expr)
and parse_p1 ~version = parser
  | [< np = parse_un ~version "Is" parse_s1 >] -> Is ((),np)
  | [< c = parse_un ~version "Type" parse_uri >] -> Type ((),c)
  | [< p, m, np = parse_ter ~version "Rel" parse_uri parse_modif_p2 parse_s1 >] -> Rel ((),p,m,np)
  | [< p, np = parse_bin ~version "Has" parse_uri parse_s1 >] -> Rel ((),p,Fwd,np) (* for backward compatibility *)
  | [< p, np = parse_bin ~version "IsOf" parse_uri parse_s1 >] -> Rel ((),p,Bwd,np) (* for backward compatibility *)
  | [< arg, np1, np2 = parse_ter ~version "Triple" parse_arg parse_s1 parse_s1 >] -> Triple ((),arg,np1,np2)
  | [< plat, plong, id1, id2 = parse_quad ~version "LatLong" parse_uri parse_uri parse_id parse_id >] -> LatLong ((),plat,plong,id1,id2)
  | [< c = parse_un ~version "Search" parse_constr >] -> Search ((),c)
  | [< c = parse_un ~version "Filter" parse_constr >] -> Filter ((),c)
  | [< c = parse_un ~version "Constr" parse_constr >] -> Filter ((),c) (* for backward compatibility *)
  | [< lr = parse_lr parse_p1 ~version "And" >] -> And ((),lr)
  | [< lr = parse_lr parse_p1 ~version "Or" >] -> Or ((),lr)
  | [< f = parse_un ~version "Maybe" parse_p1 >] -> Maybe ((),f)
  | [< f = parse_un ~version "Not" parse_p1 >] -> Not ((),f)
  | [< npg, f = parse_bin ~version "In" parse_s1 parse_p1 >] -> In ((),npg,f)
  | [< np = parse_un ~version "InWhichThereIs" parse_s1 >] -> InWhichThereIs ((),np)
  | [< () = parse_atom ~version "IsThere" >] -> IsThere ()
  | [<>] -> syntax_error "invalid p1"
and parse_modif_p2 ~version = parser
  | [< () = parse_atom ~version "Fwd" >] -> Fwd
  | [< () = parse_atom ~version "Bwd" >] -> Bwd
  | [<>] -> syntax_error "invalid modif_p2"
and parse_s1 ~version = parser
  | [< det, rel_opt = parse_bin ~version "Det" parse_s2 (parse_opt parse_p1) >] -> Det ((), det, rel_opt)
  | [< id, modif, g, rel_opt, np = parse_quin ~version "AnAggreg" parse_id parse_modif parse_aggreg_op (parse_opt parse_p1) parse_s1 >] -> AnAggreg ((),id,modif,g,rel_opt,np)
  | [< lr = parse_lr parse_s1 ~version "NAnd" >] -> NAnd ((),lr)
  | [< lr = parse_lr parse_s1 ~version "NOr" >] -> NOr ((),lr)
  | [< f = parse_un ~version "NMaybe" parse_s1 >] -> NMaybe ((),f)
  | [< f = parse_un ~version "NNot" parse_s1 >] -> NNot ((),f)
  | [< npg, f = parse_bin ~version "NIn" parse_s1 parse_s1 >] -> NIn ((),npg,f)
  | [<>] -> syntax_error "invalid s1"
and parse_s2 ~version = parser
  | [< t = parse_un ~version "Term" parse_term >] -> Term t
  | [< det_an = parse_s2_an ~version >] -> det_an
  | [< id = parse_un ~version "The" parse_id >] -> The id
  | [<>] -> syntax_error "invalid s2"
and parse_s2_an ~version =
  match version with
    | VInit -> (parser [< modif, head = parse_bin ~version "An" parse_modif parse_head >] -> An (Lisql.factory#new_id, modif, head))
    | VId -> (parser [< id, modif, head = parse_ter ~version "An" parse_id parse_modif parse_head >] -> An (id, modif, head))
and parse_head ~version  = parser
  | [< () = parse_atom ~version "Thing" >] -> Thing
  | [< c = parse_un ~version "Class" parse_uri >] -> Class c
  | [<>] -> syntax_error "invalid head"
and parse_arg ~version = parser
  | [< () = parse_atom ~version "S" >] -> S
  | [< () = parse_atom ~version "P" >] -> P
  | [< () = parse_atom ~version "O" >] -> O
  | [<>] -> syntax_error "invalid arg"
and parse_modif ~version = parser
  | [< p, o = parse_bin ~version "Modif" parse_project parse_order >] -> (p,o)
  | [<>] -> syntax_error "invalid modif"
and parse_project ~version = parser
  | [< () = parse_atom ~version "Unselect" >] -> Unselect
  | [< () = parse_atom ~version "Select" >] -> Select
  | [< _g, _o = parse_bin ~version "Aggreg" parse_aggreg_op parse_order >] -> Select (* Aggreg (g,o) is lost *)
  | [<>] -> syntax_error "invalid project"
and parse_aggreg_op ~version = parser
  | [< () = parse_atom ~version "NumberOf" >] -> NumberOf
  | [< () = parse_atom ~version "ListOf" >] -> ListOf
  | [< () = parse_atom ~version "Sample" >] -> Sample
  | [< conv_opt = parse_un ~version "TotalConv" (parse_opt parse_num_conv) >] -> Total conv_opt
  | [< () = parse_atom ~version "Total" >] -> Total None (* backward compat *)
  | [< conv_opt = parse_un ~version "AverageConv" (parse_opt parse_num_conv) >] -> Average conv_opt
  | [< () = parse_atom ~version "Average" >] -> Average None (* backward compat *)
  | [< conv_opt = parse_un ~version "MaximumConv" (parse_opt parse_num_conv) >] -> Maximum conv_opt
  | [< () = parse_atom ~version "Maximum" >] -> Maximum None (* backward compat *)
  | [< conv_opt = parse_un ~version "MinimumConv" (parse_opt parse_num_conv) >] -> Minimum conv_opt
  | [< () = parse_atom ~version "Minimum" >] -> Minimum None (* backward compat *)
  | [<>] -> syntax_error "invalid aggreg"
and parse_func ~version = parser
    | [< 'Ident atom >] -> func_of_atom atom
    | [<>] -> syntax_error "invalid func"
and parse_num_conv ~version = parser
    | [< 'Ident atom >] -> num_conv_of_atom atom
    | [<>] -> syntax_error "invalid num_conv"
and parse_order ~version = parser
    | [< () = parse_atom ~version "Unordered" >] -> Unordered
    | [< conv_opt = parse_un ~version "HighestConv" (parse_opt parse_num_conv) >] -> Highest conv_opt
    | [< () = parse_atom ~version "Highest" >] -> Highest None (* backward compat *)
    | [< conv_opt = parse_un ~version "LowestConv" (parse_opt parse_num_conv) >] -> Lowest conv_opt
    | [< () = parse_atom ~version "Lowest" >] -> Lowest None (* backward compat *)
    | [<>] -> syntax_error "invalid order"
and parse_constr ~version = parser
  | [< () = parse_atom ~version "True" >] -> True
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
  | [<>] -> syntax_error "invalid constr"
and parse_term ~version = parser
  | [< uri = parse_un ~version "URI" parse_uri >] -> URI uri
  | [< f, s, dt = parse_ter ~version "Number" parse_float parse_string parse_string >] -> Number (f,s,dt)
  | [< s, dt = parse_bin ~version "TypedLiteral" parse_string parse_uri >] -> TypedLiteral (s,dt)
  | [< s, lang = parse_bin ~version "PlainLiteral" parse_string parse_string >] -> PlainLiteral (s,lang)
  | [< id = parse_un ~version "Bnode" parse_string >] -> Bnode id
  | [< v = parse_un ~version "Var" parse_var >] -> Var v
  | [<>] -> syntax_error "invalid term"
and parse_uri ~version = parser [< s = parse_string ~version >] -> s
and parse_var ~version = parser [< s = parse_string ~version >] -> s
and parse_id ~version = parser [< i = parse_int ~version >] -> i

let to_query (str : string) : unit elt_s = parse (lexer (Stream.of_string str))
