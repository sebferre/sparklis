
(* types *)

type datatype =
[ `Term
| `IRI_Literal (* IRI or Literal *)
| `IRI
| `Blank
| `Literal (* any kind of literal *)
| `StringLiteral (* plain literal or xsd:string *)
| `String (* xsd:string *)
| `Numeric (* `Float or `Integer *)
| `Float (* xsd:decimal, xsd:float or xsd:double *)
| `Integer (* xsd:integer *)
| `Date
| `Time
| `DateTime
]

let inheritance : (datatype * datatype list) list =
  let rec aux dt =
    dt ::
      match dt with
      | `Term -> []
      | `IRI_Literal -> aux `Term
      | `IRI -> aux `IRI_Literal
      | `Blank -> aux `Term
      | `Literal -> aux `IRI_Literal
      | `StringLiteral -> aux `Literal
      | `String -> aux `StringLiteral
      | `Numeric -> aux `Literal
      | `Float -> aux `Numeric
      | `Integer -> aux `Numeric
      | `Date -> aux `Literal
      | `Time -> aux `Literal
      | `DateTime -> aux `Date
  in
  List.map (fun dt -> (dt, aux dt))
    [`Term; `IRI_Literal; `IRI; `Blank; `Literal; `StringLiteral; `String; `Numeric; `Float; `Integer; `Date; `Time; `DateTime]

let compatible_with dt1 dt2 =
  List.mem dt2 (List.assoc dt1 inheritance)
    
let lcs_datatype dt1 dt2 =
  let inh1 = try List.assoc dt1 inheritance with _ -> assert false in
  let inh2 = try List.assoc dt2 inheritance with _ -> assert false in  
  try List.find (fun dt1 -> List.mem dt1 inh2) inh1 with _ -> assert false
    (* looking for most specific common type *)

(* typing functions *)

let of_term : Rdf.term -> datatype = function
  | Rdf.URI _ -> `IRI
  | Rdf.Number (_,_,dt) ->
    if dt = Rdf.xsd_integer then `Integer
    else `Float
  | Rdf.TypedLiteral (_,dt) ->
    if dt = Rdf.xsd_string then `String
    else if dt = Rdf.xsd_integer then `Integer
    else if List.mem dt [Rdf.xsd_double; Rdf.xsd_decimal] (* or parses as float *) then `Float
    else if dt = Rdf.xsd_date then `Date
    else if dt = Rdf.xsd_time then `Time
    else if dt = Rdf.xsd_dateTime then `DateTime
    else `Literal
  | Rdf.PlainLiteral (_,lang) ->
    if lang="" then `String
    else `StringLiteral
  | Rdf.Bnode _ -> `Blank
  | Rdf.Var _ -> `Term

let of_sparql_results (results : Sparql_endpoint.results) : datatype list array =
  let typing = Array.make results.Sparql_endpoint.dim [] in
  List.iter
    (fun binding ->
      Array.iteri
	(fun i -> function
	| None -> ()
	| Some t ->
	  let l = typing.(i) in
	  let dt = of_term t in
	  if not (List.mem dt l) then
	    typing.(i) <- dt::l)
	binding)
    results.Sparql_endpoint.bindings;
  typing
    
open Lisql

let of_aggreg_pos (aggreg : aggreg) (pos : int) : datatype =
  match aggreg, pos with
  | NumberOf, 0 -> `Integer
  | NumberOf, 1 -> `IRI_Literal
  | ListOf, 0 -> `String
  | ListOf, 1 -> `Literal
  | (Total | Average), (0 | 1) -> `Numeric
  | (Maximum | Minimum), 0 -> `Literal
  | (Maximum | Minimum), 1 -> `Literal
  | Sample, (0 | 1) -> `IRI_Literal
  | _ -> invalid_arg "Lisql_type.of_aggreg_pos"
    
let of_func_pos (func : func) (pos : int) : datatype =
  match func, pos with
  | `Str, 0 -> `String
  | `Str, 1 -> `IRI_Literal
  | `Lang, 0 -> `String
  | `Lang, 1 -> `StringLiteral
  | `Datatype, 0 -> `IRI
  | `Datatype, 1 -> `Literal
  | `IRI, 0 -> `IRI
  | `IRI, 1 -> `IRI_Literal
  | `STRDT, 0 -> `Literal
  | `STRDT, 1 -> `String
  | `STRDT, 2 -> `IRI
  | `STRLANG, 0 -> `Literal
  | `STRLANG, (1 | 2) -> `String
  | `Strlen, 0 -> `Integer
  | `Strlen, 1 -> `StringLiteral
  | `Substr2, (0 | 1) -> `StringLiteral
  | `Substr2, 2 -> `Integer
  | `Substr3, (0 | 1) -> `StringLiteral
  | `Substr3, (2 | 3) -> `Integer
  | `Strbefore, (0 | 1 | 2) -> `StringLiteral
  | `Strafter, (0 | 1 | 2) -> `StringLiteral
  | `Concat, _ -> `StringLiteral
  | (`UCase | `LCase | `Encode_for_URI), (0 | 1) -> `StringLiteral
  | `Replace, (0 | 1) -> `StringLiteral
  | `Replace, (2 | 3) -> `String
  | `Integer, 0 -> `Integer
  | `Double, 0 -> `Float
  | (`Integer | `Double), 1 -> `Literal
  | (`Add | `Sub | `Mul | `Div | `Neg | `Abs), _ -> `Numeric
  | (`Round | `Ceil | `Floor), 0 -> `Integer
  | (`Round | `Ceil | `Floor), 1 -> `Float
  | `Random2, (0 | 1 | 2) -> `Float
  | `Date, 0 -> `Date
  | `Date, 1 -> `DateTime
  | `Time, 0 -> `Time
  | `Time, 1 -> `DateTime
  | (`Year | `Month | `Day | `Hours | `Minutes), 0 -> `Integer
  | `Seconds, 0 -> `Float
  | (`Year | `Month | `Day), 1 -> `Date
  | (`Hours | `Minutes | `Seconds), 1 -> `DateTime
  | `TODAY, 0 -> `Date
  | `NOW, 0 -> `DateTime
  | _ -> invalid_arg "Lisql_type.of_func_arg"

let of_elt_expr (env : id -> datatype list option) : 'a elt_expr -> datatype list option = function
  | Undef _ -> None
  | Const (_,t) -> Some [of_term t]
  | Var (_,id) -> env id
  | Apply (_,func,args) -> Some [of_func_pos func 0]

let of_ctx_expr : ctx_expr -> datatype option = function
  | SExprX _ -> None
  | ApplyX (func,ll_rr,ctx) ->
    let pos = 1 + List.length (fst ll_rr) in
    Some (of_func_pos func pos)
      
type focus_type_constraints = datatype list option * datatype option

let of_focus env : focus -> focus_type_constraints = function
  | AtExpr (expr,ctx) -> (of_elt_expr env expr, of_ctx_expr ctx)
  | focus ->
    match id_of_focus focus with
    | None -> (None, None)
    | Some id -> (env id, None)

let is_insertable (dt_arg_opt, dt_res) (ldt_opt, dt_opt) =
  let arg_ok =
    match dt_arg_opt, ldt_opt with
    | _, None -> true
    | None, Some ldt -> false
    | Some dt_arg, Some ldt ->
      List.exists (fun dt -> compatible_with dt dt_arg) ldt in
  let res_ok =
    match dt_opt with
    | None -> true
    | Some dt -> compatible_with dt_res dt in
  arg_ok && res_ok

let is_insertable_aggreg aggreg focus_type_constraints =
  is_insertable
    (Some (of_aggreg_pos aggreg 1), of_aggreg_pos aggreg 0)
    focus_type_constraints
      
let is_insertable_func_pos func pos focus_type_constraints =
  is_insertable
    (Some (of_func_pos func pos), of_func_pos func 0)
    focus_type_constraints

let is_insertable_input input_dt focus_type_constraints =
  is_insertable
    (None, input_dt)
    focus_type_constraints
