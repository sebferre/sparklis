
(* types *)

type datatype =
[ `Term
| `IRI_Literal (* IRI or Literal *)
| `IRI
| `Blank
| `Literal (* any kind of literal *)
| `StringLiteral (* plain literal or xsd:string *)
| `String (* xsd:string *)
| `Float (* xsd:float or xsd:double *)
| `Decimal (* xsd:decimal *)
| `Integer (* xsd:integer *)
| `Date
| `Time
| `DateTime
| `Boolean
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
      | `Float -> aux `Literal
      | `Decimal -> aux `Float
      | `Integer -> aux `Decimal
      | `Date -> aux `Literal
      | `Time -> aux `Literal
      | `DateTime -> aux `Date
      | `Boolean -> aux `Literal
  in
  List.map (fun dt -> (dt, aux dt))
    [`Term; `IRI_Literal; `IRI; `Blank; `Literal; `StringLiteral; `String; `Float; `Decimal; `Integer; `Date; `Time; `DateTime; `Boolean]

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
    else if dt = Rdf.xsd_decimal then `Decimal
    else `Float
  | Rdf.TypedLiteral (_,dt) ->
    if dt = Rdf.xsd_string then `String
    else if dt = Rdf.xsd_integer then `Integer
    else if dt = Rdf.xsd_decimal then `Decimal
    else if dt = Rdf.xsd_double (* or parses as float *) then `Float
    else if dt = Rdf.xsd_date then `Date
    else if dt = Rdf.xsd_time then `Time
    else if dt = Rdf.xsd_dateTime then `DateTime
    else if dt = Rdf.xsd_boolean then `Boolean
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

let aggreg_signature : aggreg -> datatype * datatype = function
  | NumberOf -> `IRI_Literal, `Integer
  | ListOf -> `Literal, `String
  | Total
  | Average -> `Float, `Float
  | Minimum
  | Maximum -> `Literal, `Literal
  | Sample -> `IRI_Literal, `IRI_Literal

let func_signatures : func -> (datatype list * datatype) list = function
  | `Str -> [ [`IRI_Literal], `String ]
  | `Lang -> [ [`StringLiteral], `String ]
  | `Datatype -> [ [`Literal], `IRI ]
  | `IRI -> [ [`IRI_Literal], `IRI ]
  | `STRDT -> [ [`String; `IRI], `Literal ]
  | `STRLANG -> [ [`String; `String], `Literal ]
  | `Strlen -> [ [`StringLiteral], `Integer ]
  | `Substr2 -> [ [`StringLiteral; `Integer], `StringLiteral ]
  | `Substr3 -> [ [`StringLiteral; `Integer; `Integer], `StringLiteral ]
  | `Strbefore
  | `Strafter
  | `Concat -> [ [`StringLiteral; `StringLiteral], `StringLiteral ]
  | `UCase
  | `LCase
  | `Encode_for_URI -> [ [`StringLiteral], `StringLiteral ]
  | `Replace -> [ [`StringLiteral; `String; `String], `StringLiteral ]
  | `Integer -> [ [`Literal], `Integer ]
  | `Double -> [ [`Literal], `Float ]
  | `Add
  | `Sub
  | `Mul -> [ [`Integer; `Integer], `Integer;
	      [`Decimal; `Decimal], `Decimal;
	      [`Float; `Float], `Float ]
  | `Div -> [ [`Decimal; `Decimal], `Decimal;
	      [`Float; `Float], `Float ]
  | `Neg
  | `Abs
  | `Round
  | `Ceil
  | `Floor -> [ [`Integer], `Integer;
		[`Decimal], `Decimal;
		[`Float], `Float ]
  | `Random2 -> [ [`Float; `Float], `Float ]
  | `Date -> [ [`DateTime], `Date ]
  | `Time -> [ [`DateTime], `Time ]
  | `Year
  | `Month
  | `Day -> [ [`Date], `Integer ]
  | `Hours
  | `Minutes -> [ [`DateTime], `Integer ]
  | `Seconds -> [ [`DateTime], `Float ]
  | `TODAY -> [ [], `Date]
  | `NOW -> [ [], `DateTime]
  | `And
  | `Or -> [ [`Boolean; `Boolean], `Boolean ]
  | `Not -> [ [`Boolean], `Boolean ]
  | `EQ | `NEQ
  | `GEQ | `GT
  | `LEQ | `LT -> [ [`Float; `Float], `Boolean;
		    [`StringLiteral; `StringLiteral], `Boolean;
		    [`DateTime; `DateTime], `Boolean;
		    [`Date; `Date], `Boolean;
		    [`Boolean; `Boolean], `Boolean ]
  | `BOUND -> [ [`Term], `Boolean ] (* should be `Var instead of `Term *)
  | `IF ->
    List.map (fun dt -> [`Boolean; dt; dt], dt)
      [`Integer; `Decimal; `Float;
       `String; `StringLiteral;
       `DateTime; `Date; `Boolean;
       `Literal; `Term]
  | `IsIRI
  | `IsBlank
  | `IsLiteral
  | `IsNumeric -> [ [`Term], `Boolean ]
  | `StrStarts
  | `StrEnds
  | `Contains
  | `LangMatches
  | `REGEX -> [ [`StringLiteral; `StringLiteral], `Boolean ]


let is_predicate (func : func) : bool =
  List.for_all
    (fun (_,dt) -> dt = `Boolean)
    (func_signatures func)

(* type constraints *)

type type_constraint = datatype list option (* list of possible types or anything *)

let check_input_constraint constr dt_input =
  match constr with
  | None -> true
  | Some ldt -> List.exists (fun dt -> compatible_with dt dt_input) ldt
let check_output_constraint constr dt_output =
  match constr with
  | None -> true
  | Some ldt -> List.exists (fun dt -> compatible_with dt_output dt) ldt

let compatible_func_signatures func input_constr_list output_constr =
  List.filter
    (fun (input_dt_list,output_dt) ->
      check_output_constraint output_constr output_dt
      && List.for_all2 check_input_constraint input_constr_list input_dt_list)
    (func_signatures func)

type focus_type_constraints = { input_constr : type_constraint;
				output_constr : type_constraint }

let default_focus_type_constraints = { input_constr = None; output_constr = None }
  
exception TypeError

let rec constr_of_elt_expr (env : id -> type_constraint) : 'a elt_expr -> type_constraint (* raise TypeError *) = function
  | Undef _ -> None
  | Const (_,t) -> Some [of_term t]
  | Var (_,id) -> env id
  | Apply (_,func,args) ->
    let output_constr = None in
    let input_constr_list = List.map (constr_of_elt_expr env) args in
    let comp_sigs = compatible_func_signatures func input_constr_list output_constr in
    if comp_sigs = []
    then raise TypeError
    else Some (Common.list_to_set (List.map snd comp_sigs))

let rec constr_of_ctx_expr (env : id -> type_constraint) : ctx_expr -> type_constraint (* raise TypeError *) = function
  | SExprX _ -> None
  | SFilterX _ -> Some [`Boolean]
  | ApplyX (func,ll_rr,ctx) ->
    let pos = 1 + List.length (fst ll_rr) in
    let output_constr = constr_of_ctx_expr env ctx in
    let input_constr_list =
      list_of_ctx None (map_ctx_list (constr_of_elt_expr env) ll_rr) in
    let comp_sigs = compatible_func_signatures func input_constr_list output_constr in
    if comp_sigs = []
    then raise TypeError
    else
      Some
	(Common.list_to_set
	   (List.map
	      (fun (input_dt_list,_) -> List.nth input_dt_list (pos-1))
	      comp_sigs))

let of_focus env : focus -> focus_type_constraints = function
  | AtExpr (expr,ctx) -> { input_constr = constr_of_elt_expr env expr;
			   output_constr = constr_of_ctx_expr env ctx }
  | focus ->
    match id_of_focus focus with
    | None -> { input_constr = None; output_constr = None }
    | Some id -> { input_constr = env id; output_constr = None }

(* insertability of elements based on constraints *)

let is_insertable (dt_arg_opt, dt_res) focus_constr =
  let arg_ok =
    match dt_arg_opt with
    | None -> true
    | Some dt_arg -> check_input_constraint focus_constr.input_constr dt_arg in
  let res_ok =
    check_output_constraint focus_constr.output_constr dt_res in
  arg_ok && res_ok

let is_insertable_aggreg aggreg focus_type_constraints =
  let param_dt, res_dt = aggreg_signature aggreg in
  is_insertable (Some param_dt, res_dt) focus_type_constraints

let is_insertable_input input_dt focus_type_constraints =
  is_insertable
    (None, input_dt)
    focus_type_constraints

let is_insertable_func_pos func pos focus_type_constraints =
  List.exists
    (fun (ldt_params, dt_res) ->
      try
	let dt_arg_opt =
	  if pos=0
	  then None
	  else Some (List.nth ldt_params (pos-1)) in
	is_insertable (dt_arg_opt,dt_res) focus_type_constraints
      with _ -> assert false)
    (func_signatures func)
