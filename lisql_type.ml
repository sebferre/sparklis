
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
  in
  List.map (fun dt -> (dt, aux dt))
    [`Term; `IRI_Literal; `IRI; `Blank; `Literal; `StringLiteral; `String; `Float; `Decimal; `Integer; `Date; `Time; `DateTime]

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


exception TypeError
    
let of_func_res func (args_typing : datatype option list) : datatype (* raise TypeError *) =
  let func_sigs = func_signatures func in
  try
    let func_sig =
      List.find
	(fun (params,_) ->
	  List.for_all2
	    (fun arg param ->
	      match arg with
	      | None -> true
	      | Some dt -> compatible_with dt param)
	    args_typing params)
	func_sigs in (* priority to most specific signatures *)
    snd (func_sig)
  with _ -> raise TypeError

let of_func_param func pos (res_typing : datatype option) : datatype (* raise TypeError *) =
  let func_sigs = func_signatures func in
  try
    let func_sig =
      List.find
	(fun (_,ret) ->
	  match res_typing with
	  | None -> true
	  | Some dt -> compatible_with ret dt)
	(List.rev func_sigs) in (* priority to most general signatures *)
    List.nth (fst func_sig) (pos-1)
  with _ -> raise TypeError


let rec of_elt_expr (env : id -> datatype list option) : 'a elt_expr -> datatype list option (* raise TypeError *) = function
  | Undef _ -> None
  | Const (_,t) -> Some [of_term t]
  | Var (_,id) -> env id
  | Apply (_,func,args) ->
    let args_typings =
      List.fold_right
	(fun arg typing ->
	  match of_elt_expr env arg with
	  | None -> List.map (fun t -> None::t) typing
	  | Some dts -> List.concat (List.map (fun t -> List.map (fun dt -> Some dt::t) dts) typing))
	args [[]] in
    Some
      (List.fold_left
	 (fun dts args_typing ->
	   try
	     let dt = of_func_res func args_typing in
	     if List.mem dt dts
	     then dts
	     else dt::dts
	   with _ -> dts)
	 [] args_typings)

let rec of_ctx_expr : ctx_expr -> datatype option (* raise TypeError *) = function
  | SExprX _ -> None
  | ApplyX (func,ll_rr,ctx) ->
    let pos = 1 + List.length (fst ll_rr) in
    let ctx_dt_opt = of_ctx_expr ctx in
    Some (of_func_param func pos ctx_dt_opt)

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
  let param_dt, res_dt = aggreg_signature aggreg in
  is_insertable (Some param_dt, res_dt) focus_type_constraints

let is_insertable_input input_dt focus_type_constraints =
  is_insertable
    (None, input_dt)
    focus_type_constraints


let is_insertable_func_pos func pos (ldt_opt, dt_opt) =
  try
    let param_dt = of_func_param func pos dt_opt in
    match ldt_opt with
    | None -> true
    | Some ldt -> List.exists (fun dt -> compatible_with dt param_dt) ldt
  with _ -> false
    
