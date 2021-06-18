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

open Lisql
   
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
| `Duration
| `Boolean
| `Conversion of datatype * num_conv * datatype (* (A,conv,B) : conv converts A to B *)
]

let of_input_type : input_type -> datatype = function
  | IRIInput -> `IRI
  | StringInput -> `String
  | FloatInput -> `Float
  | IntegerInput -> `Integer
  | DateInput -> `Date
  | TimeInput -> `Time
  | DateTimeInput -> `DateTime
  | DurationInput -> `Duration
  
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
      | `Duration -> aux `Literal
      | `Boolean -> [] (* type `Boolean used for filtering conditions, use function `Indicator to manipulate Boolean values *)
      | `Conversion _ -> assert false
  in
  List.map (fun dt -> (dt, aux dt))
    [`Term; `IRI_Literal; `IRI; `Blank; `Literal; `StringLiteral; `String;
     `Float; `Decimal; `Integer; `Date; `Time; `DateTime; `Duration; `Boolean]

type compatible = { bool : bool; conv_opt : num_conv option }
(* conv_opt field only well-defined when bool=true *)

let compatible_true = { bool=true; conv_opt=None }
let compatible_false = { bool=false; conv_opt=None }

let rec compatible_with dt1 dt2 : compatible =
  match dt1 with
  | `Conversion (dt1_src,conv,dt1_dest) ->
    let comp = compatible_with dt1_src dt2 in
    if comp.bool
    then { comp with conv_opt=None }
    else { (compatible_with dt1_dest dt2) with conv_opt = Some conv }
  | _ -> { bool=(List.mem dt2 (try List.assoc dt1 inheritance with _ -> assert false)); conv_opt=None }
    
let lcs_datatype dt1 dt2 =
  let inh1 = try List.assoc dt1 inheritance with _ -> assert false in
  let inh2 = try List.assoc dt2 inheritance with _ -> assert false in  
  try List.find (fun dt1 -> List.mem dt1 inh2) inh1 with _ -> assert false
    (* looking for most specific common type *)

let lcs_num_conv_opt conv1_opt conv2_opt = match conv1_opt, conv2_opt with
  | None, None -> None
  | None, _ -> conv2_opt
  | _, None -> conv2_opt
  | Some conv1, Some conv2 ->
    match conv1, conv2 with
    | (DoubleConv, b1) , (_, b2)
    | (_, b1), (DoubleConv, b2) -> Some (DoubleConv, b1||b2)
    | (DecimalConv, b1), (_,b2)
    | (_,b1), (DecimalConv,b2) -> Some (DecimalConv, b1||b2)
    | (_,b1), (_,b2) -> Some (IntegerConv, b1||b2)

let lcs_compatible (comp1 : compatible) (comp2 : compatible) : compatible =
  match comp1.bool, comp2.bool with
  | false, false -> comp1
  | false, true -> comp2
  | true, false -> comp1
  | true, true -> { bool = true; conv_opt = lcs_num_conv_opt comp1.conv_opt comp2.conv_opt }


(* typing functions *)

let of_num_conv : num_conv -> datatype = function
  | IntegerConv, _ -> `Integer
  | DecimalConv, _ -> `Decimal
  | DoubleConv, _ -> `Float

let of_numeric_literal s src_dt apply_str =
  if String.contains s 'E' || String.contains s 'e' then `Conversion (src_dt, (DoubleConv, apply_str), `Float)
  else if String.contains s '.' then `Conversion (src_dt, (DecimalConv, apply_str), `Decimal)
  else `Conversion (src_dt, (IntegerConv, apply_str), `Integer)

let rec of_term : Rdf.term -> datatype = function
  | Rdf.URI _ -> `IRI
  | Rdf.Number (_,s,dt) ->
    if dt = Rdf.xsd_integer then `Integer
    else if dt = Rdf.xsd_decimal then `Decimal
    else if dt = Rdf.xsd_double then `Float
    else
      let t = if dt="" then Rdf.PlainLiteral (s,"") else Rdf.TypedLiteral (s,dt) in
      let src_dt = of_term t in
      of_numeric_literal s src_dt (dt<>"")
  | Rdf.TypedLiteral (_,dt) ->
    if dt = Rdf.xsd_string then `String
    else if dt = Rdf.xsd_integer then `Integer
    else if dt = Rdf.xsd_decimal then `Decimal
    else if dt = Rdf.xsd_double then `Float
    else if dt = Rdf.xsd_date then `Date
    else if dt = Rdf.xsd_time then `Time
    else if dt = Rdf.xsd_dateTime then `DateTime
    else if dt = Rdf.xsd_duration then `Duration
    else if dt = Rdf.xsd_boolean then `Boolean
    else `Literal
  | Rdf.PlainLiteral (_,lang) ->
    if lang="" then `String
    else `StringLiteral
  | Rdf.Bnode _ -> `Blank
  | Rdf.Var _ -> `Term

let of_term_list (lt : Rdf.term list) : datatype list =
  List.fold_left
    (fun ldt t ->
     let dt = of_term t in
     if not (List.mem dt ldt)
     then dt::ldt
     else ldt)
    [] lt
		  
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

(*    
let aggreg_signatures : aggreg -> (datatype * datatype) list = function
  | NumberOf -> [ `IRI_Literal, `Integer ]
  | ListOf -> [ `Literal, `String ]
  | Sample -> [ `IRI_Literal, `IRI_Literal ]
  | Total _ -> [ `Integer, `Integer;
	       `Decimal, `Decimal;
	       `Float, `Float ]
  | Average _ -> [ `Decimal, `Decimal;
		 `Float, `Float ]
  | Minimum _
  | Maximum _ -> [ `Integer, `Integer;
		   `Decimal, `Decimal;
		   `Float, `Float;
		   `Literal, `Literal ]
*)

let constr_domains : constr -> datatype list = function
  (* constraints assimilated to one-argument functions with Bool results *)
  | True -> [`Term]
  | MatchesAll _
  | MatchesAny _
  | IsExactly _
  | StartsWith _
  | EndsWith _ -> [`IRI; `StringLiteral; `Date; `Time; `DateTime; `Duration]
  | After _
  | Before _
  | FromTo _ -> [`IRI; `StringLiteral; `Date; `Time; `Duration]
  | HigherThan _
  | LowerThan _
  | Between _ -> [`Float]
  | HasLang _ -> [`StringLiteral]
  | HasDatatype _ -> [`Literal]
  | ExternalSearch (WikidataSearch _, _) -> [`IRI]
  | ExternalSearch (TextQuery _, _) -> [`IRI]

       
let func_signatures : func -> (datatype list * datatype) list = function
  | Str -> [ [`IRI_Literal], `String ]
  | Lang -> [ [`StringLiteral], `String ]
  | Datatype -> [ [`Literal], `IRI ]
  | IRI -> [ [`IRI_Literal], `IRI ]
  | STRDT -> [ [`Literal; `IRI], `Literal ]
  | STRLANG -> [ [`Literal; `String], `StringLiteral ]
  | Strlen -> [ [`StringLiteral], `Integer ]
  | Substr2 -> [ [`StringLiteral; `Integer], `StringLiteral ]
  | Substr3 -> [ [`StringLiteral; `Integer; `Integer], `StringLiteral ]
  | Strbefore
  | Strafter
  | Concat -> [ [`StringLiteral; `StringLiteral], `StringLiteral ]
  | UCase
  | LCase
  | Encode_for_URI -> [ [`StringLiteral], `StringLiteral ]
  | Replace -> [ [`StringLiteral; `String; `String], `StringLiteral ]
  | Integer -> [ [`Literal], `Integer ]
  | Decimal -> [ [`Literal], `Decimal ]
  | Double -> [ [`Literal], `Float ]
  | Indicator -> [ [`Boolean], `Integer ]
  | Add -> [ [`Integer; `Integer], `Integer;
	      [`Decimal; `Decimal], `Decimal;
	      [`Float; `Float], `Float;
	      [`Duration; `Duration], `Duration;
	      [`DateTime; `Duration], `DateTime;
	      [`Date; `Duration], `Date;
	      [`Time; `Duration], `Time ]
  | Sub -> [ [`Integer; `Integer], `Integer;
	      [`Decimal; `Decimal], `Decimal;
	      [`Float; `Float], `Float;
	      [`Duration; `Duration], `Duration;
	      [`DateTime; `Duration], `DateTime;
	      [`Date; `Duration], `Date;
	      [`Time; `Duration], `Time;
	      [`DateTime; `DateTime], `Duration;
	      [`Date; `Date], `Duration;
	      [`Time; `Time], `Duration ]
  | Mul -> [ [`Integer; `Integer], `Integer;
	      [`Decimal; `Decimal], `Decimal;
	      [`Float; `Float], `Float;
	      [`Duration; `Float], `Duration ]
  | Div -> [ [`Decimal; `Decimal], `Decimal;
	      [`Float; `Float], `Float ]
  | Neg
  | Abs
  | Round
  | Ceil
  | Floor -> [ [`Integer], `Integer;
		[`Decimal], `Decimal;
		[`Float], `Float ]
  | Random2 -> [ [`Float; `Float], `Float ]
  | Date -> [ [`DateTime], `Date ]
  | Time -> [ [`DateTime], `Time ]
  | Year
  | Month
  | Day -> [ [`Date], `Integer;
	      [`Duration], `Integer ]
  | Hours
  | Minutes -> [ [`DateTime], `Integer;
		  [`Duration], `Integer ]
  | Seconds -> [ [`DateTime], `Float;
		  [`Duration], `Float ]
  | TODAY -> [ [], `Date ]
  | NOW -> [ [], `DateTime ]
  | And
  | Or -> [ [`Boolean; `Boolean], `Boolean ]
  | Not -> [ [`Boolean], `Boolean ]
  | EQ | NEQ
  | GEQ | GT
  | LEQ | LT -> [ [`Float; `Float], `Boolean;
		    [`StringLiteral; `StringLiteral], `Boolean;
		    [`DateTime; `DateTime], `Boolean;
		    [`Date; `Date], `Boolean ]
  | BOUND -> [ [`Term], `Boolean ] (* should be `Var instead of `Term *)
  | IF ->
    List.map (fun dt -> [`Boolean; dt; dt], dt)
      [`Integer; `Decimal; `Float;
       `String; `StringLiteral;
       `DateTime; `Date; `Boolean;
       `Literal; `Term]
  | IsIRI
  | IsBlank
  | IsLiteral
  | IsNumeric -> [ [`Term], `Boolean ]
  | StrStarts
  | StrEnds
  | Contains
  | LangMatches
  | REGEX
  | REGEX_i -> [ [`StringLiteral; `StringLiteral], `Boolean ]


let is_predicate (func : func) : bool =
  List.for_all
    (fun (_,dt) -> dt = `Boolean)
    (func_signatures func)

(* type constraints *)

type type_constraint = datatype list option (* list of possible types or anything *)

let union_constraints constr_list =
  List.fold_left (* unioning possible datatypes, allowing nothing more than already used *)
    (fun res constr ->
      match res, constr with
      | None, _ -> constr
      | _, None -> res
      | Some ldt1, Some ldt2 -> Some (Common.list_to_set (ldt1@ldt2)))
    None constr_list

(*
let check_input_constraint constr dt_input : bool =
  match constr with
  | None -> true
  | Some ldt -> List.exists (fun dt -> fst (compatible_with dt dt_input)) ldt (* disjunctive compatibility *)
let check_output_constraint constr dt_output : bool = (* assuming dt_ouput is not a conversion *)
  match constr with
  | None -> true
  | Some ldt -> List.exists (fun dt -> fst (compatible_with dt_output dt)) ldt
*)

let compatible_input_constraint constr dt_input : compatible =
  match constr with
  | None -> compatible_true
  | Some ldt ->
    List.fold_left
      (fun comp1 dt ->
	let comp2 = compatible_with dt dt_input in
	lcs_compatible comp1 comp2)
      compatible_false ldt
let check_input_constraint constr dt_input : bool =
  (compatible_input_constraint constr dt_input).bool

let compatible_output_constraint constr dt_output : compatible =
  match constr with
  | None -> compatible_true
  | Some ldt ->
    List.fold_left
      (fun comp1 dt ->
	let comp2 = compatible_with dt_output dt in
	lcs_compatible comp1 comp2)
      compatible_false ldt
let check_output_constraint constr dt_output : bool =
  (compatible_output_constraint constr dt_output).bool

let compatible_func_signatures func input_constr_list output_constr =
  List.filter
    (fun (input_dt_list,output_dt) ->
      check_output_constraint output_constr output_dt
      && List.for_all2 check_input_constraint input_constr_list input_dt_list)
    (func_signatures func)

type focus_type_constraints = { input_constr : type_constraint;
				output_constr : type_constraint }

let default_focus_type_constraints = { input_constr = None; output_constr = None }

let union_focus_type_constraints ftc1 ftc2 =
  { input_constr = union_constraints [ftc1.input_constr; ftc2.input_constr];
    output_constr = union_constraints [ftc1.output_constr; ftc2.output_constr] }
				       
exception TypeError

let rec constr_of_elt_expr (env : id -> type_constraint) : 'a elt_expr -> type_constraint (* raise TypeError *) = function
  | Undef _ -> None
  | Const (_,t) -> Some [of_term t]
  | Var (_,id) -> env id
  | Apply (_,func,args) ->
    let output_constr = None in
    let input_constr_list =
      List.map
	(fun (conv_opt,arg_expr) ->
	  match conv_opt with
	  | None -> constr_of_elt_expr env arg_expr
	  | Some conv -> Some [of_num_conv conv])
	args in
    let comp_sigs = compatible_func_signatures func input_constr_list output_constr in
    if comp_sigs = []
    then raise TypeError
    else Some (Common.list_to_set (List.map snd comp_sigs))
  | Choice (_,le) -> 
    let input_constr_list = List.map (constr_of_elt_expr env) le in
    union_constraints input_constr_list
    
let rec constr_of_ctx_expr (env : id -> type_constraint) : ctx_expr -> type_constraint (* raise TypeError *) = function
  | SExprX _ -> None
  | SFilterX _ -> None
  | ApplyX (func,ll_rr,conv_opt,ctx) ->
    let pos = 1 + List.length (fst ll_rr) in
    let output_constr = constr_of_ctx_expr env ctx in
    let input_constr_list =
      list_of_ctx None (map_ctx_list (fun (conv_opt,arg_expr) -> constr_of_elt_expr env arg_expr) ll_rr) in
    let comp_sigs = compatible_func_signatures func input_constr_list output_constr in
    if comp_sigs = []
    then raise TypeError
    else
      Some
	(Common.list_to_set
	   (List.map
	      (fun (input_dt_list,_) -> List.nth input_dt_list (pos-1))
	      comp_sigs))
  | ChoiceX (ll_rr,ctx) ->
    let le = list_of_ctx (Undef ()) ll_rr in
    let input_constr_list = List.map (constr_of_elt_expr env) le in
    union_constraints input_constr_list
    

let of_focus (env : Lisql.id -> type_constraint) (focus : focus) (focus_descr : Lisql_annot.focus_descr) : focus_type_constraints =
  match focus with
  | AtExpr (expr,ctx) ->
     { input_constr = (try constr_of_elt_expr env expr
		       with TypeError -> None);
       output_constr = (try constr_of_ctx_expr env ctx
			with TypeError -> None) }
  | _ ->
     match focus_descr#term with
     | `Undefined -> { input_constr = Some []; output_constr = None }
     | `Term t -> { input_constr = Some [of_term t]; output_constr = None }
     | `Id id -> { input_constr = env id; output_constr = None }
(*     
    match id_of_focus focus with
    | None -> { input_constr = Some []; output_constr = None }
    | Some id -> { input_constr = env id; output_constr = None }
 *)
		   
(* insertability of elements based on constraints *)

let compatibles_insertion (dt_arg_opt, dt_res) focus_constr : compatible * compatible =
  let comp_arg =
    match dt_arg_opt with
    | None -> compatible_true
    | Some dt_arg -> compatible_input_constraint focus_constr.input_constr dt_arg in
  let comp_res =
    compatible_output_constraint focus_constr.output_constr dt_res in
  comp_arg, comp_res

let is_insertable dt_arg_opt_res focus_constr =
  let comp_arg, comp_res = compatibles_insertion dt_arg_opt_res focus_constr in
  comp_arg.bool && comp_res.bool

let is_insertable_input input_dt focus_type_constraints =
  is_insertable
    (None, input_dt)
    focus_type_constraints

let is_insertable_constr constr focus_type_constraints =
  List.exists
    (fun domain_dt ->
     let comp = compatible_input_constraint focus_type_constraints.input_constr domain_dt in
     comp.bool)
    (constr_domains constr)
    
let compatibles_insertion_list ldt_arg_opt_res focus_type_constraints : compatible * compatible =
  List.fold_left
    (fun (comp_arg, comp_res) dt_arg_opt_res ->
      let comp_arg_1, comp_res_1 = compatibles_insertion dt_arg_opt_res focus_type_constraints in
      if comp_arg_1.bool && comp_res_1.bool
      then (lcs_compatible comp_arg comp_arg_1, lcs_compatible comp_res comp_res_1)
      else (comp_arg, comp_res))
    (compatible_false, compatible_false)
    ldt_arg_opt_res

let compatibles_insertion_func_pos func pos focus_type_constraints : compatible * compatible =
  compatibles_insertion_list
    (List.map
       (fun (ldt_params, dt_res) ->
	 try
	   let dt_arg_opt =
	     if pos=0
	     then None
	     else Some (List.nth ldt_params (pos-1)) in
	   (dt_arg_opt,dt_res)
	 with _ -> assert false)
       (func_signatures func))
    focus_type_constraints

    
let find_insertable_aggreg aggreg focus_type_constraints : Lisql.aggreg option =
  let aux_num f_aggreg =
    let comp = compatible_input_constraint focus_type_constraints.input_constr `Float in
    if comp.bool
    then Some (f_aggreg comp.conv_opt)
    else None
  in
  match aggreg with
  | NumberOf ->
    if check_input_constraint focus_type_constraints.input_constr `IRI_Literal
    then Some NumberOf
    else None
  | ListOf ->
    if check_input_constraint focus_type_constraints.input_constr `Literal
    then Some ListOf
    else None
  | Sample ->
    if check_input_constraint focus_type_constraints.input_constr `IRI_Literal
    then Some Sample
    else None
  | Total _ -> aux_num (fun conv_opt -> Total conv_opt) 
  | Average _ -> aux_num (fun conv_opt -> Average conv_opt) 
  | Maximum _ -> aux_num (fun conv_opt -> Maximum conv_opt) 
  | Minimum _ -> aux_num (fun conv_opt -> Minimum conv_opt) 

let find_insertable_order order focus_type_constraints : Lisql.order =
  let aux_num f_order =
    let comp = compatible_input_constraint focus_type_constraints.input_constr `Float in
    if comp.bool
    then f_order comp.conv_opt
    else f_order None
  in
  match order with
  | Unordered -> Unordered
  | Lowest _ -> aux_num (fun conv_opt -> Lowest conv_opt)
  | Highest _ -> aux_num (fun conv_opt -> Highest conv_opt)
