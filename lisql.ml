
open Common
  
(* LISQL representations *)

(* LISQL constraints *)
type constr =
  | True
  | MatchesAll of string list
  | MatchesAny of string list
  | After of string
  | Before of string
  | FromTo of string * string
  | HigherThan of string
  | LowerThan of string
  | Between of string * string
  | HasLang of string
  | HasDatatype of string


(* LISQL modifiers *)
type id = int
type arg = S | P | O
type project = Unselect | Select (* | Aggreg of aggreg * order *)
type order = Unordered | Highest | Lowest
type modif_s2 = project * order
type modif_p2 = Fwd | Bwd

type num_conv = [`Integer | `Decimal | `Double] (* subset of type [func] *)
type aggreg =
| NumberOf | ListOf | Sample
| Total of num_conv option | Average of num_conv option | Maximum of num_conv option | Minimum of num_conv option
type func =
[ `Str
| `Lang | `Datatype
| `IRI | `STRDT | `STRLANG
| `Strlen | `Substr2 | `Substr3 | `Strbefore | `Strafter
| `Concat | `UCase | `LCase | `Encode_for_URI | `Replace
| `Integer | `Decimal | `Double
| `Add | `Sub | `Mul | `Div | `Neg
| `Abs | `Round | `Ceil | `Floor | `Random2 (* from some range *)
| `Date | `Time
| `Year | `Month | `Day | `Hours | `Minutes | `Seconds
| `TODAY | `NOW
| `And | `Or | `Not
| `EQ | `NEQ | `GT | `GEQ | `LT | `LEQ
| `BOUND | `IF
| `IsIRI | `IsBlank | `IsLiteral | `IsNumeric
| `StrStarts | `StrEnds | `Contains | `LangMatches | `REGEX ]
(* missing: timezone, hash functions, BNODE *)

(* LISQL elts : 'a param is for element annotations (hook) *)
type 'a elt_p1 =
  | Is of 'a * 'a elt_s1
  | Type of 'a * Rdf.uri
  | Rel of 'a * Rdf.uri * modif_p2 * 'a elt_s1
  | Triple of 'a * arg * 'a elt_s1 * 'a elt_s1 (* abstraction arg + other S1 arguments in order: S, P, O *)
  | Search of 'a * constr
  | Filter of 'a * constr
  | And of 'a * 'a elt_p1 list
  | Or of 'a * 'a elt_p1 list
  | Maybe of 'a * 'a elt_p1
  | Not of 'a * 'a elt_p1
  | IsThere of 'a
and 'a elt_s1 =
  | Det of 'a * elt_s2 * 'a elt_p1 option
  | AnAggreg of 'a * id * modif_s2 * aggreg * 'a elt_p1 option * 'a elt_s1 (* aggregation: elt_s1 must be a Det or a AnAggreg *)
  | NAnd of 'a * 'a elt_s1 list
  | NOr of 'a * 'a elt_s1 list
  | NMaybe of 'a * 'a elt_s1
  | NNot of 'a * 'a elt_s1
and elt_s2 =
  | Term of Rdf.term
  | An of id * modif_s2 * elt_head (* existential quantifier *)
  | The of id (* co-reference *)
and elt_head =
  | Thing
  | Class of Rdf.uri
and 'a elt_dim =
  | Foreach of 'a * id * modif_s2 * 'a elt_p1 option * id
and 'a elt_aggreg =
  | TheAggreg of 'a * id * modif_s2 * aggreg * 'a elt_p1 option * id
and 'a elt_expr =
  | Undef of 'a
  | Const of 'a * Rdf.term
  | Var of 'a * id
  | Apply of 'a * func * 'a elt_expr list
and 'a elt_s =
  | Return of 'a * 'a elt_s1
  | SAggreg of 'a * 'a elt_dim list * 'a elt_aggreg list
  | SExpr of 'a * id * modif_s2 * 'a elt_expr * 'a elt_p1 option
  | SFilter of 'a * id * 'a elt_expr (* Boolean expr *)
  | Seq of 'a * 'a elt_s list (* we will avoid unnecessary nestings of Seq, but we keep it for future extensions of elt_s *)


(* list context *)

type 'a ctx_list = 'a list * 'a list
      
let list_of_ctx (x : 'a) (ll,rr : 'a ctx_list) : 'a list = List.rev ll @ x :: rr

let ctx_of_list (lr : 'a list) : ('a * 'a ctx_list) list =
  let rec aux ll = function
    | [] -> []
    | x::rr -> (x,(ll,rr)) :: aux (x::ll) rr
  in
  aux [] lr

let ctx_of_ctx_list (x : 'a) (ll,rr : 'a ctx_list) : ('a * 'a ctx_list) ctx_list =
  let rec aux_left rr = function
    | [] -> []
    | x1::ll1 -> (x1, (ll1,rr)) :: aux_left (x1::rr) ll1
  in
  let rec aux_right ll = function
    | [] -> []
    | x1::rr1 -> (x1, (ll,rr1)) :: aux_right (x1::ll) rr1
  in
  aux_left (x::rr) ll, aux_right (x::ll) rr
    
let map_ctx_list (f : 'a -> 'b) (ll,rr : 'a ctx_list) : 'b ctx_list = (List.map f ll, List.map f rr)
    
      
(* LISQL contexts : no annotations in contexts *)
type ctx_p1 =
  | DetThatX of elt_s2 * ctx_s1
  | AnAggregThatX of id * modif_s2 * aggreg * unit elt_s1 * ctx_s1
  | ForeachThatX of id * modif_s2 * id * ctx_dim
  | TheAggregThatX of id * modif_s2 * aggreg * id * ctx_aggreg
  | SExprThatX of id * modif_s2 * unit elt_expr * ctx_s
  | AndX of unit elt_p1 ctx_list * ctx_p1 (* first list is reverse prefix, second list is suffix *)
  | OrX of unit elt_p1 ctx_list * ctx_p1
  | MaybeX of ctx_p1
  | NotX of ctx_p1
and ctx_s1 =
  | IsX of ctx_p1
  | RelX of Rdf.uri * modif_p2 * ctx_p1
  | TripleX1 of arg * unit elt_s1 * ctx_p1 (* context on first S1 arg *)
  | TripleX2 of arg * unit elt_s1 * ctx_p1 (* context on second S1 arg *)
  | ReturnX of ctx_s
  | AnAggregX of id * modif_s2 * aggreg * unit elt_p1 option * ctx_s1
  | NAndX of unit elt_s1 ctx_list * ctx_s1
  | NOrX of unit elt_s1 ctx_list * ctx_s1
  | NMaybeX of ctx_s1
  | NNotX of ctx_s1
and ctx_dim =
  | SAggregForeachX of unit elt_dim ctx_list * unit elt_aggreg list * ctx_s
and ctx_aggreg =
  | SAggregX of unit elt_dim list * unit elt_aggreg ctx_list * ctx_s
and ctx_expr =
  | ApplyX of func * unit elt_expr ctx_list * ctx_expr
  | SExprX of id * modif_s2 * unit elt_p1 option * ctx_s
  | SFilterX of id * ctx_s
and ctx_s =
  | Root
  | SeqX of unit elt_s ctx_list * ctx_s

(* LISQL focus: no annotations in focus *)
type focus =
  | AtP1 of unit elt_p1 * ctx_p1
  | AtS1 of unit elt_s1 * ctx_s1
  | AtDim of unit elt_dim * ctx_dim
  | AtAggreg of unit elt_aggreg * ctx_aggreg
  | AtExpr of unit elt_expr * ctx_expr
  | AtS of unit elt_s * ctx_s

let factory =
object (self)
  val mutable cpt_id = 0
  method new_id = cpt_id <- cpt_id + 1; cpt_id
  method set n = cpt_id <- n
  method reset = cpt_id <- 0

  method top_p1 = IsThere ()
  method top_modif = (Select, Unordered)
  method top_s2 = An (self#new_id, self#top_modif, Thing)
  method top_s1 = Det ((), self#top_s2, None)
  method top_expr = Undef ()
  method top_s = Return ((), self#top_s1)
  method home_focus = AtS1 (self#top_s1, ReturnX Root)
end

let is_top_p1 = function IsThere _ -> true | _ -> false
let is_top_s2 = function An (_, (Select, Unordered), Thing) -> true | _ -> false
let is_top_s1 = function Det (_, det, None) -> is_top_s2 det | _ -> false
let is_top_expr = function Undef _ -> true | _ -> false
let is_top_s = function Return (_, np) -> is_top_s1 np | _ -> false
let is_home_focus = function AtS1 (f, ReturnX Root) -> is_top_s1 f | _ -> false

let is_root_focus = function AtS (_, Root) -> true | _ -> false

let rec is_aggregation_focus = function
  | AtS1 (AnAggreg _, _) -> true
  | AtS1 (_, ctx) -> is_aggregation_ctx_s1 ctx
  | AtP1 (_, ctx) -> is_aggregation_ctx_p1 ctx
  | AtDim _ -> false
  | AtAggreg _ -> true
  | AtExpr _ -> false
  | AtS _ -> false
and is_aggregation_ctx_p1 = function
  | DetThatX (_,ctx) -> is_aggregation_ctx_s1 ctx
  | AnAggregThatX _ -> true
  | ForeachThatX _ -> false
  | TheAggregThatX _ -> true
  | SExprThatX _ -> false
  | AndX (_,ctx) -> is_aggregation_ctx_p1 ctx
  | OrX (_,ctx) -> is_aggregation_ctx_p1 ctx
  | MaybeX ctx -> is_aggregation_ctx_p1 ctx
  | NotX ctx -> is_aggregation_ctx_p1 ctx
and is_aggregation_ctx_s1 = function
  | IsX ctx -> is_aggregation_ctx_p1 ctx
  | RelX _ -> false
  | TripleX1 _ -> false
  | TripleX2 _ -> false
  | ReturnX _ -> false
  | AnAggregX _ -> false
  | NAndX (_,ctx) -> is_aggregation_ctx_s1 ctx
  | NOrX (_,ctx) -> is_aggregation_ctx_s1 ctx
  | NMaybeX ctx -> is_aggregation_ctx_s1 ctx
  | NNotX ctx -> is_aggregation_ctx_s1 ctx

let rec is_aggregated_focus = function
  | AtS1 (_, ctx) -> is_aggregated_ctx_s1 ctx
  | _ -> false
and is_aggregated_ctx_s1 = function
  | AnAggregX _ -> true
  | _ -> false

let is_undef_expr_focus = function
  | AtExpr (Undef _, _) -> true
  | _ -> false
    
let rec is_s1_as_p1_focus = function
  | AtS1 (_,ctx) -> is_s1_as_p1_ctx_s1 ctx
  | _ -> false
and is_s1_as_p1_ctx_s1 = function
  | IsX _ -> true
  | RelX _ -> false
  | TripleX1 _ -> false
  | TripleX2 _ -> false
  | ReturnX _ -> false
  | AnAggregX _ -> false
  | NAndX (_,ctx) -> is_s1_as_p1_ctx_s1 ctx
  | NOrX (_,ctx) -> is_s1_as_p1_ctx_s1 ctx
  | NMaybeX ctx -> is_s1_as_p1_ctx_s1 ctx
  | NNotX ctx -> is_s1_as_p1_ctx_s1 ctx

let id_of_s2 = function
  | An (id, _, _) -> Some id
  | _ -> None
let id_of_s1 = function
  | Det (_,det,_) -> id_of_s2 det
  | AnAggreg (_,id,_,_,_,_) -> Some id
  | _ -> None
let id_of_dim = function
  | Foreach (_,id,_,_,_) -> Some id
let id_of_aggreg = function
  | TheAggreg (_,id,_,_,_,_) -> Some id
let id_of_s = function
  | SExpr (_,id,_,_,_) -> Some id
  | _ -> None
let id_of_focus = function
  | AtS1 (np,ctx) when not (is_s1_as_p1_ctx_s1 ctx) -> id_of_s1 np
  | AtDim (dim,_) -> id_of_dim dim
  | AtAggreg (aggreg,_) -> id_of_aggreg aggreg
  | AtExpr (_, SExprX (id,_,_,_)) -> Some id
  | AtExpr (_, SFilterX (id,_)) -> Some id
  | AtS (s,_) -> id_of_s s
  | _ -> None


(* getting element annotation *)

let rec annot_p1 : 'a elt_p1 -> 'a = function
  | Is (a,np) -> a
  | Type (a,c) -> a
  | Rel (a,p,modif,np) -> a
  | Triple (a,arg,np1,np2) -> a
  | Search (a,constr) -> a
  | Filter (a,constr) -> a
  | And (a,lr) -> a
  | Or (a,lr) -> a
  | Maybe (a,f) -> a
  | Not (a,f) -> a
  | IsThere a -> a
and annot_p1_opt : 'a elt_p1 option -> 'a option = function
  | None -> None
  | Some f -> Some (annot_p1 f)
and annot_s1 = function
  | Det (a,det,rel_opt) -> a
  | AnAggreg (a,id,modif,g,rel_opt,np) -> a
  | NAnd (a,lr) -> a
  | NOr (a,lr) -> a
  | NMaybe (a,f) -> a
  | NNot (a,f) -> a
and annot_dim = function
  | Foreach (a,id,modif,rel_opt,id2) -> a
and annot_aggreg = function
  | TheAggreg (a,id,modif,g,rel_opt,id2) -> a
and annot_expr = function
  | Undef a -> a
  | Const (a,t) -> a
  | Var (a,id) -> a
  | Apply (a,func,lr) -> a
and annot_s = function
  | Return (a,np) -> a
  | SAggreg (a,dims,aggregs) -> a
  | SExpr (a,id,modif,expr,rel_opt) -> a
  | SFilter (a,id,expr) -> a
  | Seq (a,lr) -> a

    
(* extraction of LISQL s element from focus *)

let rec elt_s_of_ctx_p1 (f : unit elt_p1) = function
  | DetThatX (det,ctx) -> elt_s_of_ctx_s1 (Det ((), det, Some f)) ctx
  | AnAggregThatX (id,modif,g,np,ctx) -> elt_s_of_ctx_s1 (AnAggreg ((), id, modif, g, Some f, np)) ctx
  | ForeachThatX (id,modif,id2,ctx) -> elt_s_of_ctx_dim (Foreach ((), id, modif, Some f, id2)) ctx
  | TheAggregThatX (id,modif,g,id2,ctx) -> elt_s_of_ctx_aggreg (TheAggreg ((), id, modif, g, Some f, id2)) ctx
  | SExprThatX (id,modif,expr,ctx) -> elt_s_of_ctx_s (SExpr ((), id, modif, expr, Some f)) ctx
  | AndX (ll_rr,ctx) -> elt_s_of_ctx_p1 (And ((), list_of_ctx f ll_rr)) ctx
  | OrX (ll_rr,ctx) -> elt_s_of_ctx_p1 (Or ((), list_of_ctx f ll_rr)) ctx
  | MaybeX ctx -> elt_s_of_ctx_p1 (Maybe ((),f)) ctx
  | NotX ctx -> elt_s_of_ctx_p1 (Not ((),f)) ctx
and elt_s_of_ctx_s1 (f : unit elt_s1) = function
  | IsX ctx -> elt_s_of_ctx_p1 (Is ((),f)) ctx
  | RelX (p,modif,ctx) -> elt_s_of_ctx_p1 (Rel ((),p,modif,f)) ctx
  | TripleX1 (arg,np,ctx) -> elt_s_of_ctx_p1 (Triple ((),arg,f,np)) ctx
  | TripleX2 (arg,np,ctx) -> elt_s_of_ctx_p1 (Triple ((),arg,np,f)) ctx
  | ReturnX ctx -> elt_s_of_ctx_s (Return ((),f)) ctx
  | AnAggregX (id,modif,g,rel_opt,ctx) -> elt_s_of_ctx_s1 (AnAggreg ((),id, modif, g, rel_opt, f)) ctx
  | NAndX (ll_rr,ctx) -> elt_s_of_ctx_s1 (NAnd ((),list_of_ctx f ll_rr)) ctx
  | NOrX (ll_rr,ctx) -> elt_s_of_ctx_s1 (NOr ((),list_of_ctx f ll_rr)) ctx
  | NMaybeX ctx -> elt_s_of_ctx_s1 (NMaybe ((),f)) ctx
  | NNotX ctx -> elt_s_of_ctx_s1 (NNot ((),f)) ctx
and elt_s_of_ctx_dim (f : unit elt_dim) = function
  | SAggregForeachX (ll_rr,aggregs,ctx) -> elt_s_of_ctx_s (SAggreg ((), list_of_ctx f ll_rr, aggregs)) ctx
and elt_s_of_ctx_aggreg (f : unit elt_aggreg) = function
  | SAggregX (dims,ll_rr,ctx) -> elt_s_of_ctx_s (SAggreg ((), dims, list_of_ctx f ll_rr)) ctx
and elt_s_of_ctx_expr (f : unit elt_expr) = function
  | SExprX (id,modif,rel_opt,ctx) -> elt_s_of_ctx_s (SExpr ((), id, modif, f, rel_opt)) ctx
  | SFilterX (id,ctx) -> elt_s_of_ctx_s (SFilter ((), id, f)) ctx
  | ApplyX (func,ll_rr,ctx) -> elt_s_of_ctx_expr (Apply ((), func, list_of_ctx f ll_rr)) ctx
and elt_s_of_ctx_s (f : unit elt_s) = function
  | Root -> f
  | SeqX (ll_rr,ctx) -> elt_s_of_ctx_s (Seq ((), list_of_ctx f ll_rr)) ctx

let elt_s_of_focus = function
  | AtP1 (f,ctx) -> elt_s_of_ctx_p1 f ctx
  | AtS1 (f,ctx) -> elt_s_of_ctx_s1 f ctx
  | AtDim (f,ctx) -> elt_s_of_ctx_dim f ctx
  | AtAggreg (f,ctx) -> elt_s_of_ctx_aggreg f ctx
  | AtExpr (f,ctx) -> elt_s_of_ctx_expr f ctx
  | AtS (f,ctx) -> elt_s_of_ctx_s f ctx


(* focus moves *)

let move_seq move1 move2 = fun focus -> match move1 focus with None -> None | Some focus2 -> move2 focus2
let move_alt move1 move2 = fun focus -> match move1 focus with None -> move2 focus | Some focus2 -> Some focus2
    
let down_p1 (ctx : ctx_p1) : unit elt_p1 -> focus option = function
  | Is (_,np) -> Some (AtS1 (np, IsX ctx))
  | Type _ -> None
  | Rel (_,p,m,np) -> Some (AtS1 (np, RelX (p,m,ctx)))
  | Triple (_,arg,np1,np2) -> Some (AtS1 (np1, TripleX1 (arg,np2,ctx)))
  | Search _ -> None
  | Filter _ -> None
  | And (_,[]) -> None
  | And (_,x::rr) -> Some (AtP1 (x, AndX (([],rr),ctx)))
  | Or (_,[]) -> None
  | Or (_,x::rr) -> Some (AtP1 (x, OrX (([],rr),ctx)))
  | Maybe (_,elt) -> Some (AtP1 (elt, MaybeX ctx))
  | Not (_,elt) -> Some (AtP1 (elt, NotX ctx))
  | IsThere _ -> None
let down_p1_opt (ctx : ctx_p1) : unit elt_p1 option -> focus option = function
  | Some (And (_,x::rr)) -> Some (AtP1 (x, AndX (([],rr), ctx)))
  | Some rel -> Some (AtP1 (rel, ctx))
  | None -> None
let down_s1 (ctx : ctx_s1) : unit elt_s1 -> focus option = function
  | Det (_, det, rel_opt) -> down_p1_opt (DetThatX (det, ctx)) rel_opt
  | AnAggreg (_, id, modif, g, Some rel, np) -> down_p1_opt (AnAggregThatX (id,modif,g,np,ctx)) (Some rel)
  | AnAggreg (_, id, modif, g, None, np) -> Some (AtS1 (np, AnAggregX (id, modif, g, None, ctx)))
  | NAnd (_,[]) -> None
  | NAnd (_,x::rr) -> Some (AtS1 (x, NAndX (([],rr),ctx)))
  | NOr (_,[]) -> None
  | NOr (_,x::rr) -> Some (AtS1 (x, NOrX (([],rr),ctx)))
  | NMaybe (_,elt) -> Some (AtS1 (elt, NMaybeX ctx))
  | NNot (_,elt) -> Some (AtS1 (elt, NNotX ctx))
let down_dim (ctx : ctx_dim) : unit elt_dim -> focus option = function
  | Foreach (_,id,modif,rel_opt,id2) -> down_p1_opt (ForeachThatX (id,modif,id2,ctx)) rel_opt
let down_aggreg (ctx : ctx_aggreg) : unit elt_aggreg -> focus option = function
  | TheAggreg (_,id,modif,g,rel_opt,id2) -> down_p1_opt (TheAggregThatX (id,modif,g,id2,ctx)) rel_opt
let down_expr (ctx : ctx_expr) : unit elt_expr -> focus option = function
  | Undef _ -> None
  | Const _ -> None
  | Var _ -> None
  | Apply (_,func,[]) -> None
  | Apply (_,func,arg::args) -> Some (AtExpr (arg, ApplyX (func, ([],args), ctx)))
let down_s (ctx : ctx_s) : unit elt_s -> focus option = function
  | Return (_,np) -> Some (AtS1 (np,ReturnX ctx))
  | SAggreg (_,[],[]) -> None
  | SAggreg (_,[],aggreg::aggregs) -> Some (AtAggreg (aggreg, SAggregX ([], ([],aggregs), ctx)))
  | SAggreg (_,dim::dims,aggregs) -> Some (AtDim (dim, SAggregForeachX (([],dims),aggregs,ctx)))
  | SExpr (_,id,modif,expr,rel_opt) -> Some (AtExpr (expr, SExprX (id,modif,rel_opt,ctx)))
  | SFilter (_,id,expr) -> Some (AtExpr (expr, SFilterX (id,ctx)))
  | Seq (_,[]) -> None
  | Seq (_,x::rr) -> Some (AtS (x, SeqX (([],rr),ctx)))
let down_focus = function
  | AtP1 (f,ctx) -> down_p1 ctx f
  | AtS1 (f,ctx) -> down_s1 ctx f
  | AtDim (f,ctx) -> down_dim ctx f
  | AtAggreg (f,ctx) -> down_aggreg ctx f
  | AtExpr (f,ctx) -> down_expr ctx f
  | AtS (f,ctx) -> down_s ctx f

let rec up_p1 f = function
  | DetThatX (det,ctx) -> Some (AtS1 (Det ((), det, Some f), ctx))
  | AnAggregThatX (id, modif, g, np, ctx) -> Some (AtS1 (AnAggreg ((), id, modif, g, Some f, np), ctx))
  | ForeachThatX (id,modif,id2,ctx) -> Some (AtDim (Foreach ((), id, modif, Some f, id2), ctx))
  | TheAggregThatX (id,modif,g,id2,ctx) -> Some (AtAggreg (TheAggreg ((), id,modif,g,Some f,id2), ctx))
  | SExprThatX (id,modif,expr,ctx) -> Some (AtS (SExpr ((), id, modif, expr, Some f), ctx))
  | AndX (ll_rr,ctx) -> up_p1 (And ((), list_of_ctx f ll_rr)) ctx (* Some (AtP1 (And ar, ctx)) *)
  | OrX (ll_rr,ctx) -> Some (AtP1 (Or ((), list_of_ctx f ll_rr), ctx))
  | MaybeX ctx -> Some (AtP1 (Maybe ((), f), ctx))
  | NotX ctx -> Some (AtP1 (Not ((), f), ctx))
let rec up_s1 f = function
  | IsX ctx -> Some (AtP1 (Is ((), f), ctx))
  | RelX (p,m,ctx) -> Some (AtP1 (Rel ((),p,m,f), ctx))
  | TripleX1 (arg,np,ctx) -> Some (AtP1 (Triple ((),arg,f,np), ctx))
  | TripleX2 (arg,np,ctx) -> Some (AtP1 (Triple ((),arg,np,f), ctx))
  | ReturnX ctx -> Some (AtS (Return ((),f), ctx))
  | AnAggregX (id, modif, g, rel_opt, ctx) -> Some (AtS1 (AnAggreg ((), id, modif, g, rel_opt, f), ctx))
  | NAndX (ll_rr,ctx) -> up_s1 (NAnd ((), list_of_ctx f ll_rr)) ctx
  | NOrX (ll_rr,ctx) -> Some (AtS1 (NOr ((), list_of_ctx f ll_rr), ctx))
  | NMaybeX ctx -> Some (AtS1 (NMaybe ((),f), ctx))
  | NNotX ctx -> Some (AtS1 (NNot ((),f), ctx))
let up_dim f = function
  | SAggregForeachX (ll_rr,aggregs,ctx) -> Some (AtS (SAggreg ((), list_of_ctx f ll_rr, aggregs), ctx))
let up_aggreg f = function
  | SAggregX (dims,ll_rr,ctx) -> Some (AtS (SAggreg ((), dims, list_of_ctx f ll_rr), ctx))
let up_expr f = function
  | SExprX (id,modif,rel_opt,ctx) -> Some (AtS (SExpr ((), id, modif, f, rel_opt), ctx))
  | SFilterX (id,ctx) -> Some (AtS (SFilter ((), id, f), ctx))
  | ApplyX (func,ll_rr,ctx) -> Some (AtExpr (Apply ((), func, list_of_ctx f ll_rr), ctx))
let up_s f = function
  | Root -> None
  | SeqX (ll_rr,ctx) -> Some (AtS (Seq ((), list_of_ctx f ll_rr), ctx))
let up_focus = function
  | AtP1 (f,ctx) -> up_p1 f ctx
  | AtS1 (f,ctx) -> up_s1 f ctx
  | AtDim (f,ctx) -> up_dim f ctx
  | AtAggreg (f,ctx) -> up_aggreg f ctx
  | AtExpr (f,ctx) -> up_expr f ctx
  | AtS (f,ctx) -> up_s f ctx

let right_p1 (f : unit elt_p1) : ctx_p1 -> focus option = function
  | DetThatX (det,ctx) -> None
  | AnAggregThatX (id, modif, g, np, ctx) -> Some (AtS1 (np, AnAggregX (id, modif, g, Some f, ctx)))
  | ForeachThatX (id,modif,id2,ctx) -> None
  | TheAggregThatX (id,modif,g,id2,ctx) -> None
  | SExprThatX (id,modif,expr,ctx) -> None
  | AndX ((ll,[]),ctx) -> None
  | AndX ((ll,x::rr),ctx) -> Some (AtP1 (x, AndX ((f::ll,rr),ctx)))
  | OrX ((ll,[]),ctx) -> None
  | OrX ((ll,x::rr),ctx) -> Some (AtP1 (x, OrX ((f::ll,rr),ctx)))
  | MaybeX ctx -> None
  | NotX ctx -> None
let right_s1 (f : unit elt_s1) : ctx_s1 -> focus option = function
  | IsX _ -> None
  | RelX _ -> None
  | TripleX1 (arg,np,ctx) -> Some (AtS1 (np, TripleX2 (arg,f,ctx)))
  | TripleX2 _ -> None
  | ReturnX _ -> None
  | AnAggregX _ -> None
  | NAndX ((ll,[]),ctx) -> None
  | NAndX ((ll,x::rr),ctx) -> Some (AtS1 (x, NAndX ((f::ll,rr),ctx)))
  | NOrX ((ll,[]),ctx) -> None
  | NOrX ((ll,x::rr),ctx) -> Some (AtS1 (x, NOrX ((f::ll,rr),ctx)))
  | NMaybeX ctx -> None
  | NNotX ctx -> None
let right_dim (f : unit elt_dim) : ctx_dim -> focus option = function
  | SAggregForeachX ((ll,[]),[],ctx) -> None
  | SAggregForeachX ((ll,[]),aggreg::aggregs,ctx) -> Some (AtAggreg (aggreg, SAggregX (List.rev ll, ([],aggregs), ctx)))
  | SAggregForeachX ((ll,x::rr),aggregs,ctx) -> Some (AtDim (x, SAggregForeachX ((f::ll,rr),aggregs,ctx)))
let right_aggreg (f : unit elt_aggreg) : ctx_aggreg -> focus option = function
  | SAggregX (dims, (ll,[]), ctx) -> None
  | SAggregX (dims, (ll,x::rr), ctx) -> Some (AtAggreg (x, SAggregX (dims, (f::ll,rr), ctx)))
let right_expr (f : unit elt_expr) : ctx_expr -> focus option = function
  | SExprX (id,modif,None,ctx) -> None
  | SExprX (id,modif,Some rel,ctx) -> Some (AtP1 (rel, SExprThatX (id,modif,f,ctx)))
  | SFilterX (id,ctx) -> None
  | ApplyX (func,(ll,[]),ctx) -> None
  | ApplyX (func,(ll,x::rr),ctx) -> Some (AtExpr (x, ApplyX (func, (f::ll,rr), ctx)))
let right_s (f : unit elt_s) : ctx_s -> focus option = function
  | Root -> None
  | SeqX ((ll,[]),ctx) -> None
  | SeqX ((ll,x::rr),ctx) -> Some (AtS (x, SeqX ((f::ll,rr),ctx)))
let right_focus = function
  | AtP1 (f,ctx) -> right_p1 f ctx
  | AtS1 (f,ctx) -> right_s1 f ctx
  | AtDim (f,ctx) -> right_dim f ctx
  | AtAggreg (f,ctx) -> right_aggreg f ctx
  | AtExpr (f,ctx) -> right_expr f ctx
  | AtS (f,ctx) -> right_s f ctx

let left_p1 (f : unit elt_p1) : ctx_p1 -> focus option = function
  | DetThatX (det,ctx) -> None
  | AnAggregThatX _ -> None
  | ForeachThatX _ -> None
  | TheAggregThatX _ -> None
  | SExprThatX (id,modif,expr,ctx) -> Some (AtExpr (expr, SExprX (id, modif, Some f, ctx)))
  | AndX (([],rr),ctx) -> None
  | AndX ((x::ll,rr),ctx) -> Some (AtP1 (x, AndX ((ll,f::rr),ctx)))
  | OrX (([],rr),ctx) -> None
  | OrX ((x::ll,rr),ctx) -> Some (AtP1 (x, OrX ((ll,f::rr),ctx)))
  | MaybeX ctx -> None
  | NotX ctx -> None
let left_s1 (f : unit elt_s1) : ctx_s1 -> focus option = function
  | IsX _ -> None
  | RelX _ -> None
  | TripleX1 _ -> None
  | TripleX2 (arg,np,ctx) -> Some (AtS1 (np, TripleX1 (arg,f,ctx)))
  | ReturnX _ -> None
  | AnAggregX (id, modif, g, None, ctx) -> None
  | AnAggregX (id, modif, g, Some rel, ctx) -> Some (AtP1 (rel, AnAggregThatX (id, modif, g, f, ctx)))
  | NAndX (([],rr),ctx) -> None
  | NAndX ((x::ll,rr),ctx) -> Some (AtS1 (x, NAndX ((ll,f::rr),ctx)))
  | NOrX (([],rr),ctx) -> None
  | NOrX ((x::ll,rr),ctx) -> Some (AtS1 (x, NOrX ((ll,f::rr),ctx)))
  | NMaybeX ctx -> None
  | NNotX ctx -> None
let left_dim (f : unit elt_dim) : ctx_dim -> focus option = function
  | SAggregForeachX (([],rr),aggregs,ctx) -> None
  | SAggregForeachX ((x::ll,rr),aggregs,ctx) -> Some (AtDim (x, SAggregForeachX ((ll,f::rr),aggregs,ctx)))
let left_aggreg (f : unit elt_aggreg) : ctx_aggreg -> focus option = function
  | SAggregX (dims, ([],rr), ctx) ->
    ( match List.rev dims with
    | [] -> None
    | x::ll_dims -> Some (AtDim (x, SAggregForeachX ((ll_dims,[]), f::rr, ctx))) )
  | SAggregX (dims, (x::ll,rr), ctx) -> Some (AtAggreg (x, SAggregX (dims, (ll,f::rr), ctx)))
let left_expr (f : unit elt_expr) : ctx_expr -> focus option = function
  | SExprX (id,modif,rel_opt,ctx) -> None
  | SFilterX (id,ctx) -> None
  | ApplyX (func, ([],rr), ctx) -> None
  | ApplyX (func, (x::ll,rr), ctx) -> Some (AtExpr (x, ApplyX (func, (ll,f::rr), ctx)))
let left_s (f : unit elt_s) : ctx_s -> focus option = function
  | Root -> None
  | SeqX (([],rr),ctx) -> None
  | SeqX ((x::ll,rr),ctx) -> Some (AtS (x, SeqX ((ll,f::rr),ctx)))
let left_focus = function
  | AtP1 (f,ctx) -> left_p1 f ctx
  | AtS1 (f,ctx) -> left_s1 f ctx
  | AtDim (f,ctx) -> left_dim f ctx
  | AtAggreg (f,ctx) -> left_aggreg f ctx
  | AtExpr (f,ctx) -> left_expr f ctx
  | AtS (f,ctx) -> left_s f ctx

(* move to next undef expr if any, or to the context of the whole expr otherwise *)
let rec next_undef_focus focus =
  match focus with
  | AtExpr (expr, ctx) ->
    ( match expr with
    | Undef _ -> Some focus
    | Const _ -> move_seq up_focus next_undef_focus focus
    | Var _ -> move_seq up_focus next_undef_focus focus
    | Apply (_,func,args) ->
      ( try
	  let x, ll_rr =
	    List.find (* if some argument is Undef *)
	      (function (Undef _, ll_rr) -> true | _ -> false)
	      (ctx_of_list args) in
	  Some (AtExpr (x, ApplyX (func,ll_rr,ctx))) (* set focus on it *)
	with _ -> move_seq up_focus next_undef_focus focus ) )
  | AtS (SExpr _,_) -> down_focus focus
  | AtS (SFilter _,_) -> down_focus focus
  | _ -> Some focus


let rec focus_moves (steps : (focus -> focus option) list) (foc : focus) : focus = (* makes as many steps as possible *)
  match steps with
    | [] -> foc
    | step::others ->
      ( match step foc with
	| None -> foc
	| Some foc' -> focus_moves others foc' )

let rec focus_opt_moves (steps : (focus -> focus option) list) (foc_opt : focus option) : focus option = (* makes as many steps as possible *)
  match foc_opt with
  | None -> None
  | Some foc -> Some (focus_moves steps foc)

(* increments *)

type input_type =  [`IRI | `String | `Float | `Integer | `Date | `Time | `DateTime]
(* a sub-type of Sparql.datatype *)

type increment =
  | IncrInput of string * input_type
  | IncrTerm of Rdf.term
  | IncrId of id
  | IncrIs
  | IncrTriple of arg
  | IncrType of Rdf.uri
  | IncrRel of Rdf.uri * modif_p2
  | IncrTriplify
  | IncrAnd
  | IncrOr
  | IncrMaybe
  | IncrNot
  | IncrUnselect
  | IncrOrder of order
  | IncrAggreg of aggreg
  | IncrForeach of id
  (*  | IncrAggregId of aggreg * id *)
  | IncrFuncArg of bool (* is_pred *) * func * int (* arity *) * int (* arg position, starting at 1 *)

      
let check_input s = function
  | `IRI -> true
  | `String -> true
  | `Float -> Regexp.string_match (Regexp.regexp "[-+]?\\d+([.]\\d*)?([eE][-+]?\\d+)?$") s 0 <> None
  (*  | `Decimal -> Regexp.string_match (Regexp.regexp "[-+]?\\d+([.]\\d* )?$") s 0 <> None *)
  | `Integer -> Regexp.string_match (Regexp.regexp "[-+]?\\d+$") s 0 <> None
  | `Date -> Regexp.string_match (Regexp.regexp "[-+]?\\d+-\\d{2}-\\d{2}$") s 0 <> None
  | `Time -> Regexp.string_match (Regexp.regexp "\\d{2}:\\d{2}:\\d{2}(Z|[-+]\\d{2}(:\\d{2})?)?$") s 0 <> None
  | `DateTime -> Regexp.string_match (Regexp.regexp "[-+]?\\d+-\\d{2}-\\d{2}T\\d{2}:\\d{2}:\\d{2}(Z|[-+]\\d{2}(:\\d{2})?)?$") s 0 <> None

let datatype_of_input_type = function
  | `IRI -> invalid_arg "datatype_of_input_type: URI has no datatype"
  | `String -> Rdf.xsd_string
  | `Float -> Rdf.xsd_double
  | `Integer -> Rdf.xsd_integer
  | `Date -> Rdf.xsd_date
  | `Time -> Rdf.xsd_time
  | `DateTime -> Rdf.xsd_dateTime
let term_of_input s = function
  | `IRI -> Rdf.URI s
  | typ -> Rdf.TypedLiteral (s, datatype_of_input_type typ)

let term_of_increment : increment -> Rdf.term option = function
  | IncrInput (s,dt) -> Some (term_of_input s dt)
  | IncrTerm t -> Some t
  | IncrType c -> Some (Rdf.URI c)
  | IncrRel (p,m) -> Some (Rdf.URI p)
  | _ -> None

let append_and_p1 ctx (elt_p1 : unit elt_p1) = function
  | IsThere _ -> AtP1 (elt_p1, ctx)
  | And (_,lr) -> AtP1 (elt_p1, AndX ((List.rev lr, []), ctx))
  | p1 -> AtP1 (elt_p1, AndX (([p1], []), ctx))
let append_or_p1 ctx (elt_p1 : unit elt_p1) = function
  | Or (_,lr) -> AtP1 (elt_p1, OrX ((List.rev lr, []), ctx))
  | p1 -> AtP1 (elt_p1, OrX (([p1], []), ctx))

let append_and_s1 ctx (elt_s1 : unit elt_s1) = function
  | NAnd (_,lr) -> AtS1 (elt_s1, NAndX ((List.rev lr, []), ctx))
  | s1 -> AtS1 (elt_s1, NAndX (([s1], []), ctx))
let append_or_s1 ctx (elt_s1 : unit elt_s1) = function
  | NOr (_,lr) -> AtS1 (elt_s1, NOrX ((List.rev lr, []), ctx))
  | s1 -> AtS1 (elt_s1, NOrX (([s1], []), ctx))

let append_seq_s ctx (elt_s : unit elt_s) = function
  | Seq (_,lr) -> AtS (elt_s, SeqX ((List.rev lr, []), ctx))
  | s -> AtS (elt_s, SeqX (([s], []), ctx))

let insert_elt_p1_in_rel_opt ctx elt = function
  | None -> Some (AtP1 (elt, ctx))
  | Some rel -> Some (append_and_p1 ctx elt rel)
    
let insert_elt_p1 (elt : unit elt_p1) = function
  | AtP1 (f, AndX ((ll,rr),ctx)) -> Some (AtP1 (elt, AndX ((f::ll,rr),ctx)))
  | AtP1 (f, ctx) -> Some (append_and_p1 ctx elt f)
  | AtS1 (Det (_, det, rel_opt), ctx) -> insert_elt_p1_in_rel_opt (DetThatX (det,ctx)) elt rel_opt
  | AtS1 (AnAggreg (_, id, modif, g, rel_opt, np), ctx) -> insert_elt_p1_in_rel_opt (AnAggregThatX (id,modif,g,np,ctx)) elt rel_opt
  | AtS1 _ -> None (* no insertion of increments on complex NPs *)
  | AtDim (Foreach (_,id,modif,rel_opt,id2), ctx) -> insert_elt_p1_in_rel_opt (ForeachThatX (id,modif,id2,ctx)) elt rel_opt
  | AtAggreg (TheAggreg (_,id,modif,g,rel_opt,id2), ctx) -> insert_elt_p1_in_rel_opt (TheAggregThatX (id,modif,g,id2,ctx)) elt rel_opt
  | AtExpr (expr, SExprX (id,modif,rel_opt,ctx)) -> insert_elt_p1_in_rel_opt (SExprThatX (id,modif,expr,ctx)) elt rel_opt
  | AtExpr _ -> None (* no insertion inside expressions *)
  | AtS _ -> None

let insert_elt_s2 det focus =
  let focus2_opt =
    match focus with
    | AtP1 _
    | AtDim _
    | AtAggreg _ -> insert_elt_p1 (Is ((), Det ((), det, None))) focus
    | AtS1 (Det (_, det2, rel_opt), ctx) ->
      if det2 = det
      then Some (AtS1 (Det ((), factory#top_s2, rel_opt), ctx))
      else Some (AtS1 (Det ((), det, rel_opt), ctx))
    | AtS1 (AnAggreg (_,id,modif,g,_,np), ctx) ->
      Some (AtS1 (AnAggreg ((), id, modif, g, Some (Is ((), Det ((), det, None))), np), ctx))
    | AtS1 _ -> None (* no insertion of terms on complex NPs *)
    | _ -> None in
  match focus2_opt with
  | Some (AtS1 (f, RelX (p, m, ctx))) -> Some (AtP1 (Rel ((),p,m,f), ctx))
  | Some (AtS1 (f, TripleX1 (arg,np,ctx))) -> Some (AtP1 (Triple ((),arg,f,np), ctx))
  | Some (AtS1 (f, TripleX2 (arg,np,ctx))) -> Some (AtP1 (Triple ((),arg,np,f), ctx))
  | other -> other

let insert_input s typ focus =
  match focus with
  | AtExpr (_,ctx) -> next_undef_focus (AtExpr (Const ((), term_of_input s typ), ctx))
  | _ -> None

let insert_term t focus =
  match t with
    | Rdf.Bnode _ -> None (* blank nodes cannot be injected in queries *)
    | _ ->
      match focus with
      | AtExpr (_,ctx) -> next_undef_focus (AtExpr (Const ((),t),ctx))
      | _ -> insert_elt_s2 (Term t) focus
let insert_id id = function
  | AtExpr (_,ctx) -> next_undef_focus (AtExpr (Var ((),id),ctx))
  | focus -> insert_elt_s2 (The id) focus

let insert_type c = function
  | AtS1 (Det (_,det,rel_opt), ctx) ->
    ( match det with
      | Term _ ->
	Some (AtS1 (Det ((), An (factory#new_id, factory#top_modif, Class c), rel_opt), ctx))
      | An (id, modif, Thing) ->
	Some (AtS1 (Det ((), An (id, modif, Class c), rel_opt), ctx))
      | An (id, modif, Class c2) when c2 = c ->
	Some (AtS1 (Det ((), An (id, modif, Thing), rel_opt), ctx))
      | _ ->
	let rel = match rel_opt with None -> IsThere () | Some rel -> rel in
	insert_elt_p1 (Type ((),c)) (AtP1 (rel, DetThatX (det, ctx))) )
  | focus -> insert_elt_p1 (Type ((),c)) focus

let insert_rel p m focus =
  let foc_opt = insert_elt_p1 (Rel ((), p, m, factory#top_s1)) focus in
  focus_opt_moves [down_focus] foc_opt

let insert_triple arg focus =
  let foc_opt = insert_elt_p1 (Triple ((), arg, factory#top_s1, factory#top_s1)) focus in
  let steps = if arg = S then [down_focus; right_focus] else [down_focus] in
  focus_opt_moves steps foc_opt

let insert_triplify = function
  | AtP1 (Rel (_, p, Fwd, np), ctx) -> Some (AtS1 (Det ((), Term (Rdf.URI p), None), TripleX1 (S, np, ctx)))
  | AtP1 (Rel (_, p, Bwd, np), ctx) -> Some (AtS1 (Det ((), Term (Rdf.URI p), None), TripleX2 (O, np, ctx)))
  | AtP1 (Triple (_, S, Det ((), Term (Rdf.URI p), _), np), ctx) -> Some (AtP1 (Rel ((), p, Fwd, np), ctx))
  | AtP1 (Triple (_, O, np, Det ((), Term (Rdf.URI p), _)), ctx) -> Some (AtP1 (Rel ((), p, Bwd, np), ctx))
  | _ -> None

let insert_constr constr focus =
  match focus with
    | AtS1 (f, ReturnX _) when is_top_s1 f -> insert_elt_p1 (Search ((),constr)) focus
    | _ -> insert_elt_p1 (Filter ((),constr)) focus

let insert_is = function
  | AtS1 (f, IsX ctx) when is_top_s1 f -> None
  | focus ->
    let foc_opt = insert_elt_p1 (Is ((),factory#top_s1)) focus in
    focus_opt_moves [down_focus] foc_opt

let insert_and = function
(*
  | AtP1 (And ar, ctx) -> Some (append_and_p1 ctx IsThere (And ar))
  | AtP1 (f, AndX (i,ar,ctx)) when not (is_top_p1 f) -> ar.(i) <- f; Some (append_and_p1 ctx IsThere (And ar))
  | AtP1 (f, ctx) when not (is_top_p1 f) -> Some (append_and_p1 ctx IsThere f)
*)
  | AtP1 _ -> None (* P1 conjunction is implicit *)
  | AtS1 (f, ReturnX ctx) -> Some (AtS1 (factory#top_s1, ReturnX (SeqX (([Return ((),f)],[]), ctx))))
  | AtS1 (f, NAndX ((ll,rr),ctx)) when not (is_s1_as_p1_ctx_s1 ctx && is_top_s1 f) -> Some (AtS1 (factory#top_s1, NAndX ((f::ll,rr),ctx)))
  | AtS1 (f, ctx) when not (is_s1_as_p1_ctx_s1 ctx && is_top_s1 f) -> Some (append_and_s1 ctx factory#top_s1 f)
  | _ -> None

let insert_or = function
  | AtP1 (f, OrX ((ll,rr),ctx2)) when not (is_top_p1 f) -> Some (AtP1 (IsThere (), OrX ((f::ll,rr),ctx2)))
  | AtP1 (f, ctx) when not (is_top_p1 f) -> Some (append_or_p1 ctx (IsThere ()) f)
  | AtS1 (f, NOrX ((ll,rr),ctx2)) when not (is_top_s1 f) -> Some (AtS1 (factory#top_s1, NOrX ((f::ll,rr),ctx2)))
  | AtS1 (f, ctx) when not (is_top_s1 f) -> Some (append_or_s1 ctx factory#top_s1 f)
  | _ -> None

let insert_maybe = function
  | AtP1 (Maybe (_,f), ctx) -> Some (AtP1 (f,ctx))
  | AtP1 (_, MaybeX ctx) -> None
  | AtP1 (Not _, ctx) -> None
  | AtP1 (_, NotX ctx) -> None				     
  | AtP1 (f, ctx) when not (is_top_p1 f) -> Some (AtP1 (Maybe ((),f), ctx))
  (*if is_top_p1 f then Some (AtP1 (f, MaybeX ctx)) else Some (AtP1 (Maybe f, ctx))*)
  | AtS1 (NMaybe (_,f), ctx) -> Some (AtS1 (f,ctx))
  | AtS1 (_, NMaybeX ctx) -> None
  | AtS1 (NNot _, ctx) -> None
  | AtS1 (_, NNotX ctx) -> None
  | AtS1 (_, ReturnX _) -> None
  | AtS1 (f, ctx) when not (is_aggregated_ctx_s1 ctx || is_s1_as_p1_ctx_s1 ctx && is_top_s1 f) -> Some (AtS1 (NMaybe ((),f), ctx))
  (*if is_top_s1 f then Some (AtS1 (f, NMaybeX ctx)) else Some (AtS1 (NMaybe f, ctx))*)
  | _ -> None

let insert_not = function
  | AtP1 (Not (_,f), ctx) -> Some (AtP1 (f,ctx))
  | AtP1 (_, NotX ctx) -> None
  | AtP1 (Maybe _, ctx) -> None
  | AtP1 (_, MaybeX ctx) -> None
  | AtP1 (f, ctx) ->
    if is_top_p1 f then Some (AtP1 (f, NotX ctx)) else Some (AtP1 (Not ((),f), ctx))
  | AtS1 (NNot (_,f), ctx) -> Some (AtS1 (f,ctx))
  | AtS1 (_, NNotX ctx) -> None
  | AtS1 (NMaybe _, ctx) -> None
  | AtS1 (_, NMaybeX ctx) -> None
  | AtS1 (_, ReturnX ctx) -> None
  | AtS1 (f, ctx) when not (is_aggregated_ctx_s1 ctx || is_s1_as_p1_ctx_s1 ctx && is_top_s1 f) ->
    if is_top_s1 f then Some (AtS1 (f, NNotX ctx)) else Some (AtS1 (NNot ((),f), ctx))
  | _ -> None

let insert_seq = function
  | AtS (f, SeqX ((ll,rr),ctx2)) -> Some (AtS (factory#top_s, SeqX ((f::ll,rr),ctx2)))
  | AtS (f, ctx) -> Some (append_seq_s ctx factory#top_s f)
  | _ -> None

let out_of_unselect modif foc =
  match fst modif with
  | Unselect -> up_focus foc (* to enforce hidden column *)
  | Select -> Some foc

let insert_modif_transf f = function
  | AtS1 (Det (_, An (id, modif, head), rel_opt), ctx) when not (is_s1_as_p1_ctx_s1 ctx) ->
    let modif2 = f modif in
    let foc2 = AtS1 (Det ((), An (id, modif2, head), rel_opt), ctx) in
    out_of_unselect modif2 foc2
  | AtS1 (AnAggreg (_, id, modif, g, rel_opt, np), ctx) ->
    let modif2 = f modif in
    let foc2 = AtS1 (AnAggreg ((), id, modif2, g, rel_opt, np), ctx) in
    out_of_unselect modif2 foc2
  | AtDim (Foreach (_,id,modif,rel_opt,id2), ctx) ->
    let modif2 = f modif in
    if fst modif2 = Unselect
    then None (* hidding dimensions is not allowed *)
    else Some (AtDim (Foreach ((),id,modif2,rel_opt,id2), ctx))
  | AtAggreg (TheAggreg (_,id,modif,g,rel_opt,id2), ctx) ->
    let modif2 = f modif in
    let foc2 = AtAggreg (TheAggreg ((),id,modif2,g,rel_opt,id2), ctx) in
    out_of_unselect modif2 foc2
  | AtExpr (expr, SExprX (id,modif,rel_opt,ctx)) ->
    let modif2 = f modif in
    if fst modif2 = Unselect
    then None (* hidding expressions is not allowed *)
    else Some (AtExpr (expr, SExprX (id,modif2,rel_opt,ctx)))
  | AtS (SExpr (_,id,modif,expr,rel_opt),ctx) ->
    let modif2 = f modif in
    if fst modif2 = Unselect
    then None  (* hidding expressions is not allowed *)
    else Some (AtS (SExpr ((), id, modif2, expr, rel_opt), ctx))
  | _ -> None

let insert_aggreg g = function
  | AtS1 (np, AnAggregX (id,modif,g0,_,ctx)) when g0 <> g ->
    Some (AtS1 (AnAggreg ((), id, factory#top_modif, g, None, np), ctx))
  | AtS1 (Det (_, An _, _) as np, ctx) when not (is_s1_as_p1_ctx_s1 ctx) ->
    Some (AtS1 (AnAggreg ((), factory#new_id, factory#top_modif, g, None, np), ctx))
  | AtS1 ((AnAggreg (_, id, modif, g0, rel_opt, np) as npg), ctx) ->
    if g0 = g then Some (AtS1 (np, ctx))
    else Some (AtS1 (AnAggreg ((), factory#new_id, factory#top_modif, g, None, npg), ctx))
  | AtS1 (np, AnAggregX (_,_,g0,_,ctx)) when g0 = g ->
    Some (AtS1 (np,ctx))
  | _ -> None

let insert_aggreg_bis g focus =
  match id_of_focus focus with
  | None -> None
  | Some id2 ->
    let s = elt_s_of_focus focus in
    let focus2 = append_seq_s Root (SAggreg ((), [], [TheAggreg ((), factory#new_id, factory#top_modif, g, None, id2)])) s in
    down_focus focus2

let insert_foreach id2 = function
  | AtS (SAggreg (_,dims,aggregs), ctx) ->
    Some (AtDim (Foreach ((), factory#new_id, factory#top_modif, None, id2), SAggregForeachX ((List.rev dims, []), aggregs, ctx)))
  | AtDim (dim, SAggregForeachX ((ll,rr), aggregs, ctx)) ->
    Some (AtDim (Foreach ((), factory#new_id, factory#top_modif, None, id2), SAggregForeachX ((dim::ll,rr), aggregs, ctx)))
  | AtAggreg (aggreg, SAggregX (dims, ll_rr, ctx)) ->
    Some (AtDim (Foreach ((), factory#new_id, factory#top_modif, None, id2), SAggregForeachX ((List.rev dims, []), list_of_ctx aggreg ll_rr, ctx)))
  | _ -> None

let insert_aggreg_id g id2 = function
  | AtS (SAggreg (_,dims,aggregs), ctx) ->
    Some (AtAggreg (TheAggreg ((), factory#new_id, factory#top_modif, g, None, id2), SAggregX (dims, (List.rev aggregs, []), ctx)))
  | AtAggreg (aggreg, SAggregX (dims, (ll,rr), ctx)) ->
    Some (AtAggreg (TheAggreg ((), factory#new_id, factory#top_modif, g, None, id2), SAggregX (dims, (aggreg::ll,rr), ctx)))
  | AtDim (dim, SAggregForeachX (ll_rr, aggregs, ctx)) ->
    Some (AtAggreg (TheAggreg ((), factory#new_id, factory#top_modif, g, None, id2), SAggregX (list_of_ctx dim ll_rr, (List.rev aggregs, []), ctx)))
  | _ -> None

let insert_func_arg is_pred func arity pos =
  let ll_rr =
    List.map (fun _ -> factory#top_expr) (Common.from_downto (pos-1) 1),
    List.map (fun _ -> factory#top_expr) (Common.from_to (pos+1) arity) in
  function
  | AtExpr (_, ctx) when arity=0 -> next_undef_focus (AtExpr (Apply ((), func, []), ctx))
  | AtExpr (expr,ctx) when (match ctx with SExprX _ -> not is_pred | _ -> true) ->
    next_undef_focus (AtExpr (Apply ((), func, list_of_ctx expr ll_rr), ctx))
  | focus ->
    ( match id_of_focus focus with
    | None -> None
    | Some id ->
      let s = elt_s_of_focus focus in
      let args = if arity = 0 then [] else list_of_ctx (Var ((),id)) ll_rr in
      let s2 =
	let expr = Apply ((), func, args) in
	if is_pred
	then SFilter ((), factory#new_id, expr)
	else SExpr ((), factory#new_id, factory#top_modif, Apply ((), func, args), None) in
      let focus2 = append_seq_s Root s2 s in
      move_seq down_focus next_undef_focus focus2 )

let insert_increment incr focus =
  match incr with
    | IncrInput (s,dt) -> insert_input s dt focus
    | IncrTerm t -> insert_term t focus
    | IncrId id -> insert_id id focus
    | IncrType c -> insert_type c focus
    | IncrRel (p,m) -> insert_rel p m focus
    | IncrTriple arg -> insert_triple arg focus
    | IncrTriplify -> insert_triplify focus
    | IncrIs -> insert_is focus
    | IncrAnd -> insert_and focus
    | IncrOr -> insert_or focus
    | IncrMaybe -> insert_maybe focus
    | IncrNot -> insert_not focus
    | IncrUnselect ->
      insert_modif_transf
	(function
	  | (Unselect,order) -> Select, order
	  | (_,order) ->  Unselect, order)
	focus
    | IncrOrder order ->
      insert_modif_transf
	(function (proj, order0) ->
	  if order0 = order
	  then proj, Unordered
	  else proj, order)
	focus
    | IncrAggreg g -> insert_aggreg_bis g focus
    | IncrForeach id -> insert_foreach id focus
    (*    | IncrAggregId (g,id) -> insert_aggreg_id g id focus *)
    | IncrFuncArg (is_pred,func,arity,pos) -> insert_func_arg is_pred func arity pos focus

      
let delete_list = function
  | [], [] -> `Empty
  | [x], [] -> `Single x
  | [], [x] -> `Single x
  | x::ll1, rr -> `List (x,ll1,rr)
  | [], x::rr1 -> `List (x,[],rr1)

let rec delete_ctx_p1 = function
  | DetThatX (det,ctx) -> Some (AtS1 (Det ((),det,None), ctx))
  | AnAggregThatX (id,modif,g,np,ctx) -> Some (AtS1 (AnAggreg ((), id, modif, g, None, np), ctx))
  | ForeachThatX (id,modif,id2,ctx) -> Some (AtDim (Foreach ((), id,modif,None,id2), ctx))
  | TheAggregThatX (id,modif,g,id2,ctx) -> Some (AtAggreg (TheAggreg ((), id,modif,g,None,id2), ctx))
  | SExprThatX (id,modif,expr,ctx) -> Some (AtS (SExpr ((), id, modif, expr, None), ctx))
  | AndX (ll_rr,ctx) ->
    ( match delete_list ll_rr with
      | `Empty -> delete_ctx_p1 ctx
      | `Single elt -> Some (AtP1 (elt, ctx))
      | `List (elt,ll2,rr2) -> Some (AtP1 (elt, AndX ((ll2,rr2),ctx))) )
  | OrX (ll_rr,ctx) ->
    ( match delete_list ll_rr with
      | `Empty -> delete_ctx_p1 ctx
      | `Single elt -> Some (AtP1 (elt, ctx))
      | `List (elt,ll2,rr2) -> Some (AtP1 (elt, OrX ((ll2, rr2), ctx))) )
  | MaybeX ctx -> delete_ctx_p1 ctx
  | NotX ctx -> delete_ctx_p1 ctx
and delete_ctx_s1 f_opt ctx =
  match ctx with
    | IsX ctx2
    | RelX (_,_,ctx2)
    | TripleX1 (_,_,ctx2)
    | TripleX2 (_,_,ctx2) ->
      ( match f_opt with
	| None -> delete_ctx_p1 ctx2
	| Some f -> Some (AtS1 (factory#top_s1, ctx)) )
    | ReturnX ctx2 ->
      ( match f_opt with
	| None -> delete_ctx_s ctx2
	| Some f -> Some (AtS1 (factory#top_s1, ctx)) )
    | AnAggregX (id,modif,g,rel_opt,ctx2) -> delete_ctx_s1 f_opt ctx2
    | NAndX (ll_rr,ctx2) ->
      ( match delete_list ll_rr with
	| `Empty -> delete_ctx_s1 None ctx2
	| `Single elt -> Some (AtS1 (elt, ctx2))
	| `List (elt,ll2,rr2) -> Some (AtS1 (elt, NAndX ((ll2,rr2),ctx2))) )
    | NOrX (ll_rr,ctx2) ->
      ( match delete_list ll_rr with
	| `Empty -> delete_ctx_s1 None ctx2
	| `Single elt -> Some (AtS1 (elt, ctx2))
	| `List (elt,ll2,rr2) -> Some (AtS1 (elt, NOrX ((ll2,rr2),ctx2))) )
    | NMaybeX ctx2 -> delete_ctx_s1 f_opt ctx2
    | NNotX ctx2 -> delete_ctx_s1 f_opt ctx2
and delete_ctx_dim ctx =
  match ctx with
  | SAggregForeachX (ll_rr,aggregs,ctx) ->
    ( match delete_list ll_rr with
    | `Empty -> Some (AtS (SAggreg ((), [],aggregs), ctx))
    | `Single elt -> Some (AtDim (elt, SAggregForeachX (([],[]),aggregs,ctx)))
    | `List (elt,ll2,rr2) -> Some (AtDim (elt, SAggregForeachX ((ll2,rr2),aggregs,ctx))) )
and delete_ctx_expr f_opt ctx =
  match ctx with
  | SExprX (id,modif,rel_opt,ctx2) -> delete_ctx_s ctx2
  | SFilterX (id,ctx2) -> delete_ctx_s ctx2
  | ApplyX (func,ll_rr,ctx2) ->
    ( match f_opt with
    | None -> delete_ctx_expr (Some (Apply ((), func, list_of_ctx factory#top_expr ll_rr))) ctx2
    | Some _ -> Some (AtExpr (factory#top_expr, ctx)) )
and delete_ctx_aggreg ctx =
  match ctx with
  | SAggregX (dims,ll_rr,ctx) ->
    ( match delete_list ll_rr with
    | `Empty -> delete_ctx_s ctx (* the list of aggregations should not be empty *)
    | `Single elt -> Some (AtAggreg (elt, SAggregX (dims,([],[]),ctx)))
    | `List (elt,ll2,rr2) -> Some (AtAggreg (elt, SAggregX (dims, (ll2,rr2), ctx))) )
and delete_ctx_s ctx =
  match ctx with
  | Root -> None
  | SeqX (ll_rr,ctx2) ->
    ( match delete_list ll_rr with
    | `Empty -> delete_ctx_s ctx2
    | `Single elt -> Some (AtS (elt,ctx2))
    | `List (elt,ll2,rr2) -> Some (AtS (elt, SeqX ((ll2,rr2),ctx2))) )

let delete_focus = function
  | AtP1 (_, ctx) -> delete_ctx_p1 ctx
  | AtS1 (f, ctx) -> delete_ctx_s1 (if is_top_s1 f then None else Some f) ctx
  | AtDim (f, ctx) -> delete_ctx_dim ctx
  | AtAggreg (f, ctx) -> delete_ctx_aggreg ctx
  | AtExpr (f, ctx) -> delete_ctx_expr (if is_top_expr f then None else Some f) ctx
  | AtS (f, ctx) -> delete_ctx_s ctx

(* goto to query *)

let focus_of_query (s : unit elt_s) = AtS (s, Root)

let goto (s : unit elt_s) focus = Some (focus_of_query s)
