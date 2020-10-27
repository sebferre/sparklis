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

(* translation from LISQL focus to annotated LISQL *)
(* to ensure consistency between lisql2nl and lisql2sparql, and simplify them *)

open Rdf
open Lisql

(* focus description *)

type term_id = [ `Term of Rdf.term | `Id of id ]
       
type focus_term = [ term_id | `Undefined ]
(* [Undefined] means 'does not exists' (e.g., sentence focus) or 'is ambiguous' (e.g., coordinated NP) *)
  
let term_id_s2 : elt_s2 -> term_id = function
  | Term t -> `Term t
  | An (id,_,_) -> `Id id
  | The id -> `Id id

let term_id_s1 : 'a elt_s1 -> term_id option = function
  | Det (_,det,rel_opt) -> Some (term_id_s2 det)
  | AnAggreg (_,id,_,_,_,_) -> Some (`Id id)
  | _ -> None
	       
let focus_term_id : focus_term -> id option = function
  | `Id id -> Some id
  | _ -> None

type focus_graph = [ `Default | `Named of term_id ]

let focus_graph_s2 : elt_s2 -> focus_graph = function
  | Term t -> `Named (`Term t)
  | An (id,_,_) -> `Named (`Id id)
  | The id -> `Named (`Id id)
let focus_graph_s1 : 'a elt_s1 -> focus_graph = function
  | Det (_,det, _) -> focus_graph_s2 det
  | _ -> assert false (* Lisql transformation must prevent this happening *)

type focus_pred_args = [ `Undefined | `PredArgs of pred * (arg * term_id) list ]

let rec focus_pred_args : focus -> focus_pred_args = function
  | AtP1 (Pred (_,arg,pred,cp),ctx) ->
     let args =
       match focus_pred_args_ctx_p1 ctx with
       | None -> []
       | Some x -> (arg,x)::[] in
     `PredArgs (pred,args)
  | AtSn (cp,ctx) -> focus_pred_args_ctx_sn [] ctx
  | AtS1 (np, CConsX1 (arg,cp,ctx)) ->
     let args = match term_id_s1 np with None -> [] | Some ti -> [arg,ti] in
     focus_pred_args_ctx_sn args ctx
  | _ -> `Undefined
and focus_pred_args_ctx_sn (args : (arg * term_id) list) : ctx_sn -> focus_pred_args = function
  | PredX (arg,pred,ctx) ->
     let args =
       match focus_pred_args_ctx_p1 ctx with
       | None -> args
       | Some x -> (arg,x)::args in
     `PredArgs (pred,args)
  | CConsX2 (arg,np,ctx) ->
     let args =
       match term_id_s1 np with
       | None -> args
       | Some z -> (arg,z)::args in
     focus_pred_args_ctx_sn args ctx
  | CAndX (ll_rr,ctx) -> focus_pred_args_ctx_sn args ctx
  | COrX (ll_rr,ctx) -> focus_pred_args_ctx_sn args ctx
  | CNotX ctx -> focus_pred_args_ctx_sn args ctx
  | CMaybeX ctx -> focus_pred_args_ctx_sn args ctx
and focus_pred_args_ctx_p1 : ctx_p1 -> term_id option = function
  | DetThatX (det,ctx) -> Some (term_id_s2 det)
  | AnAggregThatX (id,m,g,np,ctx) -> Some (`Id id)
  | ForEachThatX (id,m,id2,ctx) -> Some (`Id id)
  | TheAggregThatX (id,m,g,id2,ctx) -> Some (`Id id)
  | SExprThatX (name,id,m,expr,ctx) -> Some (`Id id)
  | AndX (ll_rr,ctx) -> focus_pred_args_ctx_p1 ctx
  | OrX (ll_rr,ctx) -> focus_pred_args_ctx_p1 ctx
  | NotX ctx -> focus_pred_args_ctx_p1 ctx
  | MaybeX ctx -> focus_pred_args_ctx_p1 ctx
  | InX (npg,ctx) -> focus_pred_args_ctx_p1 ctx

					    
class focus_descr ~(pred_args : focus_pred_args) =
  object
    val mutable term_opt : [`None | focus_term] = `None
    val mutable graph_aux : [focus_graph | `NamedFocus] = `Default
    val mutable no_incr : bool = false (* whether class/property increments should not be computed *)
    val mutable unconstrained : bool = false (* whether there is no relational constraint on focus *)

    method term : focus_term = match term_opt with `None -> `Undefined | #focus_term as ft -> ft
    method graph : focus_graph = match graph_aux with `NamedFocus -> `Default | #focus_graph as fg -> fg
    method pred_args : focus_pred_args = pred_args
    method incr : bool = not no_incr
    method unconstrained : bool = unconstrained
      
    method define_focus_term (ft : focus_term) : unit =
      match term_opt with
      | `None -> term_opt <- (ft :> [`None | focus_term])
      | _ -> ()

    method define_focus_graph (fg : focus_graph) : unit =
      match graph_aux with
      | `Default -> graph_aux <- (fg :> [focus_graph | `NamedFocus])
      | _ -> ()
    method wait_focus_graph : unit =
      graph_aux <- `NamedFocus
    method resolve_focus_graph (fg : focus_graph) : unit =
      match graph_aux with
      | `NamedFocus -> graph_aux <- (fg :> [focus_graph | `NamedFocus])
      | _ -> ()

    method set_no_incr : unit = no_incr <- true

    method set_unconstrained : unit = unconstrained <- true
  end


(* focus positions *)
    
type focus_pos =
[ `At (* at focus position *)
| `Below (* below current scope *)
| `Above of bool * int option (* above current focus: bool for operator suspension, and int for position of elt containing focus *)
| `Aside of bool (* aside current focus: below for branch suspension *)
]

let focus_pos_down = function
  | `At -> `Below
  | `Below -> `Below
  | `Above (susp,_) -> `Aside false (* one layer of susp is enough *)
  | `Aside susp -> `Aside false (* idem *)

    
(* annotations *)

module Ids = Set.Make(struct type t=id let compare=Stdlib.compare end)

type annot_ids = { seq : id list; all : Ids.t; defs : Ids.t; dims : Ids.t; refs : Ids.t }
  (* seq : all defined ids, in syntactic ordering 
     all : all defined ids, suspended or not
     defs : all defined ids, except suspended ones
     dims : all ids that together define a key over answers 
     refs : all referenced ids *)

let empty_ids = { seq = []; all = Ids.empty; defs = Ids.empty; dims = Ids.empty; refs = Ids.empty }
let concat_ids ids1 ids2 =
  { seq = ids1.seq @ ids2.seq;
    all = Ids.union ids1.all ids2.all;
    defs = Ids.union ids1.defs ids2.defs;
    dims = Ids.union ids1.dims ids2.dims;
    refs = Ids.union ids1.refs ids2.refs }
let list_concat_ids lids = List.fold_right concat_ids lids empty_ids

type sid = int (* sentence id, position in seq list *)
type view =
| Unit
| Atom of annot_ids * sid (* ids, sid *)
| InlineAggregs of annot_ids * sid * Ids.t (* ids, sid, ids2 *)
| Join of annot_ids * view list (* ids, views *)
| Aggreg of annot_ids * sid * view (* ids, sid, aggregated_view *)
type seq_view = sid * view

class annot
  ~focus_pos ?focus
  ?(ids : annot_ids = empty_ids)
  ?(seq_view : seq_view option) ?(defined : bool = false) () =
object (self)
  val focus_pos : focus_pos = focus_pos
  val focus : focus option = focus
  method focus_pos = focus_pos
  method focus = focus

  method ids = ids
    
  method seq_view = seq_view
  method defined = defined
  
  method is_at_focus : bool = (focus_pos = `At)
  method is_susp_focus : bool = match focus_pos with `Above (true,_) | `Aside true -> true | _ -> false
  method get_susp_focus_index : int option = match focus_pos with `Above (true, index_opt) -> index_opt | _ -> None

  method down = {< focus_pos = focus_pos_down focus_pos >}
  method suspended =
    if focus_pos = `Aside false
    then {< focus_pos = `Aside true >}
    else self
end

let dummy_annot = new annot ~focus_pos:(`Aside false) ()
let dummy_s1 = Det (dummy_annot, An (0, (Select, Unordered), Thing), None)

(* cleaning sequences based on dependencies *)

let clean_list a_lr lr =
  let changed, all, rev_lr_clean =
    List.fold_left2
      (fun (changed,all,rev_lr_clean) (a,ay) y ->
	let ids = a#ids in
	let new_all = Ids.union ids.all all in
	if Ids.subset ids.refs new_all
	then (changed,new_all, y::rev_lr_clean)
	else (true,all, rev_lr_clean))
      (false,Ids.empty,[]) a_lr lr in
  if changed
  then `Changed (List.rev rev_lr_clean)
  else `Unchanged

let clean_list_focus (a,a_x) x (a_ll,a_rr) (ll,rr) =
  (* removing sentences that are no more well-defined (maybe introduced by deletions *)
  let changed = false in
  let changed, all, ll =
    List.fold_right2
      (fun (a,ay) y (changed,all, ll) ->
	let ids = a#ids in
	let new_all = Ids.union ids.all all in
	if Ids.subset ids.refs new_all
	then (changed, new_all, y::ll)
	else (true, all, ll))
      a_ll ll (changed, Ids.empty,[]) in
  let changed, all, x_opt =
    let ids = a#ids in
    let new_all = Ids.union ids.all all in
    if Ids.subset ids.refs new_all
    then changed, new_all, Some x
    else true, all, None in
  let changed, all, rev_rr =
    List.fold_left2
      (fun (changed, all,rev_rr) (a,ay) y ->
	let ids = a#ids in
	let new_all = Ids.union ids.all all in
	if Ids.subset ids.refs new_all
	then (changed, new_all, y::rev_rr)
	else (true, all, rev_rr))
      (changed,all,[]) a_rr rr in
  let rr = List.rev rev_rr in
  if changed
  then `Changed
    ( match ll, x_opt, rr with
    | _, Some x, _ -> Some (x, (ll,rr))
    | y::ll1, None, _ -> Some (y, (ll1,rr))
    | [], None, y::rr1 -> Some (y, ([],rr1))
    | [], None, [] -> None)
  else `Unchanged

(* ids and views *)

let view_ids = function
  | Unit -> empty_ids
  | Atom (ids,_) -> ids
  | InlineAggregs (ids,_,_) -> ids
  | Join (ids,_) -> ids
  | Aggreg (ids,_,_) -> ids

let rec sid_in_view sid = function
  | Unit -> false
  | Atom (_,sid1) -> sid1 = sid
  | InlineAggregs (_,sid1,_) -> sid1 = sid
  | Join (_,lv) -> List.exists (fun v -> sid_in_view sid v) lv
  | Aggreg (_,sid1,v) -> sid1 = sid || sid_in_view sid v

let rec top_sid_in_view sid = function
  | Unit -> false
  | Atom (_,sid1) -> sid1 = sid
  | InlineAggregs (_,sid1,_) -> sid1 = sid
  | Join (_,lv) -> List.exists (fun v -> top_sid_in_view sid v) lv
  | Aggreg (_,sid1,_) -> sid1 = sid

let join_views = function
  | [] -> Unit
  | [v] -> v
  | lv -> let ids = list_concat_ids (List.map view_ids lv) in
	  let ids = (* removing locally aggregated ids from defs and dims *)
	    List.fold_left
	      (fun ids ->
		function
		| InlineAggregs (_,_,ids2) ->
		  {ids with defs = Ids.diff ids.defs ids2; dims = Ids.diff ids.dims ids2}
		| _ -> ids)
	      ids lv in
	  Join (ids, lv)

let seq_view_defs (_, v : seq_view) : id list =
  Ids.elements (view_ids v).defs

let seq_view_available_dims (focus_sid, v : seq_view) : id list option =
  let rec aux : view -> Ids.t option = function
    | Unit -> None
    | Atom _ -> None
    | InlineAggregs _ -> None
    | Join (ids,lv) ->
      if List.exists (function InlineAggregs (_,sid,_) -> sid = focus_sid | _ -> false) lv
      then
	let ids_defs =
	  List.fold_left
	    (fun ids_defs ->
	      function
	      | InlineAggregs (ids,_,_) -> Ids.diff (Ids.diff ids_defs ids.defs) ids.refs
	      | _ -> ids_defs)
	    ids.defs lv in
	Some ids_defs
      else
	List.fold_left
	  (fun res v ->
	    match res, aux v with
	    | None, None -> None
	    | None, Some ids -> Some ids
	    | Some ids, None -> Some ids
	    | Some ids1, Some ids2 -> Some (Ids.union ids1 ids2))
	  None lv
    | Aggreg (ids,sid,v) ->
      if sid = focus_sid
      then Some (Ids.diff (view_ids v).defs ids.refs)
      else None
  in
  match aux v with
  | None -> None
  | Some ids -> Some (Ids.elements ids)


let rec views_of_seq (focus_id_opt : id option) (views : view list) (sid : sid) : (annot * annot elt_s) list -> view list = function
  | [] -> views
  | (a,s)::las ->
    let ids = a#ids in
    match s with
    | Return _ -> (* TODO: handle Return's depending on other sentences *)
      views_of_seq focus_id_opt (Atom (ids, sid) :: views) (sid+1) las
    | SExpr _ | SFilter _ ->
      let new_view = Atom (ids, sid) in
      let views =
	List.fold_right
	  (fun view views ->
	    if Ids.subset ids.refs (view_ids view).defs
	    then join_views [view; new_view]::views
	    else view::views)
	  views [] in
      views_of_seq focus_id_opt views (sid+1) las
    | SAggreg (_, aggregs) when List.exists is_ForEachResult aggregs ->
      let ids2 =
	List.fold_left
	  (fun ids2 ->
	    function
	    | TheAggreg (_,id,modif,g,rel_opt,id2) -> Ids.add id2 ids2
	    | _ -> ids2)
	  Ids.empty aggregs in	  
      let new_view = InlineAggregs (ids, sid, ids2) in
      let views =
	List.fold_right
	  (fun view views ->
	    let not_suspended_aggreg =
	      match focus_id_opt with
	      | Some focus_id -> not (Ids.mem focus_id ids.refs)
	      | None -> true in
	    if Ids.subset ids.refs (view_ids view).defs && not_suspended_aggreg
	    then join_views [view; new_view]::views
	    else view::views)
	  views [] in
      views_of_seq focus_id_opt views (sid+1) las
    | SAggreg (_, aggregs) ->
      let views =
	try
	  let aggregated_view =
	    List.find
	      (fun view -> Ids.subset ids.refs (view_ids view).defs)
	      views in
	  let aggregated_view = (* removing unnecessary sub-aggregs from aggregated view *)
	    match aggregated_view with
	    | Join (_,lv) ->
	      let _, lv2 =
		List.fold_right
		  (fun v (refs,lv2) ->
		    let v_ids = view_ids v in
		    if (match v with Aggreg _ -> true | _ -> false)
		      && Ids.is_empty (Ids.inter refs v_ids.defs)
		    then (refs,lv2)
		    else (Ids.union v_ids.refs refs, v::lv2))
		  lv (ids.refs,[]) in		
	      join_views lv2
	    | _ -> aggregated_view in
	  let merged, views =
	    List.fold_right
	      (fun view (merged,views) ->
		let v_ids = view_ids view in
		if Ids.subset ids.dims v_ids.dims
		then
		  let ids = (* removing dimension definitions before joining, preferring the original to the copy *)
		    { ids with
		      defs = List.fold_left
			(fun defs -> function
			| ForEach (_,id,_,_,_) -> Ids.remove id defs
			| _ -> defs)
			ids.defs aggregs } in
		  let aggregation_view = Aggreg (ids, sid, aggregated_view) in
		  let same_dims = Ids.subset v_ids.dims ids.dims in
		  (merged || same_dims), join_views [view; aggregation_view]::views
		else merged, view::views)
	      views (false,[]) in
	  if merged
	  then views
	  else
	    let aggregation_view = Aggreg (ids, sid, aggregated_view) in
	    aggregation_view :: views
	with Not_found -> views in
      views_of_seq focus_id_opt views (sid+1) las
    | Seq _ -> assert false

let view_of_list a_lr =
  let views = views_of_seq None [] 0 a_lr in
  let sid = List.length a_lr - 1 in
  sid,
  (try List.find (top_sid_in_view sid) views
   with _ ->
     match views with
     | [] -> Unit
     | v::_ -> v)

let view_of_list_focus focus_id_opt a_x a_ll_rr =
  (* computing views *)
  let views = views_of_seq focus_id_opt [] 0 (list_of_ctx a_x a_ll_rr) in
  let sid = List.length (fst a_ll_rr) in
  sid,
  (try List.find (top_sid_in_view sid) views
   with _ ->
     match views with
     | [] -> Unit
     | v::_ -> v)

    
(* unzipping and annotation *)

let ids_an_id ~inactive id =
  let defs = if inactive then Ids.empty else Ids.singleton id in
  { empty_ids with seq = [id]; all = Ids.singleton id; defs = defs; dims = defs }
    
let ids_elt_s2 ~inactive = function
  | Term _ -> empty_ids
  | An (id, _, _) -> ids_an_id ~inactive id
  | The id -> { empty_ids with refs = Ids.singleton id }

let rec annot_elt_p1 pos f ctx =
  let annot = new annot ~focus_pos:pos ~focus:(AtP1 (f,ctx)) in
  let pos_down = focus_pos_down pos in
  match f with
  | Is (_,np) ->
     let a1, a_np = annot_elt_s1 pos_down np (IsX ctx) in
     let a = annot ~ids:a1#ids () in
     a, Is (a, a_np)
  | Pred (_,arg,pred,cp) ->
     let a1, a_cp = annot_elt_sn pos_down cp (PredX (arg,pred,ctx)) in
     let a = annot ~ids:a1#ids () in
     a, Pred (a, arg, pred, a_cp)
  | Type (_,c) ->
     let a = annot () in
     a, Type (a, c)
  | Rel(_,p,m,np) ->
     let a1, a_np = annot_elt_s1 pos_down np (RelX (p,m,ctx)) in
     let a = annot ~ids:a1#ids () in
     a, Rel (a, p, m, a_np)
  | Hier (_,id,pred,args,argo,x) ->
     let ids_hier = ids_an_id ~inactive:false id in
     let a1, a_x = annot_elt_s1 pos_down x (HierX (id,pred,args,argo,ctx)) in
     let ids = concat_ids ids_hier a1#ids in
     let a = annot ~ids () in
     a, Hier (a, id, pred, args, argo, a_x)
  | Sim (_,np,pred,args,argo,rank) ->
     let a1, a_np = annot_elt_s1 pos_down np (SimX (pred,args,argo,rank,ctx)) in
     let ids = a1#ids in
     let a = annot ~ids () in
     a, Sim (a,a_np,pred,args,argo,rank)
  | LatLong (_,ll,id1,id2) ->
     let a = annot ~ids:(concat_ids (ids_an_id ~inactive:false id1) (ids_an_id ~inactive:false id2)) () in
     a, LatLong (a, ll, id1, id2)
  | Triple (_,arg,np1,np2) ->
     let a1, a_np1 = annot_elt_s1 pos_down np1 (TripleX1 (arg,np2,ctx)) in
     let a2, a_np2 = annot_elt_s1 pos_down np2 (TripleX2 (arg,np1,ctx)) in
     let a = annot ~ids:(concat_ids a1#ids a2#ids) () in
     a, Triple (a, arg, a_np1, a_np2)
  | Search (_,c) ->
     let a = annot () in
     a, Search (a, c)
  | Filter (_,c,ft) ->
     let a = annot () in
     a, Filter (a, c, ft)
  | And (_,lr) ->
     let la, lax =
       List.split (List.map
		     (fun (x,ll_rr) -> annot_elt_p1 pos_down x (AndX (ll_rr,ctx)))
		     (ctx_of_list lr)) in
     let a = annot ~ids:(list_concat_ids (List.map (fun a -> a#ids) la)) () in
     a, And (a, lax)
  | Or (_,lr) ->
     let la, lax =
       List.split (List.map
		     (fun (x,ll_rr) -> annot_elt_p1 pos_down x (OrX (ll_rr,ctx)))
		     (ctx_of_list lr)) in
     let a = annot ~ids:(list_concat_ids (List.map (fun a -> a#ids) la)) () in
     a, Or (a, lax)
  | Maybe (_,x) ->
     let a1, a_x = annot_elt_p1 pos_down x (MaybeX ctx) in
     let a = annot ~ids:a1#ids () in
     a, Maybe (a, a_x)
  | Not (_,x) ->
     let a1, a_x = annot_elt_p1 pos_down x (NotX ctx) in
     let a = annot ~ids:{a1#ids with defs=Ids.empty; dims=Ids.empty} () in
     a, Not (a, a_x)
  | In (_,npg,x) ->
     let a1, a_npg = annot_elt_s1 pos_down npg (InGraphX (x,ctx)) in
     let a2, a_x = annot_elt_p1 pos_down x (InX (npg,ctx)) in
     let a = annot ~ids:(concat_ids a1#ids a2#ids) () in
     a, In (a, a_npg, a_x)
  | InWhichThereIs (_,np) ->
     let a1, a_np = annot_elt_s1 pos_down np (InWhichThereIsX ctx) in
     let a = annot ~ids:a1#ids () in
     a, InWhichThereIs (a, a_np)
  | IsThere _ ->
     let a = annot () in
     a, IsThere a
and annot_elt_p1_opt pos rel_opt ctx =
  match rel_opt with
  | None -> empty_ids, None
  | Some rel ->
     let a, a_rel = annot_elt_p1 pos rel ctx in
     a#ids, Some a_rel
and annot_elt_sn pos cp ctx =
  let annot = new annot ~focus_pos:pos ~focus:(AtSn (cp,ctx)) in
  let pos_down = focus_pos_down pos in
  match cp with
  | CNil _ ->
     let a = annot () in
     a, CNil a
  | CCons (_,arg,np,cp) ->
     let a1, a_np = annot_elt_s1 pos_down np (CConsX1 (arg,cp,ctx)) in
     let a2, a_cp = annot_elt_sn pos_down cp (CConsX2 (arg,np,ctx)) in
     let a = annot ~ids:(concat_ids a1#ids a2#ids) () in
     a, CCons (a, arg, a_np, a_cp)
  | CAnd (_,lr) ->
     let la, lax =
       List.split (List.map
		     (fun (x,ll_rr) -> annot_elt_sn pos_down x (CAndX (ll_rr,ctx)))
		     (ctx_of_list lr)) in
     let a = annot ~ids:(list_concat_ids (List.map (fun a -> a#ids) la)) () in
     a, CAnd (a, lax)
  | COr (_,lr) ->
     let la, lax =
       List.split (List.map
		     (fun (x,ll_rr) -> annot_elt_sn pos_down x (COrX (ll_rr,ctx)))
		     (ctx_of_list lr)) in
     let a = annot ~ids:(list_concat_ids (List.map (fun a -> a#ids) la)) () in
     a, COr (a, lax)
  | CMaybe (_,x) ->
     let a1, a_x = annot_elt_sn pos_down x (CMaybeX ctx) in
     let a = annot ~ids:a1#ids () in
     a, CMaybe (a, a_x)
  | CNot (_,x) ->
     let a1, a_x = annot_elt_sn pos_down x (CNotX ctx) in
     let a = annot ~ids:{a1#ids with defs = Ids.empty; dims = Ids.empty} () in
     a, CNot (a, a_x)
and annot_elt_s1 pos np ctx =
  let annot = new annot ~focus_pos:pos ~focus:(AtS1 (np,ctx)) in
  let pos_down = focus_pos_down pos in
  match np with
  | Det (_,det,rel_opt) ->
     let ids_det =
       let inactive = is_s1_as_p1_ctx_s1 ctx || is_unconstrained_det det rel_opt ctx || is_hierarchy_ctx_s1 ctx in
       ids_elt_s2 ~inactive det in
     let ids_rel, a_rel_opt = annot_elt_p1_opt pos_down rel_opt (DetThatX (det,ctx)) in
     let a = annot ~ids:(concat_ids ids_det ids_rel) () in
     a, Det (a, det, a_rel_opt)
  | AnAggreg (_,id,modif,g,rel_opt,x) ->
     let ids_rel, a_rel_opt = annot_elt_p1_opt pos_down rel_opt (AnAggregThatX (id,modif,g,x,ctx)) in
     let a1, a_x = annot_elt_s1 pos_down x (AnAggregX (id,modif,g,rel_opt,ctx)) in
     let ids_aggreg = { empty_ids with seq = [id]; all = Ids.singleton id; defs = Ids.singleton id } in
     let ids = list_concat_ids [ids_aggreg; ids_rel; a1#ids] in
     let ids =
       match id_of_s1 x with
       | None -> assert false
       | Some id2 -> { ids with defs = Ids.remove id2 ids.defs; dims = Ids.remove id2 ids.dims; refs = Ids.add id2 ids.refs } in
     let a = annot ~ids () in
     a, AnAggreg (a, id, modif, g, a_rel_opt, a_x)
  | NAnd (_,lr) ->
     let la, lax =
       List.split (List.map
		     (fun (x,ll_rr) -> annot_elt_s1 pos_down x (NAndX (ll_rr,ctx)))
		     (ctx_of_list lr)) in
     let a = annot ~ids:(list_concat_ids (List.map (fun a -> a#ids) la)) () in
     a, NAnd (a, lax)
  | NOr (_,lr) ->
     let la, lax =
       List.split (List.map
		     (fun (x,ll_rr) -> annot_elt_s1 pos_down x (NOrX (ll_rr,ctx)))
		     (ctx_of_list lr)) in
     let a = annot ~ids:(list_concat_ids (List.map (fun a -> a#ids) la)) () in
		  a, NOr (a, lax)
  | NMaybe (_,x) ->
     let a1, a_x = annot_elt_s1 pos_down x (NMaybeX ctx) in
     let a = annot ~ids:a1#ids () in
     a, NMaybe (a, a_x)
  | NNot (_,x) ->
     let a1, a_x = annot_elt_s1 pos_down x (NNotX ctx) in
     let a = annot ~ids:{a1#ids with defs = Ids.empty; dims = Ids.empty} () in
     a, NNot (a, a_x)
and annot_elt_aggreg pos aggreg ctx =
  let annot = new annot ~focus_pos:pos ~focus:(AtAggreg (aggreg,ctx)) in
  let pos_down = focus_pos_down pos in
  match aggreg with
  | ForEachResult _ ->
     let ids = empty_ids in
     let a = annot ~ids () in
     a, ForEachResult a
  | ForEach (_,id,modif,rel_opt,id2) ->
     let ids_rel, a_rel_opt = annot_elt_p1_opt pos_down rel_opt (ForEachThatX (id,modif,id2,ctx)) in
     (* TODO: what about defined ids in rel_opt *)
     let ids = {seq = id::ids_rel.seq; all = Ids.singleton id; defs = Ids.singleton id; dims = Ids.singleton id2; refs = Ids.add id2 ids_rel.refs} in
     let a = annot ~ids () in
     a, ForEach (a, id, modif, a_rel_opt, id2)
  | ForTerm (_,t,id2) ->
     let a = annot ~ids:{empty_ids with refs = Ids.singleton id2} () in
     a, ForTerm (a, t, id2)
  | TheAggreg (_,id,modif,g,rel_opt,id2) ->
     let ids_rel, a_rel_opt = annot_elt_p1_opt pos_down rel_opt (TheAggregThatX (id,modif,g,id2,ctx)) in
     let ids = {seq = id::ids_rel.seq;
		all = Ids.add id ids_rel.all;
		defs = Ids.add id ids_rel.defs;
		dims = ids_rel.dims;
		refs = Ids.add id2 ids_rel.refs} in
     let a = annot ~ids () in
     a, TheAggreg (a, id, modif, g, a_rel_opt, id2)
and annot_elt_expr pos expr ctx =
  let annot = new annot ~focus_pos:pos ~focus:(AtExpr (expr,ctx)) in
  let pos_down = focus_pos_down pos in
  match expr with
  | Undef _ ->
     let a = annot ~ids:empty_ids ~defined:false () in
     a, Undef a
  | Const (_,t) ->
     let a = annot ~ids:empty_ids ~defined:true () in
     a, Const (a, t)
  | Var (_,id) ->
     let a = annot ~ids:{empty_ids with refs = Ids.singleton id} ~defined:true () in (* we assume 'id' is a valid reference *)
     a, Var (a, id)
  | Apply (_,func,args) ->
    let la, l_a_arg =
      List.split (List.map
		    (fun ((conv_opt,arg_expr),ll_rr) ->
		      let a, a_arg_expr = annot_elt_expr pos_down arg_expr (ApplyX (func, ll_rr, conv_opt, ctx)) in
		      a, (conv_opt,a_arg_expr))
		    (ctx_of_list args)) in
    let a = annot
      ~ids:(list_concat_ids (List.map (fun a -> a#ids) la))
      ~defined:(List.for_all (fun a -> a#defined) la) () in
    a, Apply (a, func, l_a_arg)
  | Choice (_,le) ->
    let la, l_a_expr =
      List.split (List.map
		    (fun (expr,ll_rr) -> annot_elt_expr pos_down expr (ChoiceX (ll_rr, ctx)))
		    (ctx_of_list le)) in
    let a = annot
      ~ids:(list_concat_ids (List.map (fun a -> a#ids) la))
      ~defined:(List.exists (fun a -> a#defined) la) () in
    a, Choice (a, l_a_expr)
and annot_elt_s pos s ctx =
  let annot = new annot ~focus_pos:pos ~focus:(AtS (s,ctx)) in
  let pos_down = focus_pos_down pos in
  match s with
  | Return (_,np) ->
    let a1, a_np = annot_elt_s1 pos_down np (ReturnX ctx) in
    let a = annot ~ids:a1#ids () in
    a, Return (a, a_np)
  | SAggreg (_,aggregs) ->
    let la, l_a_aggreg =
      List.split (List.map
		    (fun (x,ll_rr) -> annot_elt_aggreg pos_down x (SAggregX (ll_rr,ctx)))
		    (ctx_of_list aggregs)) in
    let a = annot ~ids:(list_concat_ids (List.map (fun a -> a#ids) la)) () in
    a, SAggreg (a, l_a_aggreg)
  | SExpr (_,name,id,modif,expr,rel_opt) ->
    let a1, a_expr = annot_elt_expr pos_down expr (SExprX (name,id,modif,rel_opt,ctx)) in
    let ids_rel, a_rel_opt = annot_elt_p1_opt pos_down rel_opt (SExprThatX (name,id,modif,expr,ctx)) in
    let ids = concat_ids a1#ids ids_rel in
    let a = annot ~ids:{ids with seq = id::ids.seq; all = Ids.add id ids.all; defs = if a1#defined then Ids.add id ids.defs else ids.defs} () in
    a, SExpr (a, name, id, modif, a_expr, a_rel_opt)
  | SFilter (_,id,expr) ->
    let a1, a_expr = annot_elt_expr pos_down expr (SFilterX (id,ctx)) in
    let ids = a1#ids in
    let a = annot ~ids:{ids with seq = id::ids.seq; all = Ids.add id ids.all; defs = if a1#defined then Ids.add id ids.defs else ids.defs} () in
    a, SFilter (a, id, a_expr)
  | Seq (_,lr) ->
    let a_lr =
      List.map
	(fun (x,ll_rr) -> annot_elt_s pos_down x (SeqX (ll_rr,ctx)))
	(ctx_of_list lr) in
    match clean_list a_lr lr with
    | `Changed lr ->
      annot_elt_s pos (if lr=[] then fst factory#top_s else Seq ((), lr)) ctx
    | `Unchanged ->
      let seq_view = view_of_list a_lr in
      let la, lar = List.split a_lr in
      let a = annot ~ids:(list_concat_ids (List.map (fun a -> a#ids) la)) ~seq_view () in
      a, Seq (a, lar)
  
let rec annot_ctx_p1 fd (a1,a_x) x = function
  | DetThatX (det, ctx) ->
    ( match hierarchy_of_ctx_s1 ctx with
      | Some (id,_,_,_) ->
	 fd#define_focus_term (`Id id)
      | None when not (is_s1_as_p1_ctx_s1 ctx) ->
	 fd#define_focus_term (term_id_s2 det :> focus_term)
      | _ -> () );
    fd#resolve_focus_graph (focus_graph_s2 det);
    let f = Det ((),det,Some x) in
    let ids_det =
      let inactive = is_s1_as_p1_ctx_s1 ctx || is_unconstrained_det det (Some x) ctx || is_hierarchy_ctx_s1 ctx in
      ids_elt_s2 ~inactive det in
    let ids = concat_ids ids_det a1#ids in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS1 (f,ctx)) ~ids () in
    annot_ctx_s1 fd (a, Det (a, det, Some a_x)) f ctx
  | AnAggregThatX (id,modif,g,np,ctx) ->
    fd#define_focus_term (`Id id);
    fd#set_no_incr;
    fd#resolve_focus_graph (`Named (`Id id));
    let f = AnAggreg ((),id,modif,g,Some x,np) in
    let a2, a_np = annot_elt_s1 (`Aside false) np (AnAggregX (id,modif,g,Some x,ctx)) in
    let ids_aggreg = { empty_ids with seq = [id]; all = Ids.singleton id; defs = Ids.singleton id } in
    let ids = list_concat_ids [ids_aggreg; a1#ids; a2#ids] in
    let ids =
      match id_of_s1 np with
      | None -> assert false
      | Some id2 -> { ids with defs = Ids.remove id2 ids.defs; dims = Ids.remove id2 ids.dims; refs = Ids.add id2 ids.refs } in
    let a = new annot ~focus_pos:(`Above (false, None)) ~focus:(AtS1 (f,ctx)) ~ids () in
    annot_ctx_s1 fd (a, AnAggreg (a, id, modif, g, Some a_x, a_np)) f ctx
  | ForEachThatX (id,modif,id2,ctx) ->
    fd#define_focus_term (`Id id);
    fd#resolve_focus_graph (`Named (`Id id));
    let f = ForEach ((),id,modif,Some x,id2) in
    let ids = a1#ids in
    let ids = {seq = id::ids.seq; all = Ids.add id ids.all; defs = Ids.add id ids.defs; dims = Ids.add id2 ids.dims; refs = Ids.add id2 ids.refs} in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtAggreg (f,ctx)) ~ids () in
    annot_ctx_aggreg fd (a, ForEach (a, id, modif, Some a_x, id2)) f ctx
  | TheAggregThatX (id,modif,g,id2,ctx) ->
    fd#define_focus_term (`Id id);
    fd#set_no_incr;
    fd#resolve_focus_graph (`Named (`Id id));
    let f = TheAggreg ((),id,modif,g,Some x,id2) in
    let ids = a1#ids in
    let ids = {seq = id::ids.seq; all = Ids.add id ids.all; defs = Ids.add id ids.defs; dims = ids.dims; refs = Ids.add id2 ids.refs} in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtAggreg (f,ctx)) ~ids () in
    annot_ctx_aggreg fd (a, TheAggreg (a, id, modif, g, Some a_x, id2)) f ctx
  | SExprThatX (name,id,modif,expr,ctx) ->
    fd#define_focus_term (`Id id);
    fd#set_no_incr;
    fd#resolve_focus_graph (`Named (`Id id));
    let f = SExpr ((), name, id, modif, expr, Some x) in
    let a2, a_expr = annot_elt_expr (`Aside false) expr (SExprX (name,id,modif,Some x,ctx)) in
    let ids = concat_ids a2#ids a1#ids in
    let ids = {ids with seq = id::ids.seq; all = Ids.add id ids.all; defs = if a2#defined then Ids.add id ids.defs else ids.defs} in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS (f,ctx)) ~ids () in
    annot_ctx_s fd (a, SExpr (a, name, id, modif, a_expr, Some a_x)) f ctx
  | AndX (ll_rr,ctx) ->
    let f = And ((), list_of_ctx x ll_rr) in
    let la, lar =
      List.split
	(list_of_ctx (a1,a_x)
	   (map_ctx_list
	      (fun (x2,ll_rr2) -> annot_elt_p1 (`Aside false) x2 (AndX (ll_rr2,ctx)))
	      (ctx_of_ctx_list x ll_rr))) in
    let ids = list_concat_ids (List.map (fun a -> a#ids) la) in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) ~ids () in
    annot_ctx_p1 fd (a, And (a, lar)) f ctx
  | OrX ((ll,rr as ll_rr),ctx) -> (* alternative branches are suspended *)
    let f = Or ((), list_of_ctx x ll_rr) in
    let la, lar =
      List.split
	(list_of_ctx (a1,a_x)
	   (map_ctx_list
	      (fun (x2,ll_rr2) -> annot_elt_p1 (`Aside true) x2 (OrX (ll_rr2,ctx)))
	      (ctx_of_ctx_list x ll_rr))) in
    let ids =
      { a1#ids with
	seq = List.concat (List.map (fun a -> a#ids.seq) la);
	all = List.fold_left (fun all a -> Ids.union all a#ids.all) Ids.empty la } in
    (* ids of alternatives are no more visible as defs/dims/refs *)
    let a = new annot ~focus_pos:(`Above (true, Some (List.length ll))) ~focus:(AtP1 (f,ctx)) ~ids () in
    annot_ctx_p1 fd (a, Or (a, lar)) f ctx
  | MaybeX ctx ->
    let f = Maybe ((),x) in
    let ids = a1#ids in
    let a = new annot ~focus_pos:(`Above (true,None)) ~focus:(AtP1 (f,ctx)) ~ids () in (* suspended *)
    annot_ctx_p1 fd (a, Maybe (a, a_x)) f ctx
  | NotX ctx ->
    let f = Not ((),x) in
    let ids = a1#ids in (* negation is suspended *)
    let a = new annot ~focus_pos:(`Above (true,None)) ~focus:(AtP1 (f,ctx)) ~ids () in (* suspended *)
    annot_ctx_p1 fd (a, Not (a, a_x)) f ctx
  | InX (npg,ctx) ->
    fd#define_focus_graph (focus_graph_s1 npg);
    let f = In ((),npg,x) in
    let a2, a_npg = annot_elt_s1 (`Aside false) npg (InGraphX (x,ctx)) in
    let ids = concat_ids a2#ids a1#ids in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) ~ids () in
    annot_ctx_p1 fd (a, In (a,a_npg,a_x)) f ctx
and annot_ctx_sn fd (a1,a_x) x = function
  | PredX (arg,pred,ctx) ->
     let f = Pred ((),arg,pred,x) in
     let ids = a1#ids in
     let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) ~ids () in
     annot_ctx_p1 fd (a, Pred (a, arg, pred, a_x)) f ctx
  | CConsX2 (arg,np,ctx) ->
     let f = CCons ((),arg,np,x) in
     let a2, a_np = annot_elt_s1 (`Aside false) np (CConsX1 (arg,x,ctx)) in
     let ids = concat_ids a2#ids a1#ids in
     let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtSn (f,ctx)) ~ids () in
     annot_ctx_sn fd (a, CCons (a, arg, a_np, a_x)) f ctx
  | CAndX (ll_rr,ctx) ->
    let f = CAnd ((), list_of_ctx x ll_rr) in
    let la, lar =
      List.split
	(list_of_ctx (a1,a_x)
	   (map_ctx_list
	      (fun (x2,ll_rr2) -> annot_elt_sn (`Aside false) x2 (CAndX (ll_rr2,ctx)))
	      (ctx_of_ctx_list x ll_rr))) in
    let ids = list_concat_ids (List.map (fun a -> a#ids) la) in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtSn (f,ctx)) ~ids () in
    annot_ctx_sn fd (a, CAnd (a, lar)) f ctx
  | COrX ((ll,rr as ll_rr),ctx) -> (* alternative branches are suspended *)
    let f = COr ((), list_of_ctx x ll_rr) in
    let la, lar =
      List.split
	(list_of_ctx (a1,a_x)
	   (map_ctx_list
	      (fun (x2,ll_rr2) -> annot_elt_sn (`Aside true) x2 (COrX (ll_rr2,ctx)))
	      (ctx_of_ctx_list x ll_rr))) in
    let ids =
      { a1#ids with
	seq = List.concat (List.map (fun a -> a#ids.seq) la);
	all = List.fold_left (fun all a -> Ids.union all a#ids.all) Ids.empty la } in
    let a = new annot ~focus_pos:(`Above (true, Some (List.length ll))) ~focus:(AtSn (f,ctx)) ~ids () in
    annot_ctx_sn fd (a, COr (a, lar)) f ctx
  | CMaybeX ctx ->
    let f = CMaybe ((),x) in
    let ids = a1#ids in
    let a = new annot ~focus_pos:(`Above (true,None)) ~focus:(AtSn (f,ctx)) ~ids () in (* suspended *)
    annot_ctx_sn fd (a, CMaybe (a, a_x)) f ctx
  | CNotX ctx ->
    let f = CNot ((),x) in
    let ids = a1#ids in
    let a = new annot ~focus_pos:(`Above (true,None)) ~focus:(AtSn (f,ctx)) ~ids () in (* suspended *)
    annot_ctx_sn fd (a, CNot (a, a_x)) f ctx
and annot_ctx_s1 fd (a1,a_x) x = function
  | IsX ctx ->
    let f = Is ((),x) in
    let ids = a1#ids in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) ~ids () in
    annot_ctx_p1 fd (a, Is (a, a_x)) f ctx
  | CConsX1 (arg,cp,ctx) ->
     let f = CCons ((),arg,x,cp) in
     let a2, a_cp = annot_elt_sn (`Aside false) cp (CConsX2 (arg,x,ctx)) in
     let ids = concat_ids a1#ids a2#ids in
     let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtSn (f,ctx)) ~ids () in
     annot_ctx_sn fd (a, CCons (a, arg, a_x, a_cp)) f ctx
  | RelX (p,modif,ctx) ->
    fd#define_focus_term `Undefined;
    let f = Rel ((),p,modif,x) in
    let ids = a1#ids in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) ~ids () in
    annot_ctx_p1 fd (a, Rel (a, p, modif, a_x)) f ctx
  | TripleX1 (arg,np2,ctx) ->
    fd#define_focus_term `Undefined;
    let f = Triple ((),arg,x,np2) in
    let a2, a_np2 = annot_elt_s1 (`Aside false) np2 (TripleX2 (arg,x,ctx)) in
    let ids = concat_ids a1#ids a2#ids in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) ~ids () in
    annot_ctx_p1 fd (a, Triple (a, arg, a_x, a_np2)) f ctx
  | TripleX2 (arg,np1,ctx) ->
    fd#define_focus_term `Undefined;
    let f = Triple ((),arg,np1,x) in
    let a2, a_np1 = annot_elt_s1 (`Aside false) np1 (TripleX1 (arg,x,ctx)) in
    let ids = concat_ids a2#ids a1#ids in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) ~ids () in
    annot_ctx_p1 fd (a, Triple (a, arg, a_np1, a_x)) f ctx
  | ReturnX ctx ->
    fd#define_focus_term `Undefined;
    let f = Return ((),x) in
    let ids = a1#ids in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS (f,ctx)) ~ids () in
    annot_ctx_s fd (a, Return (a, a_x)) f ctx
  | HierX (id,pred,args,argo,ctx) ->
     fd#define_focus_term `Undefined;
     let f = Hier ((),id,pred,args,argo,x) in
     let ids_hier = ids_an_id ~inactive:false id in
     let ids = concat_ids ids_hier a1#ids in
     let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) ~ids () in
     annot_ctx_p1 fd (a, Hier (a, id, pred, args, argo, a_x)) f ctx
  | SimX (pred,args,argo,rank,ctx) ->
     let f = Sim ((),x,pred,args,argo,rank) in
     let ids = a1#ids in
     let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) ~ids () in
     annot_ctx_p1 fd (a, Sim (a, a_x, pred, args, argo, rank)) f ctx
  | AnAggregX (id,modif,g,rel_opt,ctx) -> (* suspended *)
    let f = AnAggreg ((),id,modif,g,rel_opt,x) in
    let _ids_rel, a_rel_opt = annot_elt_p1_opt (`Aside true) rel_opt (AnAggregThatX (id,modif,g,x,ctx)) in
    let ids = a1#ids in (* suspended aggregation *)
    let a = new annot ~focus_pos:(`Above (true,None)) ~focus:(AtS1 (f,ctx)) ~ids () in
    annot_ctx_s1 fd (a, AnAggreg (a, id, modif, g, a_rel_opt, a_x)) f ctx
  | NAndX (ll_rr,ctx) ->
    let f = NAnd ((), list_of_ctx x ll_rr) in
    let la, lar =
      List.split
	(list_of_ctx (a1,a_x)
	   (map_ctx_list
	      (fun (x2,ll_rr2) -> annot_elt_s1 (`Aside false) x2 (NAndX (ll_rr2,ctx)))
	      (ctx_of_ctx_list x ll_rr))) in
    let ids = list_concat_ids (List.map (fun a -> a#ids) la) in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS1 (f,ctx)) ~ids () in
    annot_ctx_s1 fd (a, NAnd (a, lar)) f ctx
  | NOrX ((ll,rr as ll_rr),ctx) -> (* alternative branches are suspended *)
    let f = NOr ((), list_of_ctx x ll_rr) in
    let la, lar =
      List.split
	(list_of_ctx (a1,a_x)
	   (map_ctx_list
	      (fun (x2,ll_rr2) -> annot_elt_s1 (`Aside true) x2 (NOrX (ll_rr2,ctx)))
	      (ctx_of_ctx_list x ll_rr))) in
    let ids =
      { a1#ids with
	seq = List.concat (List.map (fun a -> a#ids.seq) la);
	all = List.fold_left (fun all a -> Ids.union all a#ids.all) Ids.empty la } in
    let a = new annot ~focus_pos:(`Above (true, Some (List.length ll))) ~focus:(AtS1 (f,ctx)) ~ids () in
    annot_ctx_s1 fd (a, NOr (a, lar)) f ctx
  | NMaybeX ctx ->
    let f = NMaybe ((),x) in
    let ids = a1#ids in
    let a = new annot ~focus_pos:(`Above (true,None)) ~focus:(AtS1 (f,ctx)) ~ids () in (* suspended *)
    annot_ctx_s1 fd (a, NMaybe (a, a_x)) f ctx
  | NNotX ctx ->
    let f = NNot ((),x) in
    let ids = a1#ids in
    let a = new annot ~focus_pos:(`Above (true,None)) ~focus:(AtS1 (f,ctx)) ~ids () in (* suspended *)
    annot_ctx_s1 fd (a, NNot (a, a_x)) f ctx
  | InGraphX (x2,ctx) ->
    let f = In ((),x,x2) in
    let a2, a_x2 = annot_elt_p1 (`Aside false) x2 (InX (x,ctx)) in
    let ids = concat_ids a1#ids a2#ids in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) ~ids () in
    annot_ctx_p1 fd (a, In (a,a_x,a_x2)) f ctx
  | InWhichThereIsX ctx ->
    fd#wait_focus_graph;
    let f = InWhichThereIs ((),x) in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) ~ids:a1#ids () in
    annot_ctx_p1 fd (a, InWhichThereIs (a,a_x)) f ctx
(*and annot_ctx_dim fd (a1,a_x) x = function
  | SAggregForX (ll_rr,aggregs,ctx) ->
    let dims = list_of_ctx x ll_rr in
    let f = SAggreg ((),dims,aggregs) in
    let la_dim, lar_dim =
      List.split
	(list_of_ctx (a1,a_x)
	   (map_ctx_list
	      (fun (x2,ll_rr2) -> annot_elt_dim (`Aside false) x2 (SAggregForX (ll_rr2,aggregs,ctx)))
	      (ctx_of_ctx_list x ll_rr))) in
    let la_aggreg, lar_aggreg =
      List.split
	(List.map
	   (fun (x2,ll_rr2) -> annot_elt_aggreg (`Aside false) x2 (SAggregX (dims,ll_rr2,ctx)))
	   (ctx_of_list aggregs)) in
    let ids = list_union_ids (List.map (fun a -> a#ids) (la_dim @ la_aggreg)) in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS (f,ctx)) ~ids () in
    annot_ctx_s fd (a, SAggreg (a, lar_dim, lar_aggreg)) f ctx*)
and annot_ctx_aggreg fd (a1,a_x) x = function
  | SAggregX (ll_rr,ctx) ->
    let aggregs = list_of_ctx x ll_rr in
    let f = SAggreg ((),aggregs) in
    let la_aggreg, lar_aggreg =
      List.split
	(list_of_ctx (a1,a_x)
	   (map_ctx_list
	      (fun (x2,ll_rr2) -> annot_elt_aggreg (`Aside false) x2 (SAggregX (ll_rr2,ctx)))
	      (ctx_of_ctx_list x ll_rr))) in
    let ids = list_concat_ids (List.map (fun a -> a#ids) la_aggreg) in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS (f,ctx)) ~ids () in
    annot_ctx_s fd (a, SAggreg (a, lar_aggreg)) f ctx
and annot_ctx_expr defined fd (a1,a_x) x = function
(* 'defined' is about the sub-expression at focus *)
  | SExprX (name,id,modif,rel_opt,ctx) ->
    fd#define_focus_term (`Id id);
    fd#set_no_incr;
    let f = SExpr ((),name,id,modif,x,rel_opt) in
    let ids_rel, a_rel_opt = annot_elt_p1_opt (`Aside false) rel_opt (SExprThatX (name,id,modif,x,ctx)) in
    let ids = concat_ids a1#ids ids_rel in
    let ids = {ids with seq = id::ids.seq; all = Ids.add id ids.all; defs = if defined then Ids.add id ids.defs else ids.defs} in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS (f,ctx)) ~ids () in
    annot_ctx_s fd (a, SExpr (a, name, id, modif, a_x, a_rel_opt)) f ctx
  | SFilterX (id,ctx) ->
    fd#define_focus_term (`Id id);
    fd#set_no_incr;
    let f = SFilter ((),id,x) in
    let ids = a1#ids in
    let ids = {ids with seq = id::ids.seq; all = Ids.add id ids.all; defs = if defined then Ids.add id ids.defs else ids.defs} in
    let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS (f,ctx)) ~ids () in
    annot_ctx_s fd (a, SFilter (a, id, a_x)) f ctx
  | ApplyX (func,ll_rr,conv_opt,ctx) ->
    let f = Apply ((), func, list_of_ctx (conv_opt,x) ll_rr) in
    let la, lar =
      List.split
	(list_of_ctx (a1, (conv_opt,a_x))
	   (map_ctx_list
	      (fun ((conv_opt2,x2),ll_rr2) ->
		let a2, a_x2 = annot_elt_expr (`Aside true) x2 (ApplyX (func, ll_rr2, conv_opt2, ctx)) in
		a2, (conv_opt2,a_x2))
	      (ctx_of_ctx_list (conv_opt,x) ll_rr))) in
    let ids = list_concat_ids (List.map (fun a -> a#ids) la) in
    let a = new annot ~focus_pos:(`Above (true, Some (1 + List.length (fst ll_rr)))) ~focus:(AtExpr (f,ctx)) ~ids ~defined () in
    annot_ctx_expr defined fd (a, Apply (a, func, lar)) f ctx
  | ChoiceX (ll_rr,ctx) ->
    let f = Choice ((), list_of_ctx x ll_rr) in
    let la, lar =
      List.split
	(list_of_ctx (a1,a_x)
	   (map_ctx_list
	      (fun (x2,ll_rr2) -> annot_elt_expr (`Aside true) x2 (ChoiceX (ll_rr2, ctx)))
	      (ctx_of_ctx_list x ll_rr))) in
    let ids =
      { a1#ids with
	seq = List.concat (List.map (fun a -> a#ids.seq) la);
	all = List.fold_left (fun all a -> Ids.union all a#ids.all) Ids.empty la } in
    let a = new annot ~focus_pos:(`Above (true, Some (List.length (fst ll_rr)))) ~focus:(AtExpr (f,ctx)) ~ids ~defined () in
    annot_ctx_expr defined fd (a, Choice (a, lar)) f ctx
and annot_ctx_s fd (a1,a_x) x = function
  | Root -> fd, (a1,a_x)
  | SeqX (ll_rr,ctx) ->
    let f = Seq ((), list_of_ctx x ll_rr) in
    let a_ll_rr =
      map_ctx_list
	(fun (x2,ll_rr2) -> annot_elt_s (`Aside false) x2 (SeqX (ll_rr2,ctx)))
	(ctx_of_ctx_list x ll_rr) in
    match clean_list_focus (a1,a_x) x a_ll_rr ll_rr with
    | `Changed new_opt ->
      let focus =
	match new_opt with
	| None -> AtS (fst factory#top_s, Root)
	| Some (x,ll_rr) -> AtS (x, SeqX (ll_rr,ctx)) in
      let focus = 
	match down_focus focus with
	| None -> focus
	| Some focus -> focus in
      annot_focus_aux focus
    | `Unchanged ->
      let seq_view = view_of_list_focus (focus_term_id fd#term) (a1,a_x) a_ll_rr in
      let la, lar = List.split (list_of_ctx (a1,a_x) a_ll_rr) in
      let ids = list_concat_ids (List.map (fun a -> a#ids) la) in
      let a = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS (f,ctx)) ~ids ~seq_view () in
      annot_ctx_s fd (a, Seq (a, lar)) f ctx

and annot_focus_aux (focus : focus) =
  let pred_args = focus_pred_args focus in
  let fd = new focus_descr ~pred_args in
  match focus with
  | AtP1 (f,ctx) ->
     if is_unconstrained_focus_p1 f ctx then fd#set_unconstrained;
     let f_annot = annot_elt_p1 `At f ctx in
     annot_ctx_p1 fd f_annot f ctx
(*  | AtSn (CCons (_,arg,np,cp),ctx) ->
     annot_focus_aux (AtS1 (np, CConsX1 (arg,cp,ctx)))*)
  | AtSn (cp,ctx) ->
     ( match cp with
       | CCons (_,arg,np,cp) ->
	  ( match term_id_s1 np with
	    | Some ti -> fd#define_focus_term (ti :> focus_term)
	    | None -> fd#define_focus_term `Undefined )
       | _ -> fd#define_focus_term `Undefined );
     let cp_annot = annot_elt_sn `At cp ctx in
     annot_ctx_sn fd cp_annot cp ctx
  | AtS1 (np,ctx) ->
     ( match hierarchy_of_ctx_s1 ctx with
       | Some (id,_,_,_) ->
	  fd#define_focus_term (`Id id)
       | None when not (is_s1_as_p1_ctx_s1 ctx) ->
	  ( match np with
	    | Det (_,det,rel_opt) ->
	       fd#define_focus_term (term_id_s2 det :> focus_term);
	       if is_unconstrained_det det rel_opt ctx then
		 fd#set_unconstrained
	    | AnAggreg (_,id,_,g,_,_) ->
	       fd#define_focus_term (`Id id);
	       fd#set_no_incr
	    | _ ->
	       fd#define_focus_term `Undefined )
       | _ -> () );
     let np_annot = annot_elt_s1 `At np ctx in
     annot_ctx_s1 fd np_annot np ctx
  | AtAggreg (aggreg,ctx) ->
    ( match aggreg with
    | ForEachResult _ -> fd#define_focus_term `Undefined
    | ForEach (_,id,_,_,_) -> fd#define_focus_term (`Id id)
    | ForTerm (_,t,_) -> fd#define_focus_term (`Term t); fd#set_no_incr
    | TheAggreg (_,id,_,_,_,_) -> fd#define_focus_term (`Id id); fd#set_no_incr );
    let aggreg_annot = annot_elt_aggreg `At aggreg ctx in
    annot_ctx_aggreg fd aggreg_annot aggreg ctx
  | AtExpr (expr,ctx) ->
    let (a, a_expr as expr_annot) = annot_elt_expr `At expr ctx in
    annot_ctx_expr a#defined fd expr_annot expr ctx
  | AtS (s,ctx) ->
    ( match s with
    | SExpr (_,_,id,_,_,_) -> fd#define_focus_term (`Id id)
      (* consistency with Lisql.id_of_s *)
    | _ -> fd#define_focus_term `Undefined );
    let s_annot = annot_elt_s `At s ctx in
    annot_ctx_s fd s_annot s ctx

let annot_focus (focus : focus) : Ids.t * focus_descr * annot elt_s =
  let fd, (a,a_s) = annot_focus_aux focus in
  let ids = a#ids.all in
  factory#set (try Ids.max_elt ids with Not_found -> 0); (* to account for ids imported from we don't know where (ex., permalinks) *)
  ids, fd, a_s
