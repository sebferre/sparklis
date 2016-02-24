(* translation from LISQL focus to annotated LISQL *)
(* to ensure consistency between lisql2nl and lisql2sparql, and simplify them *)

open Rdf
open Lisql

(* focus terms *)

type focus_term = [ `Term of Rdf.term | `IdIncr of id | `IdNoIncr of id | `Undefined ]

let define_focus_term (ft : focus_term) : focus_term option -> focus_term = function
  | None -> ft
  | Some x -> x

let focus_term_s2 : elt_s2 -> focus_term = function
  | Term t -> `Term t
  | An (id,_,_) -> `IdIncr id
  | The id -> `IdIncr id


(* ids and views *)

type sid = int (* sentence id, position in seq list *)
type view =
| Unit
| Atom of id list * sid
| Join of id list * view list
| Aggreg of id list * id list * sid * view

let view_defs = function
  | Unit -> []
  | Atom (defs,_) -> defs
  | Join (defs,_) -> defs
  | Aggreg (defs,refs,_,_) -> defs

let rec view_available_dims = function
  | Unit -> []
  | Atom (defs,_) -> []
  | Join (defs,_) -> []
  | Aggreg (defs,refs,sid,v) -> List.filter (fun id -> not (List.mem id refs)) (view_defs v)

let rec sid_in_view sid = function
  | Unit -> false
  | Atom (_,sid1) -> sid1 = sid
  | Join (_,lv) -> List.exists (fun v -> sid_in_view sid v) lv
  | Aggreg (_,_,sid1,v) -> sid1 = sid || sid_in_view sid v

let rec top_sid_in_view sid = function
  | Unit -> false
  | Atom (_, sid1) -> sid1 = sid
  | Join (_,lv) -> List.exists (fun v -> top_sid_in_view sid v) lv
  | Aggreg (_,_,sid1,_) -> sid1 = sid

let join_views = function
  | [] -> Unit
  | [v] -> v
  | lv -> Join (List.concat (List.map view_defs lv), lv)


let rec views_of_seq (views : view list) (sid : sid) : unit elt_s list -> view list = function
  | [] -> views
  | s::ls ->
    let ids = ids_elt_s s in
    let defs, refs = Ids.defs ids, Ids.refs ids in
    match s with
    | Return _ -> (* TODO: handle Return's depending on other sentences *)
      views_of_seq (Atom (defs, sid) :: views) (sid+1) ls
    | SExpr _ | SFilter _ ->
      let views =
	List.fold_right
	  (fun view views ->
	    let v_defs = view_defs view in
	    if List.for_all
	      (fun ref_id -> List.mem ref_id v_defs)
	      refs
	    then join_views [view; Atom (defs, sid)]::views
	    else view::views)
	  views [] in
      views_of_seq views (sid+1) ls
    | SAggreg _ ->
      let views =
	List.fold_right
	  (fun view views ->
	    let v_defs = view_defs view in
	    if List.for_all
	      (fun ref_id -> List.mem ref_id v_defs)
	      refs
	    then
	      let aggregation_view = Aggreg (defs, refs, sid, view) in
	      aggregation_view::join_views [view; aggregation_view]::views
	    else view::views)
	  views [] in
      views_of_seq views (sid+1) ls
    | Seq _ -> assert false
      
let view_of_list_focus x (ll,rr) =
  (* computing ids for each element of the list context *)
  let x_ids = ids_elt_s x in
  let ll_ids = List.map ids_elt_s ll in
  let rr_ids = List.map ids_elt_s rr in
  (* removing sentences that are no more well-defined (maybe introduced by deletions *)
  let defs, ll_y_ids =
    List.fold_right2
      (fun y ids (defs,ll) ->
	let new_defs = Ids.defs ids @ defs in
	if Ids.all_defined_in ids new_defs
	then (new_defs, (y,ids)::ll)
	else (defs, ll))
      ll ll_ids ([],[]) in
  let defs = Ids.defs x_ids @ defs in
  assert (Ids.all_defined_in x_ids defs);
  let defs, rev_rr =
    List.fold_left2
      (fun (defs,rev_rr) y ids ->
	let new_defs = Ids.defs ids @ defs in
	if Ids.all_defined_in ids new_defs
	then (new_defs, y::rev_rr)
	else (defs, rev_rr))
      (defs,[]) rr rr_ids in
  let ll_rr = List.map fst ll_y_ids, List.rev rev_rr in
  (* computing views *)
  let views = views_of_seq [] 0 (list_of_ctx x ll_rr) in
  let selected_view = try List.find (top_sid_in_view (List.length (fst ll_rr))) views with _ -> assert false in
  ll_rr, selected_view

  
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

class annot ~focus_pos ~focus ?(ids : ids = Ids.empty) ?(seq_view : view option) ?(defined : bool = false) () =
object (self)
  val focus_pos : focus_pos = focus_pos
  val focus : focus = focus

  method focus = focus
  method focus_pos = focus_pos
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


(* unzipping and annotation *)

let rec annot_elt_p1 pos f ctx =
  let annot = new annot ~focus_pos:pos ~focus:(AtP1 (f,ctx)) () in
  let pos_down = focus_pos_down pos in
  match f with
  | Is (_,np) -> Is (annot,
		     annot_elt_s1 pos_down np (IsX ctx))
  | Type (_,c) -> Type (annot, c)
  | Rel(_,p,m,np) -> Rel (annot, p, m,
			  annot_elt_s1 pos_down np (RelX (p,m,ctx)))
  | Triple (_,arg,np1,np2) -> Triple (annot, arg,
				      annot_elt_s1 pos_down np1 (TripleX1 (arg,np2,ctx)),
				      annot_elt_s1 pos_down np2 (TripleX2 (arg,np1,ctx)))
  | Search (_,c) -> Search (annot, c)
  | Filter (_,c) -> Filter (annot, c)
  | And (_,lr) -> And (annot,
		       List.map
			 (fun (x,ll_rr) -> annot_elt_p1 pos_down x (AndX (ll_rr,ctx)))
			 (ctx_of_list lr))
  | Or (_,lr) -> Or (annot,
		     List.map
		       (fun (x,ll_rr) -> annot_elt_p1 pos_down x (OrX (ll_rr,ctx)))
		       (ctx_of_list lr))
  | Maybe (_,x) -> Maybe (annot,
			  annot_elt_p1 pos_down x (MaybeX ctx))
  | Not (_,x) -> Not (annot,
		      annot_elt_p1 pos_down x (NotX ctx))
  | IsThere _ -> IsThere annot
and annot_elt_p1_opt pos rel_opt ctx =
  match rel_opt with
  | None -> None
  | Some rel -> Some (annot_elt_p1 pos rel ctx)
and annot_elt_s1 pos np ctx =
  let annot = new annot ~focus_pos:pos ~focus:(AtS1 (np,ctx)) () in
  let pos_down = focus_pos_down pos in
  match np with
  | Det (_,det,rel_opt) -> Det (annot, det,
				annot_elt_p1_opt pos_down rel_opt (DetThatX (det,ctx)))
  | AnAggreg (_,id,modif,g,rel_opt,x) -> AnAggreg (annot, id, modif, g,
						   annot_elt_p1_opt pos_down rel_opt (AnAggregThatX (id,modif,g,x,ctx)),
						   annot_elt_s1 pos_down x (AnAggregX (id,modif,g,rel_opt,ctx)))
  | NAnd (_,lr) -> NAnd (annot,
			 List.map
			   (fun (x,ll_rr) -> annot_elt_s1 pos_down x (NAndX (ll_rr,ctx)))
			   (ctx_of_list lr))
  | NOr (_,lr) -> NOr (annot,
		       List.map
			 (fun (x,ll_rr) -> annot_elt_s1 pos_down x (NOrX (ll_rr,ctx)))
			 (ctx_of_list lr))
  | NMaybe (_,x) -> NMaybe (annot,
			    annot_elt_s1 pos_down x (NMaybeX ctx))
  | NNot (_,x) -> NNot (annot,
			annot_elt_s1 pos_down x (NNotX ctx))
and annot_elt_dim pos dim ctx =
  let annot = new annot ~focus_pos:pos ~focus:(AtDim (dim,ctx)) () in
  let pos_down = focus_pos_down pos in
  match dim with
  | Foreach (_,id,modif,rel_opt,id2) -> Foreach (annot, id, modif,
						 annot_elt_p1_opt pos_down rel_opt (ForeachThatX (id,modif,id2,ctx)),
						 id2)
and annot_elt_aggreg pos aggreg ctx =
  let annot = new annot ~focus_pos:pos ~focus:(AtAggreg (aggreg,ctx)) () in
  let pos_down = focus_pos_down pos in
  match aggreg with
  | TheAggreg (_,id,modif,g,rel_opt,id2) -> TheAggreg (annot, id, modif, g,
						       annot_elt_p1_opt pos_down rel_opt (TheAggregThatX (id,modif,g,id2,ctx)),
						       id2)
and annot_elt_expr pos expr ctx =
  let annot defined = new annot ~focus_pos:pos ~focus:(AtExpr (expr,ctx)) ~defined () in
  let pos_down = focus_pos_down pos in
  match expr with
  | Undef _ -> false, Undef (annot false)
  | Const (_,t) -> true, Const (annot true, t)
  | Var (_,id) -> true, Var (annot true, id) (* we assume 'id' is a valid reference *)
  | Apply (_,func,args) ->
    let l_defined, l_arg_annot =
      List.split
	(List.map
	   (fun (arg,ll_rr) -> annot_elt_expr pos_down arg (ApplyX (func, ll_rr, ctx)))
	   (ctx_of_list args)) in
    let defined = List.for_all (fun def -> def) l_defined in
    defined, Apply (annot defined, func, l_arg_annot)
and annot_elt_s pos s ctx =
  let ids = ids_elt_s s in
  let annot = new annot ~focus_pos:pos ~focus:(AtS (s,ctx)) ~ids () in
  let pos_down = focus_pos_down pos in
  match s with
  | Return (_,np) ->
    Return (annot,
	    annot_elt_s1 pos_down np (ReturnX ctx))
  | SAggreg (_,dims,aggregs) ->
    SAggreg (annot,
	     List.map
	       (fun (x,ll_rr) -> annot_elt_dim pos_down x (SAggregForeachX (ll_rr,aggregs,ctx)))
	       (ctx_of_list dims),
	     List.map
	       (fun (x,ll_rr) -> annot_elt_aggreg pos_down x (SAggregX (dims,ll_rr,ctx)))
	       (ctx_of_list aggregs))
  | SExpr (_,id,modif,expr,rel_opt) ->
    SExpr (annot, id,modif,
	   snd (annot_elt_expr pos_down expr (SExprX (id,modif,rel_opt,ctx))),
	   annot_elt_p1_opt pos_down rel_opt (SExprThatX (id,modif,expr,ctx)))
  | SFilter (_,id,expr) ->
    SFilter (annot, id,
	     snd (annot_elt_expr pos_down expr (SFilterX (id,ctx))))
  | Seq (_,lr) ->
    let lr, seq_view =
      match List.rev lr with
      | [] -> [], Unit
      | x::ll ->
	let ll_rr, seq_view = view_of_list_focus x (ll,[]) in
	list_of_ctx x ll_rr, seq_view in
    let annot = new annot ~focus_pos:pos ~focus:(AtS (s,ctx)) ~ids ~seq_view () in
    Seq (annot,
	 List.map
	   (fun (x,ll_rr) -> annot_elt_s pos_down x (SeqX (ll_rr,ctx)))
	   (ctx_of_list lr))

  
let rec annot_ctx_p1 ft_opt x_annot x = function
  | DetThatX (det, ctx) ->
    let ft = define_focus_term (focus_term_s2 det) ft_opt in
    let f = Det ((),det,Some x) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS1 (f,ctx)) () in
    annot_ctx_s1 (Some ft) (Det (annot, det, Some x_annot)) f ctx
  | AnAggregThatX (id,modif,g,np,ctx) ->
    let ft = define_focus_term (`IdNoIncr id) ft_opt in
    let f = AnAggreg ((),id,modif,g,Some x,np) in
    let annot = new annot ~focus_pos:(`Above (false, None)) ~focus:(AtS1 (f,ctx)) () in
    annot_ctx_s1 (Some ft)
      (AnAggreg (annot, id, modif, g, Some x_annot,
		 annot_elt_s1 (`Aside false) np (AnAggregX (id,modif,g,Some x,ctx))))
      f ctx
  | ForeachThatX (id,modif,id2,ctx) ->
    let ft = define_focus_term (`IdIncr id) ft_opt in
    let f = Foreach ((),id,modif,Some x,id2) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtDim (f,ctx)) () in
    annot_ctx_dim ft (Foreach (annot, id, modif, Some x_annot, id2)) f ctx
  | TheAggregThatX (id,modif,g,id2,ctx) ->
    let ft = define_focus_term (`IdNoIncr id) ft_opt in
    let f = TheAggreg ((),id,modif,g,Some x,id2) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtAggreg (f,ctx)) () in
    annot_ctx_aggreg ft (TheAggreg (annot, id, modif, g, Some x_annot, id2)) f ctx
  | SExprThatX (id,modif,expr,ctx) ->
    let ft = define_focus_term (`IdNoIncr id) ft_opt in
    let f = SExpr ((), id, modif, expr, Some x) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS (f,ctx)) () in
    annot_ctx_s ft (SExpr (annot, id, modif,
			   snd (annot_elt_expr (`Aside false) expr (SExprX (id,modif,Some x,ctx))),
			   Some x_annot)) f ctx
  | AndX (ll_rr,ctx) ->
    let f = And ((), list_of_ctx x ll_rr) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) () in
    annot_ctx_p1 ft_opt
      (And (annot,
	    list_of_ctx x_annot
	      (map_ctx_list
		 (fun (x2,ll_rr2) -> annot_elt_p1 (`Aside false) x2 (AndX (ll_rr2,ctx)))
		 (ctx_of_ctx_list x ll_rr))))
      f ctx
  | OrX ((ll,rr as ll_rr),ctx) -> (* alternative branches are suspended *)
    let f = Or ((), list_of_ctx x ll_rr) in
    let annot = new annot ~focus_pos:(`Above (true, Some (List.length ll))) ~focus:(AtP1 (f,ctx)) () in
    annot_ctx_p1 ft_opt
      (Or (annot,
	   list_of_ctx x_annot
	     (map_ctx_list
		(fun (x2,ll_rr2) -> annot_elt_p1 (`Aside true) x2 (OrX (ll_rr2,ctx)))
		(ctx_of_ctx_list x ll_rr))))
      f ctx
  | MaybeX ctx ->
    let f = Maybe ((),x) in
    let annot = new annot ~focus_pos:(`Above (true,None)) ~focus:(AtP1 (f,ctx)) () in (* suspended *)
    annot_ctx_p1 ft_opt (Maybe (annot, x_annot)) f ctx
  | NotX ctx ->
    let f = Not ((),x) in
    let annot = new annot ~focus_pos:(`Above (true,None)) ~focus:(AtP1 (f,ctx)) () in (* suspended *)
    annot_ctx_p1 ft_opt (Not (annot, x_annot)) f ctx
and annot_ctx_s1 ft_opt x_annot x = function
  | IsX ctx ->
    let f = Is ((),x) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) () in
    annot_ctx_p1 ft_opt (Is (annot, x_annot)) f ctx
  | RelX (p,modif,ctx) ->
    let ft = define_focus_term `Undefined ft_opt in
    let f = Rel ((),p,modif,x) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) () in
    annot_ctx_p1 (Some ft) (Rel (annot, p, modif, x_annot)) f ctx
  | TripleX1 (arg,np2,ctx) ->
    let ft = define_focus_term `Undefined ft_opt in
    let f = Triple ((),arg,x,np2) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) () in
    annot_ctx_p1 (Some ft)
      (Triple (annot, arg, x_annot,
	       annot_elt_s1 (`Aside false) np2 (TripleX2 (arg,x,ctx))))
      f ctx
  | TripleX2 (arg,np1,ctx) ->
    let ft = define_focus_term `Undefined ft_opt in
    let f = Triple ((),arg,np1,x) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtP1 (f,ctx)) () in
    annot_ctx_p1 (Some ft)
      (Triple (annot, arg,
	       annot_elt_s1 (`Aside false) np1 (TripleX1 (arg,x,ctx)), x_annot))
      f ctx
  | ReturnX ctx ->
    let ft = define_focus_term `Undefined ft_opt in
    let f = Return ((),x) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS (f,ctx)) ~ids:(ids_elt_s f) () in
    annot_ctx_s ft (Return (annot, x_annot)) f ctx
  | AnAggregX (id,modif,g,rel_opt,ctx) -> (* suspended *)
    let f = AnAggreg ((),id,modif,g,rel_opt,x) in
    let annot = new annot ~focus_pos:(`Above (true,None)) ~focus:(AtS1 (f,ctx)) () in
    annot_ctx_s1 ft_opt
      (AnAggreg (annot, id, modif, g,
		 annot_elt_p1_opt (`Aside true) rel_opt (AnAggregThatX (id,modif,g,x,ctx)),
		 x_annot))
      f ctx
  | NAndX (ll_rr,ctx) ->
    let f = NAnd ((), list_of_ctx x ll_rr) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS1 (f,ctx)) () in
    annot_ctx_s1 ft_opt
      (NAnd (annot,
	    list_of_ctx x_annot
	      (map_ctx_list
		 (fun (x2,ll_rr2) -> annot_elt_s1 (`Aside false) x2 (NAndX (ll_rr2,ctx)))
		 (ctx_of_ctx_list x ll_rr))))
      f ctx
  | NOrX ((ll,rr as ll_rr),ctx) -> (* alternative branches are suspended *)
    let f = NOr ((), list_of_ctx x ll_rr) in
    let annot = new annot ~focus_pos:(`Above (true, Some (List.length ll))) ~focus:(AtS1 (f,ctx)) () in
    annot_ctx_s1 ft_opt
      (NOr (annot,
	   list_of_ctx x_annot
	     (map_ctx_list
		(fun (x2,ll_rr2) -> annot_elt_s1 (`Aside true) x2 (NOrX (ll_rr2,ctx)))
		(ctx_of_ctx_list x ll_rr))))
      f ctx
  | NMaybeX ctx ->
    let f = NMaybe ((),x) in
    let annot = new annot ~focus_pos:(`Above (true,None)) ~focus:(AtS1 (f,ctx)) () in (* suspended *)
    annot_ctx_s1 ft_opt (NMaybe (annot, x_annot)) f ctx
  | NNotX ctx ->
    let f = NNot ((),x) in
    let annot = new annot ~focus_pos:(`Above (true,None)) ~focus:(AtS1 (f,ctx)) () in (* suspended *)
    annot_ctx_s1 ft_opt (NNot (annot, x_annot)) f ctx
and annot_ctx_dim ft x_annot x = function
  | SAggregForeachX (ll_rr,aggregs,ctx) ->
    let dims = list_of_ctx x ll_rr in
    let f = SAggreg ((),dims,aggregs) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS (f,ctx)) ~ids:(ids_elt_s f) () in
    annot_ctx_s ft
      (SAggreg (annot,
		list_of_ctx x_annot
		  (map_ctx_list
		     (fun (x2,ll_rr2) -> annot_elt_dim (`Aside false) x2 (SAggregForeachX (ll_rr2,aggregs,ctx)))
		     (ctx_of_ctx_list x ll_rr)),
		List.map
		  (fun (x2,ll_rr2) -> annot_elt_aggreg (`Aside false) x2 (SAggregX (dims,ll_rr2,ctx)))
		  (ctx_of_list aggregs)))
      f ctx
and annot_ctx_aggreg ft x_annot x = function
  | SAggregX (dims,ll_rr,ctx) ->
    let aggregs = list_of_ctx x ll_rr in
    let f = SAggreg ((),dims,aggregs) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS (f,ctx)) ~ids:(ids_elt_s f) () in
    annot_ctx_s ft
      (SAggreg (annot,
		List.map
		  (fun (x2,ll_rr2) -> annot_elt_dim (`Aside false) x2 (SAggregForeachX (ll_rr2,aggregs,ctx)))
		  (ctx_of_list dims),
		list_of_ctx x_annot
		  (map_ctx_list
		     (fun (x2,ll_rr2) -> annot_elt_aggreg (`Aside false) x2 (SAggregX (dims,ll_rr2,ctx)))
		     (ctx_of_ctx_list x ll_rr))))
      f ctx
and annot_ctx_expr defined x_annot x = function
(* 'defined' is about the sub-expression at focus *)
  | SExprX (id,modif,rel_opt,ctx) ->
    let f = SExpr ((),id,modif,x,rel_opt) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS (f,ctx)) ~ids:(ids_elt_s f) () in
    let ft = `IdNoIncr id in
    annot_ctx_s ft (SExpr (annot, id, modif, x_annot, annot_elt_p1_opt (`Aside false) rel_opt (SExprThatX (id,modif,x,ctx)))) f ctx
  | SFilterX (id,ctx) ->
    let f = SFilter ((),id,x) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS (f,ctx)) ~ids:(ids_elt_s f) () in
    let ft = `IdNoIncr id in
    annot_ctx_s ft (SFilter (annot, id, x_annot)) f ctx
  | ApplyX (func,ll_rr,ctx) ->
    let f = Apply ((), func, list_of_ctx x ll_rr) in
    let annot = new annot ~focus_pos:(`Above (true, Some (1 + List.length (fst ll_rr)))) ~focus:(AtExpr (f,ctx)) ~defined () in
    annot_ctx_expr defined
      (Apply (annot, func,
	      list_of_ctx x_annot
		(map_ctx_list
		   (fun (x2,ll_rr2) -> snd (annot_elt_expr (`Aside true) x2 (ApplyX (func, ll_rr2, ctx))))
		   (ctx_of_ctx_list x ll_rr))))
      f ctx
and annot_ctx_s ft x_annot x = function
  | Root -> ft, x_annot
  | SeqX (ll_rr,ctx) ->
    let ll_rr, seq_view = view_of_list_focus x ll_rr in
    let f = Seq ((), list_of_ctx x ll_rr) in
    let annot = new annot ~focus_pos:(`Above (false,None)) ~focus:(AtS (f,ctx)) ~seq_view () in
    annot_ctx_s ft
      (Seq (annot,
	    list_of_ctx x_annot
	      (map_ctx_list
		 (fun (x2,ll_rr2) -> annot_elt_s (`Aside false) x2 (SeqX (ll_rr2,ctx)))
		 (ctx_of_ctx_list x ll_rr))))
      f ctx

let annot_focus : focus -> focus_term * annot elt_s = function
  | AtP1 (f,ctx) ->
    let f_annot = annot_elt_p1 `At f ctx in
    annot_ctx_p1 None f_annot f ctx
  | AtS1 (np,ctx) ->
    let ft_opt =
      if is_s1_as_p1_ctx_s1 ctx
      then None
      else Some
	( match np with
	| Det (_,det,_) -> focus_term_s2 det
	| AnAggreg (_,id,_,g,_,_) -> `IdNoIncr id
	| _ -> `Undefined ) in
    let np_annot = annot_elt_s1 `At np ctx in
    annot_ctx_s1 ft_opt np_annot np ctx
  | AtDim (dim,ctx) ->
    let ft = match dim with Foreach (_,id,_,_,_) -> `IdIncr id in
    let dim_annot = annot_elt_dim `At dim ctx in
    annot_ctx_dim ft dim_annot dim ctx
  | AtAggreg (aggreg,ctx) ->
    let ft = match aggreg with TheAggreg (_,id,_,_,_,_) -> `IdNoIncr id in
    let aggreg_annot = annot_elt_aggreg `At aggreg ctx in
    annot_ctx_aggreg ft aggreg_annot aggreg ctx
  | AtExpr (expr,ctx) ->
    let defined, expr_annot = annot_elt_expr `At expr ctx in
    annot_ctx_expr defined expr_annot expr ctx
  | AtS (s,ctx) ->
    let ft = `Undefined in
    let s_annot = annot_elt_s `At s ctx in
    annot_ctx_s ft s_annot s ctx
