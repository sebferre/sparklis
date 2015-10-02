
open Jsutils
open Lisql
open Lisql_annot

(* translation from LISQL elts to SPARQL queries *)

(* SPARQL variable generator *)
class state (id_labelling : Lisql2nl.id_labelling) =
object (self)
  method id_labelling = id_labelling

  val mutable vars : Rdf.var list = []
  method add_var v = if not (List.mem v vars) then vars <- v::vars
  method vars = List.rev vars

  val h_var_aggreg : (Rdf.var, Rdf.var * aggreg * Sparql.formula) Hashtbl.t = Hashtbl.create 3
  method set_aggreg v aggreg : unit =
    Hashtbl.add h_var_aggreg v aggreg
  method aggreg v =
    try Some (Hashtbl.find h_var_aggreg v)
    with _ -> None

  val h_var_modif : (Rdf.var, modif_s2) Hashtbl.t = Hashtbl.create 13
  method set_modif (v : Rdf.var) (modif : modif_s2) : unit =
    Hashtbl.add h_var_modif v modif
  method modif (v : Rdf.var) =
    try Hashtbl.find h_var_modif v
    with _ -> (Select, Unordered)
  method project (v : Rdf.var) = fst (self#modif v)
  method order (v : Rdf.var) = snd (self#modif v)

end

  
let sparql_aggreg = function
  | NumberOf -> Sparql.DistinctCOUNT
  | ListOf -> Sparql.DistinctCONCAT
  | Total -> Sparql.SUM
  | Average -> Sparql.AVG
  | Maximum -> Sparql.MAX
  | Minimum -> Sparql.MIN
  | Sample -> Sparql.SAMPLE
  | Given -> Sparql.ID

let filter_constr_gen ~(label_property_lang : string * string) (t : Rdf.term) (c : constr) : Sparql.formula =
  (* both [label_prop] and [label_lang] may be the empty string, meaning undefined *)
  let label_prop, label_lang = label_property_lang in
  let label_wrapper make_filter =
    if label_prop = ""
    then make_filter t
    else
      let l = Rdf.Var "constr_label" in
      Sparql.formula_or_list
	[ make_filter t;
	  Sparql.formula_and_list
	    [ Sparql.Pattern (Sparql.triple t (Rdf.URI label_prop) l);
	      if label_lang = "" then Sparql.True else Sparql.Filter (Sparql.expr_regex (Sparql.expr_func "lang" [Sparql.term l]) label_lang);
	      make_filter l ] ] in
  match c with
    | True -> Sparql.True
    | MatchesAll [] -> Sparql.True
    | MatchesAll lpat ->
      label_wrapper (fun t ->
	Sparql.Filter
	  (Sparql.log_and
	     (List.map
		(fun pat -> Sparql.expr_regex (Sparql.expr_func "str" [Sparql.term t]) pat)
		lpat)))
    | MatchesAny [] -> Sparql.True
    | MatchesAny lpat ->
      label_wrapper (fun t ->
	Sparql.Filter
	  (Sparql.log_or
	     (List.map
		(fun pat -> Sparql.expr_regex (Sparql.expr_func "str" [Sparql.term t]) pat)
		lpat)))
    | After pat ->
      Sparql.Filter (Sparql.expr_comp ">=" (Sparql.expr_func "str" [Sparql.term t]) (Sparql.string pat))
    | Before pat ->
      Sparql.Filter (Sparql.expr_comp "<=" (Sparql.expr_func "str" [Sparql.term t]) (Sparql.string pat))
    | FromTo (pat1,pat2) ->
      Sparql.Filter
	(Sparql.log_and
	   [Sparql.expr_comp ">=" (Sparql.expr_func "str" [Sparql.term t]) (Sparql.string pat1);
	    Sparql.expr_comp "<=" (Sparql.expr_func "str" [Sparql.term t]) (Sparql.string pat2)])
    | HigherThan pat ->
      Sparql.Filter (Sparql.expr_comp ">=" (Sparql.term_numeric t) pat)
    | LowerThan pat ->
      Sparql.Filter (Sparql.expr_comp "<=" (Sparql.term_numeric t) pat)
    | Between (pat1,pat2) ->
      Sparql.Filter
	(Sparql.log_and
	   [Sparql.expr_comp ">=" (Sparql.term_numeric t) pat1;
	    Sparql.expr_comp "<=" (Sparql.term_numeric t) pat2])
    | HasLang pat ->
      Sparql.Filter
	(Sparql.log_and
	   [Sparql.expr_func "isLiteral" [Sparql.term t];
	    Sparql.expr_regex (Sparql.expr_func "lang" [Sparql.term t]) pat])
    | HasDatatype pat ->
      Sparql.Filter
	(Sparql.log_and
	   [Sparql.expr_func "isLiteral" [Sparql.term t];
	    Sparql.expr_regex (Sparql.expr_func "str" [Sparql.expr_func "datatype" [Sparql.term t]]) pat])

let filter_constr_entity t c = filter_constr_gen ~label_property_lang:Lexicon.config_entity_lexicon#property_lang t c
let filter_constr_class t c = filter_constr_gen ~label_property_lang:Lexicon.config_class_lexicon#property_lang t c
let filter_constr_property t c = filter_constr_gen ~label_property_lang:Lexicon.config_property_lexicon#property_lang t c


let search_constr (t : Rdf.term) (c : constr) : Sparql.formula =
  let l = Rdf.Var "search_label" in
  match c with
    | MatchesAll (w::lw) ->
      Sparql.formula_and_list
	[ Sparql.Pattern (Sparql.search_label t l);
	  Sparql.Pattern (Sparql.search_contains l w);
	  Sparql.Filter (Sparql.log_and (List.map (fun w -> Sparql.expr_regex (Sparql.term l) w) lw)) ]
    | MatchesAny lw ->
      Sparql.formula_or_list
	(List.map
	   (fun w ->
	     Sparql.formula_and_list
	       [Sparql.Pattern (Sparql.search_label t l);
		Sparql.Pattern (Sparql.search_contains l w)])
	   lw)
    | _ ->
      Sparql.Pattern (Sparql.something t)


let triple_arg arg x y z =
  Sparql.Pattern
    ( match arg with
      | S -> Sparql.triple x y z
      | P -> Sparql.triple y x z
      | O -> Sparql.triple y z x )

type sparql_p1 = Rdf.term -> Sparql.formula
type sparql_p2 = Rdf.term -> Rdf.term -> Sparql.formula
type sparql_s1 = sparql_p1 -> Sparql.formula
type sparql_s2 = sparql_p1 -> sparql_p1 -> Sparql.formula
type sparql_b1 = sparql_p2 -> Sparql.formula
type sparql_s = Sparql.formula


let rec form_p1 state : annot elt_p1 -> sparql_p1 = function
  | Is (annot,np) -> form_s1_as_p1 state np
  | Type (annot,c) -> (fun x -> Sparql.Pattern (Sparql.rdf_type x (Rdf.URI c)))
  | Rel (annot,p,m,np) ->
    let q_np = form_s1 state np in
    (fun x -> q_np (fun y ->
      let s, o = match m with Fwd -> x, y | Bwd -> y, x in
      Sparql.Pattern (Sparql.triple s (Rdf.URI p) o)))
  | Triple (annot,arg,np1,np2) ->
    let q_np1 = form_s1 state np1 in
    let q_np2 = form_s1 state np2 in
    (fun x -> q_np1 (fun y -> q_np2 (fun z -> triple_arg arg x y z)))
  | Search (annot,c) -> (fun x -> search_constr x c)
  | Filter (annot,c) -> (fun x -> filter_constr_entity x c)
  | And (annot,lr) ->
    let lr_d = List.map (fun elt -> form_p1 state elt) lr in
    (fun x -> Sparql.formula_and_list (List.map (fun d -> d x) lr_d))
  | Or (annot,lr) ->
    ( match annot#get_susp_focus_index with
    | Some i -> form_p1 state (List.nth lr i)
    | None ->
      let lr_d = List.map (fun elt -> form_p1 state elt) lr in
      (fun x -> Sparql.formula_or_list (List.map (fun d -> d x) lr_d)) )
  | Maybe (annot,f) ->
    if annot#is_susp_focus
    then form_p1 state f
    else
      let d = form_p1 state f in
      (fun x -> Sparql.formula_optional (d x))
  | Not (annot,f) ->
    if annot#is_susp_focus
    then form_p1 state f
    else
      let d = form_p1 (Oo.copy state) f in
      (fun x -> Sparql.formula_not (d x))
  | IsThere annot -> (fun x -> Sparql.True)
and form_p1_opt state = function
  | None -> (fun x -> Sparql.True)
  | Some rel -> form_p1 state rel
and form_s1_as_p1 state : annot elt_s1 -> sparql_p1 = function
  | Det (annot,det,rel_opt) ->
    let d1 = form_s2_as_p1 state det in
    let d2 = form_p1_opt state rel_opt in
    (fun x -> Sparql.formula_and (d1 x) (d2 x))
  | AnAggreg (annot,idg,modifg,g,relg_opt,np) ->
    if annot#is_susp_focus
    then form_s1_as_p1 state np
    else
      ( match np with
      | Det (_, An (id, _, _), _)
      | AnAggreg (_, id, _, _, _, _) ->
	form_aggreg_op state idg modifg g (form_p1_opt state relg_opt) id;
	form_s1_as_p1 state np
      | _ -> assert false )
  | NAnd (annot,lr) ->
    let lr_d = List.map (fun elt -> form_s1_as_p1 state elt) lr in
    (fun x -> Sparql.formula_and_list (List.map (fun d -> d x) lr_d))
  | NOr (annot,lr) ->
    ( match annot#get_susp_focus_index with
    | Some i -> form_s1_as_p1 state (List.nth lr i)
    | None ->
      let lr_d = List.map (fun elt -> form_s1_as_p1 state elt) lr in
      (fun x -> Sparql.formula_or_list (List.map (fun d -> d x) lr_d)) )
  | NMaybe (annot,f) ->
    if annot#is_susp_focus
    then form_s1_as_p1 state f
    else
      let d = form_s1_as_p1 state f in
      (fun x -> Sparql.formula_optional (d x))
  | NNot (annot,f) ->
    if annot#is_susp_focus
    then form_s1_as_p1 state f
    else
      let d = form_s1_as_p1 (Oo.copy state) f in
      (fun x -> Sparql.formula_not (d x))
and form_s2_as_p1 state : elt_s2 -> sparql_p1 = function
  | Term t ->
    (fun x -> Sparql.Filter (Sparql.expr_comp "=" (Sparql.term x) (Sparql.term t)))
(*    (fun x -> "BIND (" ^ Sparql.term t ^ " AS " ^ Sparql.term x ^ ")") *)
  | An (_id, _modif,head) ->
    let d_head =
      match head with
	| Thing -> (fun x -> Sparql.True)
	| Class c -> (fun x -> Sparql.Pattern (Sparql.rdf_type x (Rdf.URI c))) in
    d_head
  | The id ->
    (fun x ->
      let v = state#id_labelling#get_id_var id in
      let t = Rdf.Var v in
      Sparql.Filter (Sparql.expr_comp "=" (Sparql.term x) (Sparql.term t)))    
and form_s1 state : annot elt_s1 -> sparql_s1 = function
  | Det (annot,det,rel_opt) ->
    let qu = form_s2 state det in
    let d1 = form_p1_opt state rel_opt in
    (fun d -> qu d1 d)
  | AnAggreg (annot,idg,modifg,g,relg_opt,np) ->
    if annot#is_susp_focus
    then form_s1 state np
    else
      ( match np with
      | Det (_, An (id, _, _), _)
      | AnAggreg (_, id, _, _, _, _) ->
	form_aggreg_op state idg modifg g (form_p1_opt state relg_opt) id;
	form_s1 state np
      | _ -> assert false )
  | NAnd (annot,lr) ->
    let lr_q = List.map (fun elt -> form_s1 state elt) lr in
    (fun d -> Sparql.formula_and_list (List.map (fun q -> q d) lr_q))
  | NOr (annot,lr) ->
    ( match annot#get_susp_focus_index with
    | Some i -> form_s1 state (List.nth lr i)
    | None ->
      let lr_q = List.map (fun elt -> form_s1 state elt) lr in
      (fun d -> Sparql.formula_or_list (List.map (fun q -> q d) lr_q)) )
  | NMaybe (annot,f) ->
    if annot#is_susp_focus
    then form_s1 state f
    else
      let q = form_s1 state f in
      (fun d -> Sparql.formula_optional (q d))
  | NNot (annot,f) ->
    if annot#is_susp_focus
    then form_s1 state f
    else
      let q = form_s1 (Oo.copy state) f in
      (fun d -> Sparql.formula_not (q d))
(*      
  | NRelax f ->
    state#set_relax true;
    let q = form_s1 state f in
    state#set_relax false;
    q
*)
and form_s2 state : elt_s2 -> sparql_s2 = function
  | Term t -> (fun d1 d2 -> Sparql.formula_and (d1 t) (d2 t))
  | An (id, modif, head) ->
    let qhead = form_head state head in
    let v = state#id_labelling#get_id_var id in
    state#set_modif v modif;
    let t = Rdf.Var v in
    (fun d1 d2 -> state#add_var v; qhead t (Sparql.formula_and (d2 t) (d1 t))) (* YES: d2 - d1 *)
  | The id ->
    let v = state#id_labelling#get_id_var id in
    let t = Rdf.Var v in
    (fun d1 d2 -> Sparql.formula_and (d2 t) (d1 t)) (* YES: d2 - s1 *)
and form_head state : elt_head -> (Rdf.term -> Sparql.formula -> Sparql.formula) = function
  | Thing ->
    (fun x form -> Sparql.formula_bind x form)
  | Class c ->
    (fun x form -> Sparql.formula_and (Sparql.Pattern (Sparql.rdf_type x (Rdf.URI c))) form)
and form_aggreg_op state idg modifg g (d : sparql_p1) id : unit =
  let vg = state#id_labelling#get_id_var idg in
  let v = state#id_labelling#get_id_var id in
  state#set_aggreg v (vg, g, (d (Rdf.Var vg)));
  state#set_modif vg modifg
and form_dim state : annot elt_dim -> Sparql.projection * Rdf.var (* group by var *) * Sparql.formula (* relative *) = function
  | Foreach (annot,id,modif,rel_opt,id2) ->
    let v = state#id_labelling#get_id_var id in
    state#set_modif v modif;
    let d = form_p1_opt state rel_opt in
    let v2 = state#id_labelling#get_id_var id2 in
    (`Expr (Sparql.var v2), v), v2, (d (Rdf.Var v))
and form_aggreg state : annot elt_aggreg -> Sparql.projection * Sparql.expr (* having expr *) = function
  | TheAggreg (annot,id,modif,g,rel_opt,id2) ->
    let v = state#id_labelling#get_id_var id in
    state#set_modif v modif;
    let d = form_p1_opt state rel_opt in
    let v2 = state#id_labelling#get_id_var id2 in
    (`Aggreg (sparql_aggreg g, v2), v), Sparql.expr_of_formula (d (Rdf.Var v))
and form_expr state : annot elt_expr -> Sparql.expr = function
  | Undef annot -> ""
  | Const (annot,t) -> Sparql.term t
  | Var (annot,id) -> Sparql.var (state#id_labelling#get_id_var id)
  | Apply (annot,func,args) ->
    if not annot#defined
    then ""
    else
      ( match annot#focus_pos with
      | `Above (true, Some pos) -> form_expr state (List.nth args (pos-1))
      | _ ->
	let sparql_args = List.map (fun arg -> form_expr state arg) args in
	( match func with
	| `Add -> Sparql.expr_infix "+" sparql_args
	| `Sub -> Sparql.expr_infix "-" sparql_args
	| `Mul -> Sparql.expr_infix "*" sparql_args
	| `Div -> Sparql.expr_infix "/" sparql_args
	| `Strlen -> Sparql.expr_func "strlen" sparql_args
	| `Now -> Sparql.expr_func "now" [] ) )
and find_defining_views state (ids : ids) (views : Sparql.view list) : Rdf.var list * Rdf.var list * Sparql.view list * Sparql.view list =
  let refs = List.map state#id_labelling#get_id_var (Ids.refs ids) in
  let defs = List.map state#id_labelling#get_id_var (Ids.defs ids) in
  let defining_views, other_views =
    List.partition
      (fun (defs_i,form_i) -> List.exists (fun id -> List.mem id refs) defs_i)
      views in
  defs, refs, defining_views, other_views
and form_s state ?(views : Sparql.view list = []) : annot elt_s -> Rdf.var list (* available defs *) * Sparql.view list = function
  | Return (annot,np) ->
    let defs, refs, defining_views, other_views = find_defining_views state annot#ids views in
    let form = form_s1 state np (fun t -> Sparql.True) in
    [], Sparql.join_views (defining_views @ [(defs, (fun ?limit () -> form))]) :: other_views
  | SAggreg (annot,dims,aggregs) ->
    let defs, refs, defining_views, other_views = find_defining_views state annot#ids views in
    let (aggregated_defs, aggregated_f) = Sparql.join_views defining_views in
    let available_defs = List.filter (fun v -> not (List.mem v refs)) aggregated_defs in
    let l_dims = List.map (form_dim state) dims in
    let l_aggregs = List.map (form_aggreg state) aggregs in
    let projections_dims = List.map (fun (proj,_,_) -> proj) l_dims in
    let projections_aggregs = List.map fst l_aggregs in
    let groupings_dims = List.map (fun (_,group,_) -> group) l_dims in
    let lf_dims = List.map (fun (_,_,hav) -> hav) l_dims in
    let havings_aggregs = List.map snd l_aggregs in
    let f_aggreg =
      fun ?limit () ->
	Sparql.Subquery
	  { Sparql.projections = projections_dims @ projections_aggregs;
	    pattern = Sparql.pattern_of_formula (aggregated_f ?limit:(match limit with None -> None | Some l -> Some (10*l)) ());
	    groupings = groupings_dims;
	    having = Sparql.log_and havings_aggregs;
	    limit;
	  } in
    let f =
      fun ?limit () ->
	Sparql.formula_and_list (f_aggreg ?limit () :: lf_dims) in
    available_defs, (defs,f) :: views (* adding aggregation on top of defining query *)
  | SExpr (annot,id,modif,expr,rel_opt) ->
    let v = state#id_labelling#get_id_var id in
    state#set_modif v modif;
    let sparql_expr =
      match form_expr state expr with
      | "" -> "\"?\""
      | s -> s in
    let d = form_p1_opt state rel_opt in
    let form = Sparql.formula_and (Sparql.Pattern (Sparql.bind sparql_expr v)) (d (Rdf.Var v)) in
    let defs, refs, defining_views, other_views = find_defining_views state annot#ids views in
    [], Sparql.join_views (defining_views @ [([v], (fun ?limit () -> form))]) :: other_views
  | Seq (annot,lr) ->
    let seq_ids = match annot#seq_ids with Some x -> x | None -> assert false in
    List.fold_left2
      (fun (available_defs,views) ids_opt s ->
	if ids_opt = None
	then (available_defs,views)
	else form_s state ~views s)
      ([],views) seq_ids lr

(* 
and form_s state ?(defining : Lisql.id list * Sparql.formula = [], Sparql.True) ?(defs : Lisql.id list = []) : annot elt_s -> bool * Sparql.formula =
  let defining_defs, defining_form = defining in
  function
  | Return (annot,np) ->
    let q = form_s1 state np in
    let f = q (fun t -> Sparql.True) in
    true, (defining_defs @ defs, Sparql.formula_and defining_form f) (* extending defining query *)
  | SAggreg (annot,dims,aggregs) ->
    let l_dims = List.map (form_dim state) dims in
    let l_aggregs = List.map (form_aggreg state) aggregs in
    let projections_dims = List.map (fun (proj,_,_) -> proj) l_dims in
    let projections_aggregs = List.map fst l_aggregs in
    let groupings = List.map (fun (_,group,_) -> group) l_dims in
    let havings_dims = List.map (fun (_,_,hav) -> hav) l_dims in
    let havings_aggregs = List.map snd l_aggregs in
    let f = Sparql.Subquery
      { projections = projections_dims @ projections_aggregs;
	pattern = Sparql.pattern_of_formula defining_form;
	groupings;
	having = Sparql.log_and (havings_dims @ havings_aggregs);
      } in
    false, (defs, f) (* adding aggregation on top of defining query *)
  | Seq (annot,lr) ->
    ( match annot#seq_ids with
    | Some seq_ids ->
      let list_defs_form =
	List.fold_left2
	  (fun list_defs_form ids_opt s ->
	    match ids_opt with
	    | None -> list_defs_form
	    | Some ids ->
	      let refs = Ids.keys_of_val `Ref ids in
	      let defs = Ids.keys_of_val `Def ids in
	      let list_defining_defs_form, list_other_defs_form =
		List.partition (fun (defs_i,form_i) -> List.exists (fun id -> List.mem id refs) defs_i) list_defs_form in
	      let list_defining_defs, list_defining_form = List.split defining_defs_forms in
	      let defining_defs_form = List.concat list_defining_defs, Sparql.formula_and_list list_defining_form in
	      let new_defs_form, replace = form_s state ~defining:defining_defs_form ~defs s in
	      (*let new_defs_form = List.concat (defs::defining_defs), Sparql.formula_and_list (f::defining_forms) in *)
	      new_defs_form :: (if replace then other_defs_forms else list_defs_form))
	  [] seq_ids lr in
      ( match list_defs_forms with
      | (defs,form)::_ -> true, (defs,form) (* returning most recent formula *)
      | _ -> assert false )
    | None -> assert false )
*)
(*      
    let lr_f = List.map (fun elt -> form_s state elt) lr in
    Sparql.formula_and_list lr_f
*)

type template = ?constr:constr -> limit:int -> string

(*  
let rec var_aggregation_stack state v acc =
  match state#aggreg v with
  | None -> acc
  | Some (vg,g,f) -> var_aggregation_stack state vg (`Aggreg (vg,g,f,v,acc))

let rec transpose_aggregation_stacks t_list var_stacks acc =
  let l2 =
    List.map
      (function
      | `Var v -> (v,`Dim, List.mem (Rdf.Var v) t_list), `VarEcho v
      | `VarEcho v -> (v, `Dim, false), `VarEcho v (* at_focus is not propagated to subqueries *)
      | `Aggreg (v,g,f,vi, st) -> (v, `Aggreg (g,vi,f), List.mem (Rdf.Var v) t_list), st)
      var_stacks in
  let layer, substacks = List.split l2 in
  let acc =
    if List.exists (fun (v,_,at_focus) -> at_focus) layer
    then [] (* layers above focus are ignored *)
    else acc in
  if List.for_all (function (v,`Dim,_) -> true | _ -> false) layer
  then
    if acc = []
    then [layer]
    else acc (* because in that case, no additional nested query is necessary *)
  else transpose_aggregation_stacks t_list substacks (layer::acc)

let make_select state t_list ~is_subquery dims_aggregs form =
  let projections, groupings, havings, ordering =
    List.fold_right
      (fun (v,kind,at_focus) (projs,groups,havings,ordering) ->
	let projs, groups, havings, order, v_order = (* v_order is to be used in ordering *)
	  match state#modif v with
	  | (Unselect, _) when not at_focus && not is_subquery -> projs, groups, havings, Unordered, v
	    | (_, order) ->
	      match kind with
	      | `Dim -> (`Bare, v)::projs, v::groups, havings, order, v
	      | `Aggreg (Lisql.Given,vi,f) -> (`Aggreg (sparql_aggreg Lisql.Given,vi),v)::projs, vi::groups, f::havings, order, v
	      | `Aggreg (g,vi,f) -> (`Aggreg (sparql_aggreg g,vi),v)::projs, groups, f::havings, order, v in
	let ordering =
	  match order with
	  | Unordered -> ordering
	  | Lowest -> (Sparql.ASC, v_order) :: ordering
	  | Highest -> (Sparql.DESC, v_order) :: ordering in
	projs, groups, havings, ordering)
      dims_aggregs ([],[],[],[]) in
  let having = Sparql.expr_of_formula (Sparql.formula_and_list havings) in
  (fun ?(constr=True) ~limit ->
    Sparql.select ~distinct:true ~projections ~groupings ~having ~ordering ~limit
      (Sparql.pattern_of_formula
	 (match t_list with [t] -> Sparql.formula_and form (filter_constr_entity t constr) | _ -> form)))

let make_query state t_list form =
  let lv = state#vars in
  let var_aggreg_stacks = List.map (fun v -> var_aggregation_stack state v (`Var v)) lv in
  let select_layers_outward = transpose_aggregation_stacks t_list var_aggreg_stacks [] in
  match select_layers_outward with
  | [] -> assert false
  | layer::layers ->
    let depth = List.length layers in
    let d, select_query =
      List.fold_left
	(fun (d,select_query) layer ->
	  d-1,
	  (fun ?constr ~limit ->
	    make_select state t_list ~is_subquery:(d-1 > 0)
	      layer
	      (Sparql.Pattern (Sparql.subquery (select_query ?constr ~limit:(10*limit))))
	      ?constr ~limit))
	(depth, make_select state t_list ~is_subquery:(depth > 0) layer form)
	layers in
    select_query
*)
      
let make_query state t_list (defs, f : Sparql.view) : template =
  let visible_defs =
    List.filter
      (fun v -> state#project v = Select || List.mem (Rdf.Var v) t_list)
      defs in
  let ordering =
    List.fold_right
      (fun v ordering ->
	match state#order v with
	| Unordered -> ordering
	| Lowest -> (Sparql.ASC, v) :: ordering
	| Highest -> (Sparql.DESC, v) :: ordering)
      defs [] in
  (fun ?constr ~limit ->
    let f_constr =
      fun ?limit () ->
	match t_list, constr with
	| [(Rdf.Var _ as t)], Some c -> Sparql.formula_and (f ?limit ()) (filter_constr_entity t c)
	| _ -> f ?limit () in
    Sparql.query_of_view ~distinct:true ~ordering ~limit (visible_defs, f_constr))

      
let s_annot (id_labelling : Lisql2nl.id_labelling) (ft : focus_term) (s_annot : annot elt_s)
    : Rdf.term list * template option * template option * template option * template option * Rdf.var list =
  let state = new state id_labelling in
  let available_defs, views = form_s state s_annot in
  let (defs, f as view) = try List.hd views with _ -> Sparql.empty_view in
  let t_list =
    match ft with
    | `Term t -> [t]
    | `IdIncr id | `IdNoIncr id -> [Rdf.Var (id_labelling#get_id_var id)]
    | `Undefined -> [] in
  let query_opt =
    if f () = Sparql.True
    then None
    else Some (make_query state t_list view) in
  let query_incr_opt x filter_constr triple =
    match ft, t_list with
      | `IdNoIncr _, _ -> None (* no increments for this focus term (aggregations) *)
      | _, [t] ->
	let tx = Rdf.Var x in
	Some (fun ?(constr=True) ~limit ->
	  let form_x =
	    match t with
	    | Rdf.Var _
	    | Rdf.Bnode _ -> Sparql.formula_and (f ~limit ()) (triple t tx)
	    | _ -> triple t tx in
	  Sparql.select ~projections:[(`Bare,x)] ~limit
	    (Sparql.pattern_of_formula
	       (Sparql.formula_and form_x (filter_constr tx constr))))
      | _ -> None in
  let query_class_opt = query_incr_opt "class" filter_constr_class (fun t tc -> Sparql.Pattern (Sparql.rdf_type t tc)) in
  let query_prop_has_opt = query_incr_opt "prop" filter_constr_property (fun t tp -> Sparql.Pattern (Sparql.triple t tp (Rdf.Bnode ""))) in
  let query_prop_isof_opt = query_incr_opt "prop" filter_constr_property (fun t tp -> Sparql.Pattern (Sparql.triple (Rdf.Bnode "") tp t)) in
  t_list, query_opt, query_class_opt, query_prop_has_opt, query_prop_isof_opt, available_defs
