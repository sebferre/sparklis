
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
	      if label_lang = "" then Sparql.True else Sparql.Filter (Sparql.expr_regex (Sparql.expr_func "lang" (Sparql.term l)) label_lang);
	      make_filter l ] ] in
  match c with
    | True -> Sparql.True
    | MatchesAll [] -> Sparql.True
    | MatchesAll lpat ->
      label_wrapper (fun t ->
	Sparql.Filter
	  (Sparql.log_and
	     (List.map
		(fun pat -> Sparql.expr_regex (Sparql.expr_func "str" (Sparql.term t)) pat)
		lpat)))
    | MatchesAny [] -> Sparql.True
    | MatchesAny lpat ->
      label_wrapper (fun t ->
	Sparql.Filter
	  (Sparql.log_or
	     (List.map
		(fun pat -> Sparql.expr_regex (Sparql.expr_func "str" (Sparql.term t)) pat)
		lpat)))
    | After pat ->
      Sparql.Filter (Sparql.expr_comp ">=" (Sparql.expr_func "str" (Sparql.term t)) (Sparql.string pat))
    | Before pat ->
      Sparql.Filter (Sparql.expr_comp "<=" (Sparql.expr_func "str" (Sparql.term t)) (Sparql.string pat))
    | FromTo (pat1,pat2) ->
      Sparql.Filter
	(Sparql.log_and
	   [Sparql.expr_comp ">=" (Sparql.expr_func "str" (Sparql.term t)) (Sparql.string pat1);
	    Sparql.expr_comp "<=" (Sparql.expr_func "str" (Sparql.term t)) (Sparql.string pat2)])
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
	   [Sparql.expr_func "isLiteral" (Sparql.term t);
	    Sparql.expr_regex (Sparql.expr_func "lang" (Sparql.term t)) pat])
    | HasDatatype pat ->
      Sparql.Filter
	(Sparql.log_and
	   [Sparql.expr_func "isLiteral" (Sparql.term t);
	    Sparql.expr_regex (Sparql.expr_func "str" (Sparql.expr_func "datatype" (Sparql.term t))) pat])

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
	form_aggreg state idg modifg g (form_p1_opt state relg_opt) id;
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
	form_aggreg state idg modifg g (form_p1_opt state relg_opt) id;
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
and form_aggreg state idg modifg g (d : sparql_p1) id : unit =
  let vg = state#id_labelling#get_id_var idg in
  let v = state#id_labelling#get_id_var id in
  state#set_aggreg v (vg, g, (d (Rdf.Var vg)));
  state#set_modif vg modifg
and form_s state : annot elt_s -> Sparql.formula = function
  | Return (annot,np) ->
    let q = form_s1 state np in
    q (fun t -> Sparql.True)
  | Seq (annot,lr) ->
    let lr_f = List.map (fun elt -> form_s state elt) lr in
    Sparql.formula_and_list lr_f


type template = ?constr:constr -> limit:int -> string

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
  let projections, aggregations, groupings, havings, ordering =
    List.fold_right
      (fun (v,kind,at_focus) (projs,aggregs,groups,havings,ordering) ->
	let projs, aggregs, groups, havings, order, v_order = (* v_order is to be used in ordering *)
	  match state#modif v with
	  | (Unselect, _) when not at_focus && not is_subquery -> projs, aggregs, groups, havings, Unordered, v
	    | (_, order) ->
	      match kind with
	      | `Dim -> v::projs, aggregs, v::groups, havings, order, v
	      | `Aggreg (Lisql.Given,vi,f) -> projs, (sparql_aggreg Lisql.Given,vi,v)::aggregs, vi::groups, f::havings, order, v
	      | `Aggreg (g,vi,f) -> projs, (sparql_aggreg g,vi,v)::aggregs, groups, f::havings, order, v in
	let ordering =
	  match order with
	  | Unordered -> ordering
	  | Lowest -> (Sparql.ASC, v_order) :: ordering
	  | Highest -> (Sparql.DESC, v_order) :: ordering in
	projs, aggregs, groups, havings, ordering)
      dims_aggregs ([],[],[],[],[]) in
  let having = Sparql.expr_of_formula (Sparql.formula_and_list havings) in
  (fun ?(constr=True) ~limit ->
    Sparql.select ~distinct:true ~projections ~aggregations ~groupings ~having ~ordering ~limit
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

      
let s_annot (id_labelling : Lisql2nl.id_labelling) (ft : focus_term) (s_annot : annot elt_s)
    : Rdf.term list * template option * template option * template option * template option =
  let state = new state id_labelling in
  let form = form_s state s_annot in
  let t_list =
    match ft with
    | `Term t -> [t]
    | `IdIncr id | `IdNoIncr id -> [Rdf.Var (id_labelling#get_id_var id)]
    | `Undefined -> [] in
  let query_opt =
    if form = Sparql.True
    then None
    else Some (make_query state t_list form) in
  let query_incr_opt x filter_constr triple =
    match ft, t_list with
      | `IdNoIncr _, _ -> None (* no increments for this focus term (aggregations) *)
      | _, [t] ->
	let tx = Rdf.Var x in
	let form_x =
	  match t with
	    | Rdf.Var _
	    | Rdf.Bnode _ -> Sparql.formula_and form (triple t tx)
	    | _ -> triple t tx in
	Some (fun ?(constr=True) ~limit ->
	  Sparql.select ~projections:[x] ~limit
	    (Sparql.pattern_of_formula
	       (Sparql.formula_and form_x (filter_constr tx constr))))
      | _ -> None in
  let query_class_opt = query_incr_opt "class" filter_constr_class (fun t tc -> Sparql.Pattern (Sparql.rdf_type t tc)) in
  let query_prop_has_opt = query_incr_opt "prop" filter_constr_property (fun t tp -> Sparql.Pattern (Sparql.triple t tp (Rdf.Bnode ""))) in
  let query_prop_isof_opt = query_incr_opt "prop" filter_constr_property (fun t tp -> Sparql.Pattern (Sparql.triple (Rdf.Bnode "") tp t)) in
  t_list, query_opt, query_class_opt, query_prop_has_opt, query_prop_isof_opt
