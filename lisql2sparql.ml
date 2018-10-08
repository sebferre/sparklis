(*
  Copyright 2013-2017 Sébastien Ferré, IRISA, Université de Rennes 1

  This file is part of Sparklis.
*)

open Jsutils
open Lisql
open Lisql_annot

(* configs *)

let config_fulltext_search = new Config.select_input ~key:"fulltext_search" ~select_selector:"#input-fulltext-search-select" ~default:"regex" ()
       
(* translation from LISQL elts to SPARQL queries *)

(* SPARQL variable generator *)
class genvar =
object
  val h_varprefix_cpt : (string, int ref) Hashtbl.t = Hashtbl.create 7
  method new_var (prefix : string) : string =
    let cpt =
      try Hashtbl.find h_varprefix_cpt prefix
      with Not_found ->
	let cpt = ref 0 in
	Hashtbl.add h_varprefix_cpt prefix cpt;
	cpt in
    incr cpt;
    prefix ^ string_of_int !cpt
end
       
(* SPARQL generation state *)
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

  val mutable geolocs : (Sparql.term * (Rdf.var * Rdf.var)) list = []
  method add_geoloc (t : Sparql.term) (v_lat : Rdf.var) (v_long : Rdf.var) : unit =
    geolocs <- (t,(v_lat,v_long))::geolocs
  method geolocs = geolocs

  val gv = new genvar
  method genvar = gv
end

(* assuming only few variables are created with same prefix in a given query *)
(*let random_sparql_var prefix : Sparql.var = Sparql.var (prefix ^ string_of_int (Random.int 1000))*)
  
let sparql_converter (conv_opt : num_conv option) : Sparql.converter =
  match conv_opt with
  | None -> (fun e -> e)
  | Some (conv,b) ->
    let func_conv =
      match conv with
      | `Integer -> "xsd:integer"
      | `Decimal -> "xsd:decimal"
      | `Double -> "xsd:double" in
    (fun e ->
      Sparql.expr_func func_conv
	[ if b
	  then Sparql.expr_func "str" [e]
	  else e ])
  
let sparql_aggreg = function
  | NumberOf -> Sparql.DistinctCOUNT
  | ListOf -> Sparql.DistinctCONCAT
  | Sample -> Sparql.SAMPLE
  | Total conv_opt -> Sparql.SUM (sparql_converter conv_opt)
  | Average conv_opt -> Sparql.AVG (sparql_converter conv_opt)
  | Maximum conv_opt -> Sparql.MAX (sparql_converter conv_opt)
  | Minimum conv_opt -> Sparql.MIN (sparql_converter conv_opt)

let sparql_order = function
  | Unordered -> None
  | Lowest conv_opt -> Some (Sparql.ASC (sparql_converter conv_opt))
  | Highest conv_opt -> Some (Sparql.DESC (sparql_converter conv_opt))

type filter_context = [`Properties|`Terms] * [`Bind|`Filter]
			     
let filter_kwds_gen (ctx : filter_context) (gv : genvar) ~(label_properties_langs : string list * string list) (t : _ Sparql.any_term) ~(op : [`All|`Any]) ~(kwds : string list) : bool * Sparql.formula =
  let label_props, label_langs = label_properties_langs in
  let log_op =
    match op with
    | `All -> Sparql.log_and
    | `Any -> Sparql.log_or in
  let make_filter (e : _ Sparql.any_expr) : Sparql.formula =
    Sparql.Filter
      (log_op
	 (List.map
	    (fun pat -> Sparql.expr_regex (Sparql.expr_func "str" [e]) pat)
	    kwds)) in
  let str_filter =
    make_filter t in
  let label_filter_opt =
    match config_fulltext_search#value, ctx with
    | "text:query", _ ->
       let terms =
	 Common.mapfilter
	   (fun kwd ->
	    let n = String.length kwd in
	    if n < 3 then None
	    else if kwd.[n-1] = '~' then Some kwd
	    else Some (kwd ^ "*"))
	   kwds in
       let lucene_query =
	 let sep = match op with `All -> " AND " | `Any -> " OR " in
	 match terms with
	 | [] -> ""
	 | [term] -> term
	 | _ -> "(" ^ String.concat sep terms ^ ")" in
       let _ = firebug ("Lucene query: " ^ lucene_query) in
       if lucene_query = ""
       then `NoFilter
       else `Filter (Sparql.Pattern (Sparql.text_query t lucene_query))
    | "bif:contains", (`Terms,`Bind) -> (* only efficient in this context *)
       if label_props = []
       then `Undefined
       else
	 let terms =
	   Common.mapfilter
	     (fun kwd ->
	      let n = String.length kwd in
	      if n < 4 then None
	      else Some ("'" ^ kwd ^ "*'"))
	     kwds in
	 let sql_query =
	   let sep = match op with `All -> " AND " | `Any -> " OR " in
	   match terms with
	   | [] -> ""
	   | [term] -> term
	   | _ -> String.concat sep terms in
	 let _ = firebug ("SQL full-text query: " ^ sql_query) in
	 if sql_query = ""
	 then `NoFilter
	 else
	   let open Sparql in
	   let term_l = var (gv#new_var "constr_label") in
	   `Filter (formula_and_list
		      [ Pattern (triple t (path_alt (List.map uri label_props :> pred list)) term_l);
		     (if label_langs = []
		      then True
		      else Filter (expr_in (expr_func "lang" [term_l]) (List.map string label_langs)));
		     Pattern (bif_contains term_l sql_query) ])
    | _ -> (* using REGEX *)
       if label_props = []
       then `Undefined
       else
	 let open Sparql in
	 let term_l = var (gv#new_var "constr_label") in
	 `Filter (formula_and_list
		 [ Pattern (triple t (path_alt (List.map uri label_props :> pred list)) term_l);
		   (if label_langs = []
		    then True
		    else Filter (expr_in (expr_func "lang" [term_l]) (List.map string label_langs)));
		   make_filter term_l ])
  in
  let binding, f =
    match label_filter_opt with
    | `Undefined -> false, str_filter
    | `NoFilter -> false, Sparql.True (* kwds not specific enough *)
    | `Filter label_filter ->
       true,
       Sparql.formula_or_list (* TODO: avoid this OR, choose from focus type (URI vs literal) *)
	 [ str_filter;
	   label_filter ] in
  binding, f

let filter_constr_gen (ctx : filter_context) (gv : genvar) ~(label_properties_langs : string list * string list) (t : _ Sparql.any_term) (c : constr) : Sparql.formula =
  (* both [label_properties] and [label_langs] may be the empty list, meaning undefined *)
  match c with
    | True -> Sparql.True
    | MatchesAll [] -> Sparql.True
    | MatchesAll lpat ->
       snd (filter_kwds_gen ctx gv ~label_properties_langs t ~op:`All ~kwds:lpat)
    | MatchesAny [] -> Sparql.True
    | MatchesAny lpat ->
       snd (filter_kwds_gen ctx gv ~label_properties_langs t ~op:`Any ~kwds:lpat)
    | After pat ->
      Sparql.Filter (Sparql.expr_comp ">=" (Sparql.expr_func "str" [t]) (Sparql.string pat))
    | Before pat ->
      Sparql.Filter (Sparql.expr_comp "<=" (Sparql.expr_func "str" [t]) (Sparql.string pat))
    | FromTo (pat1,pat2) ->
      Sparql.Filter
	(Sparql.log_and
	   [Sparql.expr_comp ">=" (Sparql.expr_func "str" [t]) (Sparql.string pat1);
	    Sparql.expr_comp "<=" (Sparql.expr_func "str" [t]) (Sparql.string pat2)])
    | HigherThan pat ->
      Sparql.Filter (Sparql.expr_comp ">=" (Sparql.conv_numeric t) (Sparql.sparql pat))
    | LowerThan pat ->
      Sparql.Filter (Sparql.expr_comp "<=" (Sparql.conv_numeric t) (Sparql.sparql pat))
    | Between (pat1,pat2) ->
      Sparql.Filter
	(Sparql.log_and
	   [Sparql.expr_comp ">=" (Sparql.conv_numeric t) (Sparql.sparql pat1);
	    Sparql.expr_comp "<=" (Sparql.conv_numeric t) (Sparql.sparql pat2)])
    | HasLang pat ->
      Sparql.Filter
	(Sparql.log_and
	   [Sparql.expr_func "isLiteral" [t];
	    Sparql.expr_regex (Sparql.expr_func "lang" [t]) pat])
    | HasDatatype pat ->
      Sparql.Filter
	(Sparql.log_and
	   [Sparql.expr_func "isLiteral" [t];
	    Sparql.expr_regex (Sparql.expr_func "str" [Sparql.expr_func "datatype" [t]]) pat])

let filter_constr_entity gv t c = filter_constr_gen (`Terms,`Filter) gv ~label_properties_langs:Lexicon.config_entity_lexicon#properties_langs t c
let filter_constr_class gv t c = filter_constr_gen (`Properties,`Filter) gv ~label_properties_langs:Lexicon.config_class_lexicon#properties_langs t c
let filter_constr_property gv t c = filter_constr_gen (`Properties,`Filter) gv ~label_properties_langs:Lexicon.config_property_lexicon#properties_langs t c

let search_constr_entity (gv : genvar) (t : _ Sparql.any_term) (c : constr) : Sparql.formula =
  let op_kwds_opt =
    match c with
    | MatchesAll lpat when lpat<>[] -> Some (`All, lpat)
    | MatchesAny lpat when lpat<>[] -> Some (`Any, lpat)
    | _ -> None in
  match op_kwds_opt with
  | Some (op,kwds) ->
     let label_properties_langs = Lexicon.config_entity_lexicon#properties_langs in
     let binding, f = filter_kwds_gen (`Terms,`Bind) gv ~label_properties_langs t ~op ~kwds in
     if not binding
     then Sparql.formula_and (Sparql.Pattern (Sparql.something t)) f
     else f
  | _ -> Sparql.Pattern (Sparql.something t)
  

let triple_arg arg x y z =
  Sparql.Pattern
    ( match arg with
      | S -> Sparql.triple x y z
      | P -> Sparql.triple y x z
      | O -> Sparql.triple y z x
      | Q _ -> assert false)

let rec expr_apply func args =
  match func with
  | `Add -> Sparql.expr_infix "+" args
  | `Sub -> Sparql.expr_infix "-" args
  | `Mul -> Sparql.expr_infix "*" args
  | `Div -> Sparql.expr_infix "/" args
  | `Random2 ->
    ( match args with
    | [arg1; arg2] ->
      Sparql.expr_infix "+"
	[arg1;
	 Sparql.expr_infix "*"
	   [Sparql.expr_func "RAND" [];
	    Sparql.expr_infix "-" [arg2; arg1]]]
    | _ -> assert false )
  | `TODAY ->
    ( match args with
    | [] -> Sparql.expr_func "xsd:date" [Sparql.expr_func "NOW" []]
    | _ -> assert false )
  | `And -> Sparql.expr_infix "&&" args
  | `Or -> Sparql.expr_infix "||" args
  | `EQ -> Sparql.expr_infix "=" args
  | `NEQ -> Sparql.expr_infix "!=" args
  | `GT -> Sparql.expr_infix ">" args
  | `GEQ -> Sparql.expr_infix ">=" args
  | `LT -> Sparql.expr_infix "<" args
  | `LEQ -> Sparql.expr_infix "<=" args
  | `STRDT | `STRLANG | `Integer | `Decimal | `Double ->
    ( match args with
    | arg::other_args -> Sparql.expr_func (name_func func) (Sparql.expr_func "str" [arg] :: other_args)
    | [] -> assert false )
  | `REGEX_i -> Sparql.expr_func (name_func func) (args @ [(Sparql.string "i" :> Sparql.expr)])
  | func -> Sparql.expr_func (name_func func) args
and name_func = function
  | `Str -> "str"
  | `Lang -> "lang"
  | `Datatype -> "datatype"
  | `IRI -> "IRI"
  | `STRDT -> "STRDT"
  | `STRLANG -> "STRLANG"
  | `Strlen -> "strlen"
  | `Substr2 -> "substr"
  | `Substr3 -> "substr"
  | `Strbefore -> "strbefore"
  | `Strafter -> "strafter"
  | `Concat -> "concat"
  | `UCase -> "ucase"
  | `LCase -> "lcase"
  | `Encode_for_URI -> "encode_for_uri"
  | `Replace -> "replace"
  | `Integer -> "xsd:integer"
  | `Decimal -> "xsd:decimal"
  | `Double -> "xsd:double"
  | `Indicator -> "xsd:integer"
  | `Add | `Sub | `Mul | `Div -> invalid_arg "Lisql2sparql.name_func"
  | `Neg -> "-"
  | `Abs -> "abs"
  | `Round -> "round"
  | `Ceil -> "ceil"
  | `Floor -> "floor"
  | `Random2 -> invalid_arg "Lisql2sparql.name_func: Random2"
  | `Date -> "xsd:date"
  | `Time -> "xsd:time"
  | `Year -> "year"
  | `Month -> "month"
  | `Day -> "day"
  | `Hours -> "hours"
  | `Minutes -> "minutes"
  | `Seconds -> "seconds"
  | `TODAY -> invalid_arg "Lisql2sparql.name_func: TODAY"
  | `NOW -> "NOW"
  | `Not -> "!"
  | `And | `Or
  | `EQ | `NEQ | `GT | `GEQ | `LT | `LEQ -> invalid_arg "Lisql2sparql.name_func"
  | `BOUND -> "BOUND"
  | `IF -> "IF"
  | `IsIRI -> "IsIRI"
  | `IsBlank -> "IsBlank"
  | `IsLiteral -> "IsLiteral"
  | `IsNumeric -> "IsNumeric"
  | `StrStarts -> "strstarts"
  | `StrEnds -> "strends"
  | `Contains -> "contains"
  | `REGEX | `REGEX_i -> "REGEX"
  | `LangMatches -> "langMatches"

    
type sparql_p1 = Sparql.term -> Sparql.formula
type sparql_p2 = Sparql.term -> Sparql.term -> Sparql.formula
type sparql_pn = (arg * Sparql.term) list -> Sparql.formula
type sparql_s1 = sparql_p1 -> Sparql.formula
type sparql_s2 = sparql_p1 -> sparql_p1 -> Sparql.formula
type sparql_sn = sparql_pn -> Sparql.formula
type sparql_b1 = sparql_p2 -> Sparql.formula
type sparql_s = Sparql.formula

let get_arg (arg : arg) (l : (arg * _ Sparql.any_term) list) : Sparql.term =
  try List.assoc arg l
  with Not_found -> Sparql.bnode ""

(* definitions to retrieve classes from focus *)
module WhichClass =
  struct
    let pattern_vars = ["c"]
    let intent_pattern () =
      Sparql.(union
		[ rdf_type (var "c") (uri Rdf.rdfs_Class);
		  rdf_type (var "c") (uri Rdf.owl_Class) ])
    let pattern_of_term (t_opt : Rdf.term option) : Sparql.pattern =
      let init, t =
	match t_opt with
	| None -> true, Rdf.Bnode ""
	| Some t -> false, t in
      Sparql.(rdf_type (term t) (var "c"))
    let increments_of_terms ~(init : bool) (lt : Rdf.term option list) : Lisql.increment list =
      (* ~init: for initial focus *)
      match lt with
      | [Some (Rdf.URI c)] -> [Lisql.IncrType c]
      | _ -> []
  end

(* definitions to retrieve properties from focus *)
module WhichProp =
  struct
    let pattern_vars = ["p";"ip"] (* property, inverse property *)
    let intent_pattern () =
      Sparql.(union
		[ rdf_type (var "p") (uri Rdf.rdf_Property);
		  rdf_type (var "p") (uri Rdf.owl_ObjectProperty);
		  rdf_type (var "p") (uri Rdf.owl_DatatypeProperty) ])
    let pattern_of_term (t_opt : Rdf.term option) : Sparql.pattern =
      let init, t =
	match t_opt with
	| None -> true, Rdf.Bnode ""
	| Some t -> false, t in
      let filt p =
	if Rdf.config_wikidata_mode#value
	then Sparql.(filter (expr_func "strstarts" [expr_func "str" [var p]; (string "http://www.wikidata.org/prop/direct/P" :> expr)]))
	else Sparql.empty in
      Sparql.(union
		[ join
		    [ triple (term t) (var "p") (bnode "");
		      filt "p" ];
		  if init then empty
		  else join
			 [ triple (bnode "") (var "ip") (term t);
			   filt "ip" ] ])
    let increments_of_terms ~(init : bool) (lt : Rdf.term option list) : Lisql.increment list =
      match lt with
      | [Some (Rdf.URI p); None] ->
	 if init
	 then [Lisql.IncrRel (p,Fwd); Lisql.IncrRel (p,Bwd)]
	 else [Lisql.IncrRel (p,Fwd)]
      | [None; Some (Rdf.URI ip)] ->
	 [Lisql.IncrRel (ip,Bwd)]
      | _ -> []
  end
    
(* definitions to retrieve predicates from focus *)
module WhichPred =
  struct
    let pattern_vars : Rdf.var list = ["pe"; "ps"; "po"; "pq"]

    (* pattern_X defined as functions because [uri] has a side effect in Sparql.prologue *)
    let pattern_SO ps po =
      Sparql.(triple
		(var ps)
		(uri Rdf.nary_subjectObject)
		(var po))
    let pattern_EO pe po =
      Sparql.(triple
		(var pe)
		(uri Rdf.nary_eventObject)
		(var po))
    let pattern_wikidata pe po =
      Sparql.(join
		[ filter (expr_func "strstarts" [expr_func "str" [var pe]; (string "http://www.wikidata.org/prop/P" :> expr)]);
		  filter (expr_func "strstarts" [expr_func "str" [var po]; (string "http://www.wikidata.org/prop/statement/P" :> expr)]) ])
      (*Sparql.(bnode_triples_as_pattern
		[ (uri Rdf.wikibase_claim :> pred), var pe;
		  (uri Rdf.wikibase_statementProperty :> pred), var po ])*)
	    
    let intent_pattern () : Sparql.pattern =
      if Rdf.config_wikidata_mode#value
      then pattern_wikidata "pe" "po"
      else Sparql.(union [pattern_SO "ps" "po"; pattern_EO "pe" "po"])
		 
    let pattern_of_term (t_opt : Rdf.term option) : Sparql.pattern =
      let init, t =
	match t_opt with
	| None -> true, Rdf.Bnode ""
	| Some t -> false, t in		 
      let pat_SO =
	Sparql.(join
		  [ pattern_SO "ps" "po";
		    union
		      [ bnode_triples_as_pattern (* relation: ps, po *)
			  [ var "ps", term t;
			    var "po", bnode "" ];
			(*join (* qualifier: ps, po, pq *)
			  [ bnode_triples_as_pattern
			      [ var "ps", bnode "";
				var "po", bnode "";
				var "pq", term t ];
			    filter
			      (log_and
				 [ expr_infix "!=" [var "pq"; var "ps"];
				   expr_infix "!=" [var "pq"; var "po"] ])
			  ]*)
		      ]
		  ]) in
      let pat_EO_wikidata =
	let pat_schema pe po =
	  if Rdf.config_wikidata_mode#value
	  then pattern_wikidata pe po
	  else pattern_EO pe po in
	Sparql.(union
		  [ join
		      [ pat_schema "pe" "po";
			triple (* forward: pe, po *)
			  (term t)
			  (var "pe")
			  (bnode_triples
			     [ var "po", bnode "" ]) ];
		    if init then empty
		    else join (* backward: pe, ps, po *)
			   [ pat_schema "pe" "ps";
			     triple
			       (bnode "")
			       (var "pe")
			       (bnode_triples
				  [ var "ps", term t ]) ]; (* binding 'ps' to distinguish orientation *)
		    (*join (* qualifier: pe, po, pq *)
		      [ triple
			  (bnode "")
			  (var "pe")
			  (bnode_triples
			     [ var "po", bnode "";
			       var "pq", term t ]);
			filter
			  (expr_infix "!=" [var "pq"; var "po"])
		      ]*)
		  ]) in
      if Rdf.config_wikidata_mode#value
      then pat_EO_wikidata
      else Sparql.(union [pat_SO; pat_EO_wikidata])
	    
    let increments_of_terms ~(init : bool) (lt : Rdf.term option list) : Lisql.increment list =
      (* ~init: for initial focus, remind to generate increments in all relevant directions S/P/O *)
      match lt with
      | [None; Some (Rdf.URI ps); Some (Rdf.URI po); None] ->
	 [Lisql.IncrPred (S, SO (ps,po))]
      | [None; Some (Rdf.URI ps); Some (Rdf.URI po); Some (Rdf.URI pq)] ->
	 [Lisql.IncrPred (Q pq, SO (ps,po))]
      | [Some (Rdf.URI pe); None; Some (Rdf.URI po); None] ->
	 if init
	 then [Lisql.IncrPred (S, EO (pe,po)); Lisql.IncrPred (O, EO (pe,po))]
	 else [Lisql.IncrPred (S, EO (pe,po))]
      | [Some (Rdf.URI pe); Some (Rdf.URI ps); None; None] ->
	 [Lisql.IncrPred (O, EO (pe,ps))]
      | [Some (Rdf.URI pe); None; Some (Rdf.URI po); Some (Rdf.URI pq)] ->
	 [Lisql.IncrPred (Q pq, EO (pe,po))]
      | _ -> []

    let increments_hidden_by_increment ~(init : bool) (incr : increment) : increment list =
      let open Lisql in
      if init
      then
	let lp =
	  match incr with
	  | IncrPred (_, SO (ps,po)) -> [ps; po]
	  | IncrPred (_, EO (pe,po)) -> [pe; po]
	  | _ -> [] in
	List.fold_right
	  (fun p res -> IncrRel (p,Fwd) :: IncrRel (p,Bwd) :: res)
	  lp []
      else
	match incr with
	| IncrPred (S, SO (ps,po)) -> [IncrRel (ps,Bwd)]
	| IncrPred (O, SO (ps,po)) -> [IncrRel (po,Bwd)]
	| IncrPred (S, EO (pe,po)) -> [IncrRel (pe,Fwd)]
	| IncrPred (O, EO (pe,po)) -> [IncrRel (po,Bwd)]
	| _ -> []
  end

    
let pattern_pred_args (pred : pred) (args : (arg * _ Sparql.any_term) list) (var_args : (string * _ Sparql.any_term) list) : Sparql.pattern =
  let args = if List.mem_assoc S args then args else (S, Sparql.bnode "")::args in
  let args = if List.mem_assoc O args then args else (O, Sparql.bnode "")::args in
  match pred with
  | Class c -> Sparql.rdf_type (get_arg S args) (Sparql.uri c)
  | Prop p -> Sparql.triple (get_arg S args) (Sparql.uri p) (get_arg O args)
  | SO (ps,po) ->
     let lpo = [] in
     let lpo =
       List.fold_right
	 (fun (v,t) lpo -> ((Sparql.var v :> Sparql.pred), t) :: lpo)
	 var_args lpo in
     let lpo =
       List.fold_right
	 (fun (arg,t) lpo ->
	  match arg with
	  | S -> ((Sparql.uri ps :> Sparql.pred), t) :: lpo
	  | O -> ((Sparql.uri po :> Sparql.pred), t) :: lpo
	  | P -> lpo
	  | Q q -> ((Sparql.uri q :> Sparql.pred), t) :: lpo)
	 args lpo in
     Sparql.bnode_triples_as_pattern lpo
  | EO (pe,po) ->
     let lpo = [] in
     let lpo =
       List.fold_right
	 (fun (v,t) lpo -> ((Sparql.var v :> Sparql.pred), t) :: lpo)
	 var_args lpo in
     let lpo =
       List.fold_right
	 (fun (arg,t) lpo ->
	  match arg with
	  | S -> lpo
	  | O -> ((Sparql.uri po :> Sparql.pred), t) :: lpo
	  | P -> lpo
	  | Q q -> ((Sparql.uri q :> Sparql.pred), t) :: lpo)
	 args lpo in
     Sparql.(triple
	       (get_arg S args)
	       (uri pe)
	       (bnode_triples lpo))

module WhichArg =
  struct
    let pattern_vars = ["pq"]

    let pattern_of_pred_args (pred : Lisql.pred) (args : (Lisql.arg * Rdf.term) list) : Sparql.pattern =
      let filter_qualifier =
	match pred with
	| Class _ -> Sparql.empty
	| Prop _ -> Sparql.empty
	| SO (ps,po) -> Sparql.(filter (expr_not_in (var "pq") [uri Rdf.rdf_type; uri ps; uri po]))
	| EO (pe,po) ->
	   if Rdf.config_wikidata_mode#value
	   then Sparql.(filter (expr_func "strstarts" [expr_func "str" [var "pq"]; (string "http://www.wikidata.org/prop/qualifier/P" :> expr)]))
	   else Sparql.(filter (expr_not_in (var "pq") [uri Rdf.rdf_type; uri po])) in
      Sparql.(join
		[ pattern_pred_args
		    pred
		    (List.map (fun (arg,t) -> (arg, term t)) args)
		    ["pq", bnode ""];
		  filter_qualifier ])

    let increments_of_terms (lt : Rdf.term option list) : Lisql.increment list =
      match lt with
      | [Some (Rdf.URI pq)] -> [Lisql.IncrArg pq]
      | _ -> []
  end
	   
let form_pred state (pred : pred) : sparql_pn =
  (fun l -> Sparql.Pattern (pattern_pred_args pred l []))
	      
let rec form_p1 state : annot elt_p1 -> sparql_p1 = function
  | Is (annot,np) -> form_s1_as_p1 state np
  | Pred (annot,arg,pred,cp) ->
     let pred = form_pred state pred in
     let cp = form_sn state cp in
     (fun x -> cp (fun l -> pred ((arg,x)::l)))
  | Type (annot,c) ->
     (fun x -> Sparql.Pattern (Sparql.rdf_type x (Sparql.uri c)))
  | Rel (annot,prop,ori,np) ->
     let p = Sparql.uri prop in
     let rel =
       match ori with
       | Fwd -> (fun x y -> Sparql.Pattern (Sparql.triple x p y))
       | Bwd -> (fun x y -> Sparql.Pattern (Sparql.triple y p x)) in
     let q_np = form_s1 state np in
     (fun x -> q_np (fun y -> rel x y))
  | Hier (annot,id,p,ori,inv,np) ->
     let vy = state#id_labelling#get_id_var id in
     state#set_modif vy (Lisql.Unselect,Lisql.Unordered);
     let y = (Sparql.var vy :> Sparql.term) in
     let hier =
       let ptrans = Sparql.path_transitive (Sparql.uri p) in
       match ori with
       | Fwd -> (fun x y -> Sparql.Pattern (Sparql.triple x ptrans y))
       | Bwd -> (fun x y -> Sparql.Pattern (Sparql.triple y ptrans x)) in
     let q_np = form_s1 ~ignore_top:true state np in
     (fun x ->
      state#add_var vy;
      Sparql.formula_and_list [q_np (fun z -> hier x z); hier x y])
  | LatLong (annot,ll,id1,id2) ->
    let v1 = state#id_labelling#get_id_var id1 in
    let v2 = state#id_labelling#get_id_var id2 in
    let lat, long = Sparql.var v1, Sparql.var v2 in
    let f_ll = form_latlong ll in
    (fun x ->
     state#add_geoloc x v1 v2;
     f_ll x lat long)
  | Triple (annot,arg,np1,np2) ->
    let q_np1 = form_s1 state np1 in
    let q_np2 = form_s1 state np2 in
    (fun x -> q_np1 (fun y -> q_np2 (fun z -> triple_arg arg x y z)))
  | Search (annot,c) -> (fun x -> search_constr_entity state#genvar x c)
  | Filter (annot,c) -> (fun x -> filter_constr_entity state#genvar x c)
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
  | In (annot,npg,f) ->
    let q = form_s1 state npg in
    let d = form_p1 state f in
    (fun x -> q (fun g -> Sparql.formula_graph g (d x)))
  | InWhichThereIs (annot,np) ->
    let q = form_s1 state np in
    (fun g -> Sparql.formula_graph g (q (fun x -> Sparql.True)))
  | IsThere annot -> (fun x -> Sparql.True)
and form_latlong = function
  | `Custom (plat,plong) ->
     (fun x lat long ->
      Sparql.(formula_and
	(Pattern (triple x (uri plat) lat))
	(Pattern (triple x (uri plong) long))))
  | `Wikidata ->
     (fun x lat long -> Sparql.Pattern (Sparql.wikidata_lat_long x lat long))
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
    (fun x -> Sparql.(Filter (expr_comp "=" x (term t))))
(*    (fun x -> "BIND (" ^ Sparql.term t ^ " AS " ^ Sparql.term x ^ ")") *)
  | An (_id, _modif,head) -> form_head_as_p1 state head
  | The id ->
    (fun x ->
      let v = state#id_labelling#get_id_var id in
      let t = Rdf.Var v in
      Sparql.(Filter (expr_comp "=" x (term t))))
and form_head_as_p1 state : elt_head -> sparql_p1 = function
  | Thing -> (fun x -> Sparql.True)
  | Class c -> (fun x -> Sparql.(Pattern (rdf_type x (uri c))))
and form_sn state : annot elt_sn -> sparql_sn = function
  | CNil annot ->
     (fun p -> p [])
  | CCons (annot,arg,np,cp) ->
     let np = form_s1 state np in
     let cp = form_sn state cp in
     (fun p -> np (fun x -> cp (fun l -> p ((arg,x)::l))))
  | CAnd (annot,lr) ->
    let lr_q = List.map (fun elt -> form_sn state elt) lr in
    (fun p -> Sparql.formula_and_list (List.map (fun q -> q p) lr_q))
  | COr (annot,lr) ->
    ( match annot#get_susp_focus_index with
    | Some i -> form_sn state (List.nth lr i)
    | None ->
      let lr_q = List.map (fun elt -> form_sn state elt) lr in
      (fun p -> Sparql.formula_or_list (List.map (fun q -> q p) lr_q)) )
  | CMaybe (annot,f) ->
    if annot#is_susp_focus
    then form_sn state f
    else
      let q = form_sn state f in
      (fun p -> Sparql.formula_optional (q p))
  | CNot (annot,f) ->
    if annot#is_susp_focus
    then form_sn state f
    else
      let q = form_sn (Oo.copy state) f in
      (fun p -> Sparql.formula_not (q p))
and form_s1 ?(ignore_top = false) state : annot elt_s1 -> sparql_s1 = function
  | Det (annot,det,rel_opt) ->
     if ignore_top && is_top_s2 det && is_top_p1_opt rel_opt
     then (fun d -> Sparql.True)
     else
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
    let lr_q = List.map (fun elt -> form_s1 ~ignore_top state elt) lr in
    (fun d -> Sparql.formula_and_list (List.map (fun q -> q d) lr_q))
  | NOr (annot,lr) ->
    ( match annot#get_susp_focus_index with
    | Some i -> form_s1 ~ignore_top state (List.nth lr i)
    | None ->
      let lr_q = List.map (fun elt -> form_s1 ~ignore_top state elt) lr in
      (fun d -> Sparql.formula_or_list (List.map (fun q -> q d) lr_q)) )
  | NMaybe (annot,f) ->
    if annot#is_susp_focus
    then form_s1 ~ignore_top state f
    else
      let q = form_s1 ~ignore_top state f in
      (fun d -> Sparql.formula_optional (q d))
  | NNot (annot,f) ->
    if annot#is_susp_focus
    then form_s1 ~ignore_top state f
    else
      let q = form_s1 ~ignore_top (Oo.copy state) f in
      (fun d -> Sparql.formula_not (q d))
(*      
  | NRelax f ->
    state#set_relax true;
    let q = form_s1 state f in
    state#set_relax false;
    q
*)
and form_s2 state : elt_s2 -> sparql_s2 = function
  | Term term ->
    let t = Sparql.term term in
    (fun d1 d2 -> Sparql.formula_and (d1 t) (d2 t))
  | An (id, modif, head) ->
    let qhead = form_head state head in
    let v = state#id_labelling#get_id_var id in
    state#set_modif v modif;
    let t = (Sparql.var v :> Sparql.term) in
    (fun d1 d2 -> state#add_var v; qhead t (Sparql.formula_and (d2 t) (d1 t))) (* YES: d2 - d1 *)
  | The id ->
    let v = state#id_labelling#get_id_var id in
    let t = (Sparql.var v :> Sparql.term) in
    (fun d1 d2 -> Sparql.formula_and (d2 t) (d1 t)) (* YES: d2 - s1 *)
and form_head state : elt_head -> (Sparql.term -> Sparql.formula -> Sparql.formula) = function
  | Thing ->
    (fun x form -> Sparql.formula_bind x form)
  | Class c ->
    (fun x form -> Sparql.formula_and (Sparql.Pattern (Sparql.rdf_type x (Sparql.uri c))) form)
and form_aggreg_op state idg modifg g (d : sparql_p1) id : unit =
  let vg = state#id_labelling#get_id_var idg in
  let v = state#id_labelling#get_id_var id in
  state#set_aggreg v (vg, g, (d (Sparql.var vg :> Sparql.term)));
  state#set_modif vg modifg
and form_dim state : annot elt_aggreg -> Sparql.projection option * Rdf.var option (* group by var *) * Sparql.formula (* relative *) = function
  | ForEachResult annot -> assert false
  | ForEach (annot,id,modif,rel_opt,id2) ->
    let v = state#id_labelling#get_id_var id in
    state#set_modif v modif;
    let d = form_p1_opt state rel_opt in
    let v2 = state#id_labelling#get_id_var id2 in
    Some (`Expr (Sparql.var v2 :> Sparql.expr), v), Some v2, (d (Sparql.var v2 :> Sparql.term))
  | ForTerm (annot,t,id2) ->
    let v2 = state#id_labelling#get_id_var id2 in
    None, None, Sparql.Filter (Sparql.expr_comp "=" (Sparql.var v2) (Sparql.term t))
  | _ -> assert false
and form_aggreg state : annot elt_aggreg -> Sparql.projection * Rdf.var * Sparql.expr (* having expr *) = function
  | TheAggreg (annot,id,modif,g,rel_opt,id2) ->
    let v = state#id_labelling#get_id_var id in
    state#set_modif v modif;
    let d = form_p1_opt state rel_opt in
    let v2 = state#id_labelling#get_id_var id2 in
    let sparql_g = sparql_aggreg g in
    let t_v2 = (Sparql.var v2 :> Sparql.term) in
    (`Aggreg (sparql_g, t_v2), v), v2, Sparql.expr_of_formula (d (Sparql.term_aggreg sparql_g t_v2))
  | _ -> assert false
and form_expr_list state : annot elt_expr -> Sparql.expr list = function (* non-deterministic semantics *)
  | Undef annot -> []
  | Const (annot,t) -> [(Sparql.term t :> Sparql.expr)]
  | Var (annot,id) -> [(Sparql.var (state#id_labelling#get_id_var id) :> Sparql.expr)]
  | Apply (annot,func,args) ->
    if not annot#defined
    then []
    else
      ( match annot#focus_pos with
      | `Above (true, Some pos) -> form_expr_list state (snd (List.nth args (pos-1)))
      | _ ->
	let sparql_list_args =
	  List.map
	    (fun (conv_opt,arg_expr) -> List.map (sparql_converter conv_opt) (form_expr_list state arg_expr))
	    args in
	Common.list_fold_prod
	  (fun res sparql_args -> expr_apply func sparql_args :: res)
	  [] sparql_list_args )
  | Choice (annot,le) ->
    ( match annot#focus_pos with
    | `Above (true, Some pos) -> form_expr_list state (try List.nth le pos with _ -> assert false)
    | _ -> List.concat (List.map (form_expr_list state) le) )
and form_s state (s : annot elt_s) : seq_view * Sparql.view =
  let (_, view as seq_view), lr =
    match s with
    | Return (annot,np) -> (0, Atom (annot#ids,0)), [s]
    | Seq (annot,lr) -> (match annot#seq_view with Some seq_view -> seq_view | None -> assert false), lr
    | _ -> assert false in
  seq_view, form_view state lr view
and form_view state (lr : annot elt_s list) (v : view) : Sparql.view =
  let lv =
    match v with
    | Unit -> []
    | Atom _ -> [v]
    | InlineAggregs _ -> [v]
    | Aggreg _ -> [v]
    | Join (_,lv) -> lv in
  form_view_list state lr Sparql.empty_view lv
and form_view_list state (lr : annot elt_s list) (view : Sparql.view) : view list -> Sparql.view =
  let ids2vars ids = List.map state#id_labelling#get_id_var ids in
  function
  | [] -> view
  | Unit::lv -> form_view_list state lr view lv
  | Atom (ids,sid)::lv ->
    ( match List.nth lr sid with
    | Return (annot,np) ->
      let ids = annot#ids in
      let lx = ids2vars (Ids.elements ids.defs) in
      let form = form_s1 state np (fun t -> Sparql.True) in
      form_view_list state lr (Sparql.join_views [view; Sparql.simple_view lx form]) lv
    | SExpr (annot,name,id,modif,expr,rel_opt) ->
      let x = state#id_labelling#get_id_var id in
      state#set_modif x modif;
      let sparql_expr_list = form_expr_list state expr in
      let form =
	if sparql_expr_list = []
	then Sparql.True
	else
	  let d = form_p1_opt state rel_opt in
	  Sparql.formula_and
	    (Sparql.formula_or_list
	       (List.map
		  (fun sparql_expr -> Sparql.Pattern (Sparql.bind sparql_expr (Sparql.var x)))
		  sparql_expr_list))
	    (d (Sparql.var x :> Sparql.term)) in
      form_view_list state lr (Sparql.join_views [view; Sparql.simple_view [x] form]) lv
    | SFilter (annot,id,expr) ->
      let x = state#id_labelling#get_id_var id in
      let sparql_expr_list = form_expr_list state expr in
      let lx, form =
	match annot#focus_pos with
	| `Above _ -> [x], Sparql.formula_or_list (List.map (fun sparql_expr -> Sparql.Pattern (Sparql.bind sparql_expr (Sparql.var x))) sparql_expr_list)
	| _ -> [], Sparql.Filter (Sparql.log_or sparql_expr_list) in
      let form =
	if sparql_expr_list = []
	then Sparql.True
	else form in
      form_view_list state lr (Sparql.join_views [view; Sparql.simple_view lx form]) lv
    | _ -> assert false )
  | InlineAggregs (ids,sid,_ids2)::lv ->
    ( match List.nth lr sid with
    | SAggreg (annot, aggregs) ->
      assert (List.exists is_ForEachResult aggregs);
      let aggregs = List.filter is_aggreg aggregs in 
      let l_aggregs = List.map (form_aggreg state) aggregs in
      let lx2 = List.map (fun (_,x2,_) -> x2) l_aggregs in
      let projections_aggregs = List.map (fun (proj,_,_) -> proj) l_aggregs in
      let havings_aggregs = List.map (fun (_,_,hav) -> hav) l_aggregs in
      let view =
	(fun ?limit () ->
	  let sq = view ?limit () in
	  { sq with
	    Sparql.projections = List.filter (fun (_,x) -> not (List.mem x lx2)) sq.Sparql.projections @ projections_aggregs;
	    groupings = List.filter (fun x -> not (List.mem x lx2)) sq.Sparql.groupings;
	    having = Sparql.log_and (sq.Sparql.having :: havings_aggregs) }) in
      form_view_list state lr view lv
    | _ -> assert false )
  | Aggreg (ids,sid,v2)::lv ->
    let aggregated_view = form_view state lr v2 in
    ( match List.nth lr sid with
    | SAggreg (annot,dims_aggregs) ->
      let dims = List.filter is_dim dims_aggregs in
      let aggregs = List.filter is_aggreg dims_aggregs in
      let l_dims = List.map (form_dim state) dims in
      let l_aggregs = List.map (form_aggreg state) aggregs in
      let projections_dims = List.fold_right (fun (proj_opt,_,_) res -> match proj_opt with None -> res | Some proj -> proj::res) l_dims [] in
      let projections_aggregs = List.map (fun (proj,_,_) -> proj) l_aggregs in
      let projections = projections_dims @ projections_aggregs in
      let groupings_dims = List.fold_right (fun (_,group_opt,_) res -> match group_opt with None -> res | Some group -> group::res) l_dims [] in
      let lf_dims = List.map (fun (_,_,hav) -> hav) l_dims in
      let havings_aggregs = List.map (fun (_,_,hav) -> hav) l_aggregs in
      let view_aggreg =
	(fun ?limit () ->
	  let form =
	    Sparql.formula_and_list
	      (Sparql.formula_of_view ?limit:(match limit with None -> None | Some l -> Some (10*l)) aggregated_view :: lf_dims) in
	  let form = (* special handling of GROUP_CONCAT without grouping, to avoid explosion *)
	    if groupings_dims = []
	    && List.exists (function (`Aggreg (Sparql.DistinctCONCAT, _), _) -> true | _ -> false) projections_aggregs
	    then Sparql.Subquery
	      (Sparql.make_subquery
		 ~projections:(List.fold_right
				 (fun (_,v2_opt,_) res -> match v2_opt with None -> res | Some v2 -> (`Bare,v2)::res) l_dims
				 (List.map (fun (_,v2,_) -> (`Bare,v2)) l_aggregs))
		 ~groupings:[]
		 ~having:Sparql.log_true
		 ?limit
		 form)
	    else form in
	  let sq_aggreg =
	    Sparql.make_subquery
	      ~projections
	      ~groupings:groupings_dims
	      ~having:(Sparql.log_and havings_aggregs)
	      ?limit
	      form in
	  if Sparql.is_empty_view view && lv = []
	  then sq_aggreg (* isolated aggregation *)
	  else
	    Sparql.make_subquery
	      ~projections:(List.map (fun (_,x) -> (`Bare,x)) sq_aggreg.Sparql.projections)
	      ~groupings:(List.map (fun (_,x) -> x) sq_aggreg.Sparql.projections)
	      (Sparql.Subquery sq_aggreg)) in
      form_view_list state lr (Sparql.join_views [view; view_aggreg]) lv
    | _ -> assert false)
  | Join (_,lv1)::lv -> form_view_list state lr view (lv1@lv)

    
type template = ?hook:(Sparql.term -> Sparql.formula) -> froms:(Rdf.uri list) -> limit:int -> string

let make_query state (focus_term_opt : Rdf.term option) (view : Sparql.view) : template =
  (fun ?hook ~froms ~limit ->
    let sq_view = view ~limit () in
    let sq_view = (* when sq_view makes no proper computation *)
      if sq_view.Sparql.having = Sparql.log_true &&
	List.for_all (function (`Bare,_) -> true | _ -> false) sq_view.Sparql.projections (* implies there are no relevant group-by *)
      then (* and its contents is itself a subquery *)
	match sq_view.Sparql.formula with
	| Sparql.Subquery sq -> sq (* use that subquery instead *)
	| _ -> sq_view
      else sq_view in
    let visible_projections =
      List.filter
	(fun (_,v) -> state#project v = Select || focus_term_opt = Some (Rdf.Var v))
	sq_view.Sparql.projections in
    let form_hook =
      match focus_term_opt, hook with
      | Some (Rdf.Var v), Some f_hook ->
	Sparql.formula_and sq_view.Sparql.formula (f_hook (Sparql.var v :> Sparql.term))
      | _ -> sq_view.Sparql.formula in
    let orderings =
      List.fold_right
	(fun (_,v) orderings ->
	  match sparql_order (state#order v) with
	  | None -> orderings
	  | Some order -> (order, Sparql.var v)::orderings)
	sq_view.Sparql.projections [] in
    let query = Sparql.select
      ~distinct:true
      ~projections:visible_projections
      ~froms
      ~groupings:(List.map Sparql.var sq_view.Sparql.groupings)
      ~having:sq_view.Sparql.having
      ~limit
      ~orderings
      (Sparql.pattern_of_formula form_hook) in
    (query :> string))

type s_sparql =
  { state : state;
    focus_term_opt : Rdf.term option;
    focus_graph_opt : Rdf.term option;
    focus_pred_args_opt : (pred * (arg * Rdf.term) list) option;
    query_opt : template option;
    query_class_opt : template option;
    query_prop_opt : template option;
    query_pred_opt : template option;
    query_arg_opt : template option;
    seq_view : seq_view }
    
let s_annot (id_labelling : Lisql2nl.id_labelling) (fd : focus_descr) (s_annot : annot elt_s) : s_sparql =
  let state = new state id_labelling in
  let seq_view, view = form_s state s_annot in
  let rdf_term_of_term_id : term_id -> Rdf.term = function
    | `Term t -> t
    | `Id id -> Rdf.Var (id_labelling#get_id_var id) in
  let focus_term_opt : Rdf.term option =
    match fd#term with
    | `Undefined -> None
    | (#term_id as ti) -> Some (rdf_term_of_term_id ti) in
  let focus_graph_opt : Rdf.term option =
    match fd#graph with
    | `Default -> None
    | `Named ti -> Some (rdf_term_of_term_id ti) in
  let focus_pred_args_opt : (pred * (arg * Rdf.term) list) option =
    match fd#pred_args with
    | `Undefined -> None
    | `PredArgs (pred,args) ->
       let rdf_args = List.map (fun (arg,ti) -> (arg, rdf_term_of_term_id ti)) args in
       Some (pred,rdf_args) in
  let query_opt =
    if Sparql.is_empty_view view
    then None
    else Some (make_query state focus_term_opt view) in
  let query_incr_opt (lx : Rdf.var list) (make_pattern : Rdf.term -> Sparql.pattern) =
    let _ = assert (lx <> []) in
    let x = List.hd lx in
    match focus_term_opt with
    | Some t when fd#incr -> (* no increments for this focus term (expressions, aggregations) *)
      let tx = (Sparql.var x :> Sparql.term) in
      Some (fun ?(hook=(fun tx -> Sparql.True)) ~froms ~limit ->
	let form_x = Sparql.Pattern (make_pattern t) in
	let form_x = match focus_graph_opt with None -> form_x | Some tg -> Sparql.formula_graph (Sparql.term tg) form_x in
	let form_x =
	  match focus_term_opt with
	  | Some (Rdf.Var _) -> Sparql.formula_and (Sparql.formula_of_view ~limit view) form_x
	  | _ -> form_x in
	let form_x = Sparql.formula_and form_x (hook tx) in
	let projections = List.map (fun x -> (`Bare,x)) lx in
	(Sparql.select ~projections ~froms ~limit
	   (Sparql.pattern_of_formula form_x) :> string))
    | _ -> None in
  let query_class_opt =
    query_incr_opt
      WhichClass.pattern_vars
      (fun t -> WhichClass.pattern_of_term (Some t)) in
  let query_prop_opt =
    query_incr_opt
      WhichProp.pattern_vars
      (fun t -> WhichProp.pattern_of_term (Some t)) in
  let query_pred_opt =
    query_incr_opt
      WhichPred.pattern_vars
      (fun t -> WhichPred.pattern_of_term (Some t)) in
  let query_arg_opt =
    match focus_pred_args_opt with
    | None
    | Some ((Lisql.Class _ | Lisql.Prop _),_) -> None (* non-reified predicates *)
    | Some (pred,args) ->
       query_incr_opt
	 WhichArg.pattern_vars
	 (fun _t -> WhichArg.pattern_of_pred_args pred args) in
  { state;
    focus_term_opt;
    focus_graph_opt;
    focus_pred_args_opt;
    query_opt;
    query_class_opt;
    query_prop_opt;
    query_pred_opt;
    query_arg_opt;
    seq_view }
