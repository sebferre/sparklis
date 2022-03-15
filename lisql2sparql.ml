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
      | IntegerConv -> "xsd:integer"
      | DecimalConv -> "xsd:decimal"
      | DoubleConv -> "xsd:double" in
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

type filter_context = [`Properties|`Terms] * Lisql.filter_type * [`Bind|`Filter]

let filter_kwds_gen (ctx : filter_context) (gv : genvar) ~(label_properties_langs : string list * string list) (t : _ Sparql.any_term) ~(op : [`All|`Any|`Exact|`Start|`End]) ~(kwds : string list) : Sparql.formula =
  let label_props, label_langs = label_properties_langs in
  let kwd = match kwds with kwd::_ -> kwd | _ -> assert false in
  let make_filter (e : Sparql.expr) : Sparql.formula =
    match op with
    | (`All | `Any as op) ->
       let log_op =
	 match op with
	 | `All -> Sparql.log_and
	 | `Any -> Sparql.log_or in
       Sparql.Filter
	 (log_op
	    (List.map
	       (fun pat -> Sparql.expr_regex (Sparql.expr_func "str" [e]) pat)
	       kwds))
    | `Exact -> Sparql.(Filter (expr_comp "=" (Sparql.expr_func "str" [e]) (string kwd)))
    | `Start -> Sparql.(Filter (expr_func "strstarts" [e; (string kwd :> Sparql.expr)]))
    | `End -> Sparql.(Filter (expr_func "strends" [e; (string kwd :> Sparql.expr)]))
  in
  let str_filter =
    make_filter (t :> Sparql.expr) in
  let label_filter_opt =
    if label_props = []
    then `Undefined
    else
      let open Sparql in
      let term_l = (var (gv#new_var "constr_label") :> Sparql.term) in
      `Filter (formula_and_list
		 [ Pattern (triple t (path_alt (List.map path_uri label_props :> pred list)) term_l);
		   (if label_langs = []
		    then True
		    else Filter (expr_in (expr_func "lang" [term_l]) (List.map string label_langs)));
		   make_filter (term_l :> Sparql.expr) ]) in
  let label_filter_opt =
    match op, config_fulltext_search#value, ctx with
    | (`All | `Any as op), "text:query", _  ->
       let lucene_query = Jsutils.lucene_query_of_kwds ~op kwds in
       if lucene_query = ""
       then `NoFilter
       else `Filter (Sparql.Pattern (Sparql.text_query t lucene_query))
    | (`All | `Any as op), "bif:contains", (`Terms,OnlyIRIs,`Bind) -> (* only efficient in this context; TODO: check *)
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
		      [ Pattern (triple t (path_alt (List.map path_uri label_props :> pred list)) term_l);
			Pattern (bif_contains term_l sql_query);
			(if label_langs = []
			 then True
			 else Filter (expr_in (expr_func "lang" [term_l]) (List.map string label_langs))) ])
    | _ -> label_filter_opt (* using REGEX *)
  in
  let f =
    match label_filter_opt with
    | `Undefined -> str_filter
    | `NoFilter -> Sparql.True (* kwds not specific enough *)
    | `Filter label_filter ->
       ( match ctx with
	 | _, OnlyIRIs, _ -> label_filter
	 | _, OnlyLiterals, _ -> str_filter
	 | _, Mixed, _ -> Sparql.formula_or_list [str_filter; label_filter] ) in
  f

let filter_constr_gen (ctx : filter_context) (gv : genvar) ~(label_properties_langs : string list * string list) (t : _ Sparql.any_term) (c : constr) : Sparql.formula =
  (* both [label_properties] and [label_langs] may be the empty list, meaning undefined *)
  match c with
    | True -> Sparql.True
    | MatchesAll [] -> Sparql.True
    | MatchesAll lpat ->
       filter_kwds_gen ctx gv ~label_properties_langs t ~op:`All ~kwds:lpat
    | MatchesAny [] -> Sparql.True
    | MatchesAny lpat ->
       filter_kwds_gen ctx gv ~label_properties_langs t ~op:`Any ~kwds:lpat
    | IsExactly "" -> Sparql.True
    | IsExactly pat ->
       filter_kwds_gen ctx gv ~label_properties_langs t ~op:`Exact ~kwds:[pat]
    | StartsWith "" -> Sparql.True
    | StartsWith pat ->
       filter_kwds_gen ctx gv ~label_properties_langs t ~op:`Start ~kwds:[pat]
    | EndsWith "" -> Sparql.True
    | EndsWith pat ->
       filter_kwds_gen ctx gv ~label_properties_langs t ~op:`End ~kwds:[pat]
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
    | ExternalSearch (_, None) -> Sparql.True
    | ExternalSearch (_, Some lt) ->
       Sparql.formula_term_in_term_list t (List.map Sparql.term lt)
					
let filter_constr_entity gv t c (ft : Lisql.filter_type) = filter_constr_gen (`Terms,ft,`Filter) gv ~label_properties_langs:Lexicon.config_entity_lexicon#properties_langs t c
let filter_constr_class gv t c = filter_constr_gen (`Properties,OnlyIRIs,`Filter) gv ~label_properties_langs:Lexicon.config_concept_lexicon#properties_langs t c
let filter_constr_property gv t c = filter_constr_gen (`Properties,OnlyIRIs,`Filter) gv ~label_properties_langs:Lexicon.config_concept_lexicon#properties_langs t c

let search_constr_entity (gv : genvar) (t : _ Sparql.any_term) (c : constr) (ft : Lisql.filter_type) : Sparql.formula =
  let label_properties_langs = Lexicon.config_entity_lexicon#properties_langs in
  let f = filter_constr_gen (`Terms,ft,`Bind) gv
			    ~label_properties_langs
			    t c in
  let open Sparql in
  let binding_pat =
    match ft with
    | OnlyIRIs -> something t
    | OnlyLiterals -> triple (bnode "") (var (gv#new_var "p")) t
    | Mixed -> union [something t;
		      triple (bnode "") (var (gv#new_var "p")) t] in
  match f with
  | Pattern _ -> f
  | Subquery _ -> f
  | Filter expr -> Pattern (join [binding_pat; filter expr])
  | True -> Pattern binding_pat
  | False -> False
  | Or (pat,expr) -> Pattern (union [pat; join [binding_pat; filter expr]])
	      
let triple_arg arg x y z =
  Sparql.Pattern
    ( match arg with
      | S -> Sparql.triple x y z
      | P -> Sparql.triple y x z
      | O -> Sparql.triple y z x
      | Q _ -> assert false)

let rec expr_apply func args =
  match func with
  | Add -> Sparql.expr_infix "+" args
  | Sub -> Sparql.expr_infix "-" args
  | Mul -> Sparql.expr_infix "*" args
  | Div -> Sparql.expr_infix "/" args
  | Random2 ->
    ( match args with
    | [arg1; arg2] ->
      Sparql.expr_infix "+"
	[arg1;
	 Sparql.expr_infix "*"
	   [Sparql.expr_func "RAND" [];
	    Sparql.expr_infix "-" [arg2; arg1]]]
    | _ -> assert false )
  | TODAY ->
    ( match args with
    | [] -> Sparql.expr_func "xsd:date" [Sparql.expr_func "NOW" []]
    | _ -> assert false )
  | And -> Sparql.expr_infix "&&" args
  | Or -> Sparql.expr_infix "||" args
  | EQ -> Sparql.expr_infix "=" args
  | NEQ -> Sparql.expr_infix "!=" args
  | GT -> Sparql.expr_infix ">" args
  | GEQ -> Sparql.expr_infix ">=" args
  | LT -> Sparql.expr_infix "<" args
  | LEQ -> Sparql.expr_infix "<=" args
  | STRDT | STRLANG | Integer | Decimal | Double ->
    ( match args with
    | arg::other_args -> Sparql.expr_func (name_func func) (Sparql.expr_func "str" [arg] :: other_args)
    | [] -> assert false )
  | REGEX_i -> Sparql.expr_func (name_func func) (args @ [(Sparql.string "i" :> Sparql.expr)])
  | func -> Sparql.expr_func (name_func func) args
and name_func = function
  | Str -> "str"
  | Lang -> "lang"
  | Datatype -> "datatype"
  | IRI -> "IRI"
  | STRDT -> "STRDT"
  | STRLANG -> "STRLANG"
  | Strlen -> "strlen"
  | Substr2 -> "substr"
  | Substr3 -> "substr"
  | Strbefore -> "strbefore"
  | Strafter -> "strafter"
  | Concat -> "concat"
  | UCase -> "ucase"
  | LCase -> "lcase"
  | Encode_for_URI -> "encode_for_uri"
  | Replace -> "replace"
  | Integer -> "xsd:integer"
  | Decimal -> "xsd:decimal"
  | Double -> "xsd:double"
  | Indicator -> "xsd:integer"
  | Add | Sub | Mul | Div -> invalid_arg "Lisql2sparql.name_func"
  | Neg -> "-"
  | Abs -> "abs"
  | Round -> "round"
  | Ceil -> "ceil"
  | Floor -> "floor"
  | Random2 -> invalid_arg "Lisql2sparql.name_func: Random2"
  | Date -> "xsd:date"
  | Time -> "xsd:time"
  | Year -> "year"
  | Month -> "month"
  | Day -> "day"
  | Hours -> "hours"
  | Minutes -> "minutes"
  | Seconds -> "seconds"
  | TODAY -> invalid_arg "Lisql2sparql.name_func: TODAY"
  | NOW -> "NOW"
  | Not -> "!"
  | And | Or
  | EQ | NEQ | GT | GEQ | LT | LEQ -> invalid_arg "Lisql2sparql.name_func"
  | BOUND -> "BOUND"
  | IF -> "IF"
  | IsIRI -> "IsIRI"
  | IsBlank -> "IsBlank"
  | IsLiteral -> "IsLiteral"
  | IsNumeric -> "IsNumeric"
  | StrStarts -> "strstarts"
  | StrEnds -> "strends"
  | Contains -> "contains"
  | REGEX | REGEX_i -> "REGEX"
  | LangMatches -> "langMatches"

type deps = Rdf.term list list (* each dependency corresponds to a hyper-edge over a list of vars *)
type deps_p1 = Rdf.term -> deps
type deps_pn = Rdf.term list -> deps
type deps_s1 = deps_p1 -> deps
type deps_s2 = deps_p1 -> deps_p1 -> deps
type deps_sn = deps_pn -> deps

let string_of_deps deps =
  String.concat ""
		(List.map
		   (fun dep ->
		    "("
		    ^ String.concat " "
				    (List.map Rdf.string_of_term dep)
		    ^ ")")
		   deps)
		
type sparql_p1 = Sparql.term -> Sparql.formula
type sparql_p2 = Sparql.term -> Sparql.term -> Sparql.formula
type sparql_pn = (arg * Sparql.term) list -> Sparql.formula
type sparql_s1 = sparql_p1 -> Sparql.formula
type sparql_s2 = sparql_p1 -> sparql_p1 -> Sparql.formula
type sparql_sn = sparql_pn -> Sparql.formula
type sparql_b1 = sparql_p2 -> Sparql.formula
type sparql_s = Sparql.formula

type 'a formula_hook = 'a -> Sparql.formula -> Sparql.formula
		  
let make_pat ?(hook : string formula_hook option) (v : string) (pat : Sparql.pattern) : Sparql.pattern =
  match hook with
  | None -> pat
  | Some h ->
     if pat = Sparql.empty
     then pat (* nothing to hook *)
     else
       Sparql.pattern_of_formula
         (h v (Sparql.Pattern pat))
				 
(* definitions to retrieve classes from focus *)
module WhichClass =
  struct
    let pattern_vars = ["c"]
    let intent_pattern ?(hook : string formula_hook option) () =
      make_pat ?hook "c"
	       Sparql.(union
			 [ rdf_type (var "c") (term_uri Rdf.rdfs_Class);
			   rdf_type (var "c") (term_uri Rdf.owl_Class) ])
    let pattern_of_term ?(hook : string formula_hook option) (t_opt : Rdf.term option) : Sparql.pattern (* maybe mepty *) =
      let init, t =
	match t_opt with
	| None -> true, Rdf.Bnode ""
	| Some t -> false, t in
      if Rdf.term_can_be_subject t
      then make_pat ?hook "c" Sparql.(rdf_type (term t) (var "c"))
      else Sparql.empty
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

    let filter_wikidata vp =
      Sparql.(filter (expr_func
		"strstarts"
		[expr_func "str" [var vp];
		 (string "http://www.wikidata.org/prop/direct/P" :> expr)]))
    let intent_pattern ?(hook : string formula_hook option) () =
      make_pat ?hook "p"
	       Sparql.(union
			 [ rdf_type (var "p") (term_uri Rdf.rdf_Property);
			   rdf_type (var "p") (term_uri Rdf.owl_ObjectProperty);
			   rdf_type (var "p") (term_uri Rdf.owl_DatatypeProperty) ])
    let pattern_of_term ?(hook : string formula_hook option) (t_opt : Rdf.term option) : Sparql.pattern  (* maybe empty *) =
      let init, t =
	match t_opt with
	| None -> true, Rdf.Bnode ""
	| Some t -> false, t in
      let make_pat vp pat =
	let pat =
	  if Rdf.config_wikidata_mode#value
	  then Sparql.(join [pat; filter_wikidata vp])
	  else pat in
	make_pat ?hook vp pat in
      Sparql.(union
		[ if Rdf.term_can_be_subject t
                  then make_pat "p" (triple (term t) (var "p") (bnode ""))
                  else empty;
                  
		  if init
                  then empty
		  else make_pat "ip" (triple (bnode "") (var "ip") (term t)) ])
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
		(path_uri Rdf.nary_subjectObject)
		(var po))
    let pattern_EO pe po =
      Sparql.(triple
		(var pe)
		(path_uri Rdf.nary_eventObject)
		(var po))
    let filter_wikidata pe po =
      Sparql.(join
		[ filter (expr_func "strstarts" [expr_func "str" [var pe]; (string "http://www.wikidata.org/prop/P" :> expr)]);
		  filter (expr_func "strstarts" [expr_func "str" [var po]; (string "http://www.wikidata.org/prop/statement/P" :> expr)]) ])
    let pattern_wikidata pe po =
      Sparql.(bnode_triples_as_pattern
		[ (path_uri Rdf.wikibase_claim :> pred), var pe;
		  (path_uri Rdf.wikibase_statementProperty :> pred), var po ])
	    
    let intent_pattern ?(hook : string formula_hook option) () : Sparql.pattern =
      if Rdf.config_wikidata_mode#value
      then make_pat ?hook "pe" (pattern_wikidata "pe" "po")
      else Sparql.(union [ make_pat ?hook "po" (pattern_SO "ps" "po");
			   make_pat ?hook "pe" (pattern_EO "pe" "po") ])
		 
    let pattern_of_term ?(hook : string formula_hook option) (t_opt : Rdf.term option) : Sparql.pattern (* maybe empty *) =
      let init, t =
	match t_opt with
	| None -> true, Rdf.Bnode ""
	| Some t -> false, t in
      if Rdf.config_wikidata_mode#value
      then
	let make_pat p1 p2 pat =
	  let pat = Sparql.join [pat; filter_wikidata p1 p2] in
	  make_pat ?hook p1 pat in
	let pat_wikidata =
	  Sparql.(union
		    [ if Rdf.term_can_be_subject t
                      then make_pat "pe" "po"
			     (triple (* forward: pe, po *)
				(term t)
				(var "pe")
				(bnode_triples
				   [ var "po", bnode "" ]))
                      else empty;
                      
		      if init
		      then empty
		      else join (* backward: pe, ps, po *)
			     [ make_pat "pe" "ps"
					(triple
					   (bnode "")
					   (var "pe")
					   (bnode_triples
					      [ var "ps", term t ])) ] (* binding 'ps' to distinguish orientation *)
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
	pat_wikidata
      else
	let pat_SO =
	  Sparql.(join
		    [ make_pat ?hook "po" (pattern_SO "ps" "po");
		      filter
			(exists (
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
			       ]))
		    ]) in
	let pat_EO =
	  Sparql.(union
		    [ if Rdf.term_can_be_subject t
                      then join
			     [ make_pat ?hook "pe" (pattern_EO "pe" "po");
			       filter (exists (
				           triple (* forward: pe, po *)
					     (term t)
					     (var "pe")
					     (bnode_triples
					        [ var "po", bnode "" ]))) ]
                      else empty;
                      
		      if init
		      then empty
		      else join (* backward: pe, ps, po *)
			     [ make_pat ?hook "pe" (pattern_EO "pe" "ps");
			       filter
				 (exists (
				      triple
					(bnode "")
					(var "pe")
					(bnode_triples
					   [ var "ps", term t ]))) (* binding 'ps' to distinguish orientation *)
			     ];
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
	Sparql.(union [pat_SO; pat_EO])
	    
    let increments_of_terms ~(init : bool) (lt : Rdf.term option list) : Lisql.increment list =
      (* ~init: for initial focus, remind to generate increments in all relevant directions S/P/O *)
      assert (List.length lt = List.length pattern_vars);
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
  let bnode = Sparql.bnode "" in
  let tS, args = try List.assoc S args, args with Not_found -> bnode, (S,bnode)::args in
  let tO, args = try List.assoc O args, args with Not_found -> bnode, (O,bnode)::args in
  match pred with
  | Class c -> Sparql.(rdf_type tS (term_uri c))
  | Prop p -> Sparql.(triple tS (path_uri p) tO)
  | SO (ps,po) ->
     let lpo = [] in
     let lpo =
       List.fold_right
	 (fun (v,t) lpo -> Sparql.(((var v :> pred), t) :: lpo))
	 var_args lpo in
     let lpo =
       List.fold_right
	 (fun (arg,t) lpo ->
	  match arg with
	  | S -> Sparql.(((path_uri ps :> pred), t) :: lpo)
	  | O -> Sparql.(((path_uri po :> pred), t) :: lpo)
	  | P -> lpo
	  | Q q -> Sparql.(((path_uri q :> pred), t) :: lpo))
	 args lpo in
     Sparql.bnode_triples_as_pattern lpo
  | EO (pe,po) ->
     let lpo = [] in
     let lpo =
       List.fold_right
	 (fun (v,t) lpo -> Sparql.(((var v :> pred), t) :: lpo))
	 var_args lpo in
     let lpo =
       List.fold_right
	 (fun (arg,t) lpo ->
	  match arg with
	  | S -> lpo
	  | O -> Sparql.(((path_uri po :> pred), t) :: lpo)
	  | P -> lpo
	  | Q q -> Sparql.(((path_uri q :> pred), t) :: lpo))
	 args lpo in
     Sparql.(triple
	       tS
	       (path_uri pe)
	       (bnode_triples lpo))

module WhichArg =
  struct
    let pattern_vars = ["pq"]

    let pattern_of_pred_args ?(hook : string formula_hook option) (pred : Lisql.pred) (args : (Lisql.arg * Rdf.term) list) : Sparql.pattern (* maybe empty *) =
      let filter_qualifier =
	match pred with
	| Class _ -> Sparql.empty
	| Prop _ -> Sparql.empty
	| SO (ps,po) -> Sparql.(filter (expr_not_in (var "pq") [term_uri Rdf.rdf_type; term_uri ps; term_uri po]))
	| EO (pe,po) ->
	   if Rdf.config_wikidata_mode#value
	   then Sparql.(filter (expr_func "strstarts" [expr_func "str" [var "pq"]; (string "http://www.wikidata.org/prop/qualifier/P" :> expr)]))
	   else Sparql.(filter (expr_not_in (var "pq") [term_uri Rdf.rdf_type; term_uri po])) in
      let valid_term_for_triple_subjects =
        match pred with
        | Class _ | Prop _ | EO _ ->
           ( match List.assoc_opt S args with
             | None -> true (* a blank node will be used *)
             | Some t -> Rdf.term_can_be_subject t )
        | SO _ -> true in
      if valid_term_for_triple_subjects
      then
        let pat =
          pattern_pred_args
	    pred
	    (List.map (fun (arg,t) -> (arg, Sparql.term t)) args)
	    ["pq", Sparql.bnode ""] in
        Sparql.(join
		  [ make_pat ?hook "pq"
		      (Sparql.join [ pat; filter_qualifier ]) ])
      else Sparql.empty
      
    let increments_of_terms (lt : Rdf.term option list) : Lisql.increment list =
      match lt with
      | [Some (Rdf.URI pq)] -> [Lisql.IncrArg pq]
      | _ -> []
  end
	   
let path_pred_args_argo ?(transitive = false) pred args argo =
  let path_transitive_opt path =
    if transitive
    then Sparql.path_transitive path
    else path in
  let uri_transitive_opt uri =
    if transitive
    then
      match Ontology.config_transitive_closure#value#info uri with
      | uri_star::_ -> Sparql.path_uri uri_star
      | _ -> Sparql.path_transitive (Sparql.path_uri uri)
    else Sparql.path_uri uri in
  let open Sparql in
  match pred, args, argo with
  | Prop p, S, O -> (uri_transitive_opt p :> pred)
  | Prop p, O, S -> path_inverse (uri_transitive_opt p)
  | SO (ps,po), S, O -> path_transitive_opt (path_seq (path_inverse (path_uri ps)) (path_uri po))
  | SO (po,ps), O, S -> path_transitive_opt (path_seq (path_inverse (path_uri po)) (path_uri ps))
  | EO (pe,po), S, O -> path_transitive_opt (path_seq (path_uri pe) (path_uri po))
  | EO (pe,po), O, S -> path_inverse (path_transitive_opt (path_seq (path_uri pe) (path_uri po)))
  | _ -> assert false (* from Lisql.toggle_hierarchy *)
	     
let form_pred state (pred : pred) : sparql_pn =
  (fun l -> Sparql.Pattern (pattern_pred_args pred l []))

let form_sim state pred args argo rank : sparql_p2 =
  let open Sparql in
  let path = path_pred_args_argo pred args argo in
  let interv_path = path_interv path 0 rank in
  (fun x y -> Pattern (triple x interv_path y))

    
let rec form_p1 state : annot elt_p1 -> deps_p1 * sparql_p1 = function
  | Is (annot,np) -> form_s1_as_p1 state np
  | Pred (annot,arg,pred,cp) ->
     let pred = form_pred state pred in
     let cp_deps, cp = form_sn state cp in
     (fun x -> cp_deps (fun l -> [x::l])),
     (fun x -> cp (fun l -> pred ((arg,x)::l)))
  | Type (annot,c) ->
     (fun x -> []),
     (fun x -> Sparql.Pattern (Sparql.rdf_type x (Sparql.term_uri c)))
  | Rel (annot,prop,ori,np) ->
     let p = Sparql.path_uri prop in
     let rel =
       match ori with
       | Fwd -> (fun x y -> Sparql.Pattern (Sparql.triple x p y))
       | Bwd -> (fun x y -> Sparql.Pattern (Sparql.triple y p x)) in
     let q_np_deps, q_np = form_s1 state np in
     (fun x -> q_np_deps (fun y -> [[x;y]])),
     (fun x -> q_np (fun y -> rel x y))
  | Hier (annot,id,pred,args,argo,np) ->
     let vy = state#id_labelling#get_id_var id in
     state#set_modif vy (Lisql.Unselect,Lisql.Unordered);
     let y = (Sparql.var vy :> Sparql.term) in
     let hier =
       let open Sparql in
       let trans_path = path_pred_args_argo ~transitive:true pred args argo in
       (fun x y -> Pattern (triple x trans_path y)) in
     let q_np_deps, q_np = form_s1 ~ignore_top:true state np in
     (fun x -> q_np_deps (fun z -> [[x;z]]) @ [[x; Rdf.Var vy]]),
     (fun x ->
      state#add_var vy;
      Sparql.formula_and_list [q_np (fun z -> hier x z); hier x y])
  | Sim (annot,np,pred,args,argo,rank) ->
     let q_deps, q = form_s1 state np in
     let sim = form_sim state pred args argo rank in
     (fun x -> q_deps (fun y -> [[y; x]])),
     (fun x -> q (fun y -> sim y x))
  | LatLong (annot,ll,id1,id2) ->
    let v1 = state#id_labelling#get_id_var id1 in
    let v2 = state#id_labelling#get_id_var id2 in
    let lat, long = Sparql.var v1, Sparql.var v2 in
    let f_ll = form_latlong ll in
    (fun x -> [[x; Rdf.Var v1; Rdf.Var v2]]),
    (fun x ->
     state#add_geoloc x v1 v2;
     f_ll x lat long)
  | Triple (annot,arg,np1,np2) ->
    let q_np1_deps, q_np1 = form_s1 state np1 in
    let q_np2_deps, q_np2 = form_s1 state np2 in
    (fun x -> q_np1_deps (fun y -> q_np2_deps (fun z -> [[x;y;z]]))),
    (fun x -> q_np1 (fun y -> q_np2 (fun z -> triple_arg arg x y z)))
  | Search (annot,c) ->
     (fun x -> []),
     (fun x -> search_constr_entity state#genvar x c OnlyIRIs)
  | Filter (annot,c,ft) ->
     (fun x -> []),
     (fun x -> filter_constr_entity state#genvar x c ft)
  | And (annot,lr) ->
     let lr_d_deps, lr_d = List.split (List.map (fun elt -> form_p1 state elt) lr) in
     (fun x -> List.concat (List.map (fun d_deps -> d_deps x) lr_d_deps)),
     (fun x -> Sparql.formula_and_list (List.map (fun d -> d x) lr_d))
  | Or (annot,lr) ->
    ( match annot#get_susp_focus_index with
    | Some i -> form_p1 state (List.nth lr i)
    | None ->
       let lr_d_deps, lr_d = List.split (List.map (fun elt -> form_p1 state elt) lr) in
       (fun x -> List.concat (List.map (fun d_deps -> d_deps x) lr_d_deps)),
       (fun x -> Sparql.formula_or_list (List.map (fun d -> d x) lr_d)) )
  | Maybe (annot,f) ->
    if annot#is_susp_focus
    then form_p1 state f
    else
      let d_deps, d = form_p1 state f in
      (fun x -> d_deps x),
      (fun x -> Sparql.formula_optional (d x))
  | Not (annot,f) ->
    if annot#is_susp_focus
    then form_p1 state f
    else
      let d_deps, d = form_p1 (Oo.copy state) f in
      (fun x -> d_deps x),
      (fun x -> Sparql.formula_not (d x))
  | In (annot,npg,f) ->
    let q_deps, q = form_s1 state npg in
    let d_deps, d = form_p1 state f in
    (fun x -> q_deps (fun g -> d_deps x |> List.map (fun dep -> g::dep))),
    (fun x -> q (fun g -> Sparql.formula_graph g (d x)))
  | InWhichThereIs (annot,np) ->
     let q_deps, q = form_s1 state np in
     (fun g -> q_deps (fun x -> []) |> List.map (fun dep -> g::dep)),
     (fun g -> Sparql.formula_graph g (q (fun x -> Sparql.True)))
  | IsThere annot ->
     (fun x -> []),
     (fun x -> Sparql.True)
and form_latlong = function
  | CustomLatLong (plat,plong) ->
     (fun x lat long ->
      Sparql.(formula_and
	(Pattern (triple x (path_uri plat) lat))
	(Pattern (triple x (path_uri plong) long))))
  | WikidataLatLong ->
     (fun x lat long -> Sparql.Pattern (Sparql.wikidata_lat_long x lat long))
and form_p1_opt state = function
  | None -> (fun x -> []), (fun x -> Sparql.True)
  | Some rel -> form_p1 state rel
and form_s1_as_p1 state : annot elt_s1 -> deps_p1 * sparql_p1 = function
  | Det (annot,det,rel_opt) ->
    let d1 = form_s2_as_p1 state det in
    let d2_deps, d2 = form_p1_opt state rel_opt in
    (fun x -> d2_deps x),
    (fun x -> Sparql.formula_and (d1 x) (d2 x))
  | AnAggreg (annot,idg,modifg,g,relg_opt,np) ->
    if annot#is_susp_focus
    then form_s1_as_p1 state np
    else
      ( match np with
      | Det (_, An (id, _, _), _)
      | AnAggreg (_, id, _, _, _, _) ->
	 let _d_deps, d = form_p1_opt state relg_opt in
	 form_aggreg_op state idg modifg g d id;
	 form_s1_as_p1 state np
      | _ -> assert false )
  | NAnd (annot,lr) ->
     let lr_d_deps, lr_d = List.split (List.map (fun elt -> form_s1_as_p1 state elt) lr) in
     (fun x -> List.concat (List.map (fun d_deps -> d_deps x) lr_d_deps)),
     (fun x -> Sparql.formula_and_list (List.map (fun d -> d x) lr_d))
  | NOr (annot,lr) ->
    ( match annot#get_susp_focus_index with
    | Some i -> form_s1_as_p1 state (List.nth lr i)
    | None ->
       let lr_d_deps, lr_d = List.split (List.map (fun elt -> form_s1_as_p1 state elt) lr) in
       (fun x -> List.concat (List.map (fun d_deps -> d_deps x) lr_d_deps)),
       (fun x -> Sparql.formula_or_list (List.map (fun d -> d x) lr_d)) )
  | NMaybe (annot,f) ->
    if annot#is_susp_focus
    then form_s1_as_p1 state f
    else
      let d_deps, d = form_s1_as_p1 state f in
      (fun x -> d_deps x),
      (fun x -> Sparql.formula_optional (d x))
  | NNot (annot,f) ->
    if annot#is_susp_focus
    then form_s1_as_p1 state f
    else
      let d_deps, d = form_s1_as_p1 (Oo.copy state) f in
      (fun x -> d_deps x),
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
  | Class c -> (fun x -> Sparql.(Pattern (rdf_type x (term_uri c))))
and form_sn state : annot elt_sn -> deps_sn * sparql_sn = function
  | CNil annot ->
     (fun p -> p []),
     (fun p -> p [])
  | CCons (annot,arg,np,cp) ->
     let np_deps, np = form_s1 state np in
     let cp_deps, cp = form_sn state cp in
     (fun p -> np_deps (fun x -> cp_deps (fun l -> p (x::l)))),
     (fun p -> np (fun x -> cp (fun l -> p ((arg,x)::l))))
  | CAnd (annot,lr) ->
     let lr_q_deps, lr_q = List.split (List.map (fun elt -> form_sn state elt) lr) in
     (fun p -> List.concat (List.map (fun q_deps -> q_deps p) lr_q_deps)),
     (fun p -> Sparql.formula_and_list (List.map (fun q -> q p) lr_q))
  | COr (annot,lr) ->
    ( match annot#get_susp_focus_index with
    | Some i -> form_sn state (List.nth lr i)
    | None ->
       let lr_q_deps, lr_q = List.split (List.map (fun elt -> form_sn state elt) lr) in
       (fun p -> List.concat (List.map (fun q_deps -> q_deps p) lr_q_deps)),
       (fun p -> Sparql.formula_or_list (List.map (fun q -> q p) lr_q)) )
  | CMaybe (annot,f) ->
    if annot#is_susp_focus
    then form_sn state f
    else
      let q_deps, q = form_sn state f in
      (fun p -> q_deps p),
      (fun p -> Sparql.formula_optional (q p))
  | CNot (annot,f) ->
    if annot#is_susp_focus
    then form_sn state f
    else
      let q_deps, q = form_sn (Oo.copy state) f in
      (fun p -> q_deps p),
      (fun p -> Sparql.formula_not (q p))
and form_s1 ?(ignore_top = false) state : annot elt_s1 -> deps_s1 * sparql_s1 = function
  | Det (annot,det,rel_opt) ->
     let qu_deps, qu = form_s2 state det in
     let d1_deps, d1 = form_p1_opt state rel_opt in
     (fun d -> qu_deps d1_deps d),
     (if ignore_top && is_top_s2 det && is_top_p1_opt rel_opt
      then (fun d -> Sparql.True)
      else (fun d -> qu d1 d))
  | AnAggreg (annot,idg,modifg,g,relg_opt,np) ->
    if annot#is_susp_focus
    then form_s1 state np
    else
      ( match np with
      | Det (_, An (id, _, _), _)
      | AnAggreg (_, id, _, _, _, _) ->
	 let _d_deps, d = form_p1_opt state relg_opt in
	form_aggreg_op state idg modifg g d id;
	form_s1 state np 
     | _ -> assert false )
  | NAnd (annot,lr) ->
     let lr_q_deps, lr_q = List.split (List.map (fun elt -> form_s1 ~ignore_top state elt) lr) in
     (fun d -> List.concat (List.map (fun q_deps -> q_deps d) lr_q_deps)),
     (fun d -> Sparql.formula_and_list (List.map (fun q -> q d) lr_q))
  | NOr (annot,lr) ->
    ( match annot#get_susp_focus_index with
    | Some i -> form_s1 ~ignore_top state (List.nth lr i)
    | None ->
       let lr_q_deps, lr_q = List.split (List.map (fun elt -> form_s1 ~ignore_top state elt) lr) in
       (fun d -> List.concat (List.map (fun q_deps -> q_deps d) lr_q_deps)),
       (fun d -> Sparql.formula_or_list (List.map (fun q -> q d) lr_q)) )
  | NMaybe (annot,f) ->
    if annot#is_susp_focus
    then form_s1 ~ignore_top state f
    else
      let q_deps, q = form_s1 ~ignore_top state f in
      (fun d -> q_deps d),
      (fun d -> Sparql.formula_optional (q d))
  | NNot (annot,f) ->
    if annot#is_susp_focus
    then form_s1 ~ignore_top state f
    else
      let q_deps, q = form_s1 ~ignore_top (Oo.copy state) f in
      (fun d -> q_deps d),
      (fun d -> Sparql.formula_not (q d))
(*      
  | NRelax f ->
    state#set_relax true;
    let q = form_s1 state f in
    state#set_relax false;
    q
*)
and form_s2 state : elt_s2 -> deps_s2 * sparql_s2 = function
  | Term term ->
     let t = Sparql.term term in
     (fun d1 d2 -> d1 term @ d2 term),
     (fun d1 d2 -> Sparql.formula_and (d1 t) (d2 t))
  | An (id, modif, head) ->
    let qhead = form_head state head in
    let v = state#id_labelling#get_id_var id in
    state#set_modif v modif;
    let t = (Sparql.var v :> Sparql.term) in
    (fun d1 d2 -> let t = Rdf.Var v in d1 t @ d2 t),
    (fun d1 d2 -> state#add_var v; qhead t (Sparql.formula_and (d2 t) (d1 t))) (* YES: d2 - d1 *)
  | The id ->
    let v = state#id_labelling#get_id_var id in
    let t = (Sparql.var v :> Sparql.term) in
    (fun d1 d2 -> let t = Rdf.Var v in d1 t @ d2 t),
    (fun d1 d2 -> Sparql.formula_and (d2 t) (d1 t)) (* YES: d2 - s1 *)
and form_head state : elt_head -> (Sparql.term -> Sparql.formula -> Sparql.formula) = function
  | Thing ->
    (fun x form -> Sparql.formula_bind x form)
  | Class c ->
    (fun x form -> Sparql.formula_and (Sparql.Pattern (Sparql.rdf_type x (Sparql.term_uri c))) form)
and form_aggreg_op state idg modifg g (d : sparql_p1) id : unit =
  let vg = state#id_labelling#get_id_var idg in
  let v = state#id_labelling#get_id_var id in
  state#set_aggreg v (vg, g, (d (Sparql.var vg :> Sparql.term)));
  state#set_modif vg modifg
and form_dim state
    : annot elt_aggreg ->
      deps * Rdf.term option (* non-var term in dim *)
      * Sparql.projection option * Rdf.var option (* group by var *)
      * Sparql.formula (* relative *) = function
  | ForEachResult annot -> assert false
  | ForEach (annot,id,modif,rel_opt,id2) ->
    let v = state#id_labelling#get_id_var id in
    state#set_modif v modif;
    let d_deps, d = form_p1_opt state rel_opt in
    let v2 = state#id_labelling#get_id_var id2 in
    d_deps (Rdf.Var v), None,
    Some (`Expr (Sparql.var v2 :> Sparql.expr), v), Some v2,
    (d (Sparql.var v2 :> Sparql.term))
  | ForTerm (annot,t,id2) ->
    let v2 = state#id_labelling#get_id_var id2 in
    [], Some t,
    None, None,
    Sparql.Filter (Sparql.expr_comp "=" (Sparql.var v2) (Sparql.term t))
  | _ -> assert false
and form_aggreg state : annot elt_aggreg -> deps * Sparql.projection * Rdf.var * Sparql.expr (* having expr *) = function
  | TheAggreg (annot,id,modif,g,rel_opt,id2) ->
    let v = state#id_labelling#get_id_var id in
    state#set_modif v modif;
    let d_deps, d = form_p1_opt state rel_opt in
    let v2 = state#id_labelling#get_id_var id2 in
    let sparql_g = sparql_aggreg g in
    let t_v2 = (Sparql.var v2 :> Sparql.term) in
    (*[Rdf.Var v; Rdf.Var v2] ::*) d_deps (Rdf.Var v),
    (`Aggreg (sparql_g, t_v2), v), v2, Sparql.expr_of_formula (d (Sparql.term_aggreg sparql_g t_v2))
  | _ -> assert false
and form_expr_list state : annot elt_expr -> Rdf.var list * Sparql.expr list = function (* non-deterministic semantics *)
  | Undef annot -> [], []
  | Const (annot,t) -> [], [(Sparql.term t :> Sparql.expr)]
  | Var (annot,id) ->
     let v = state#id_labelling#get_id_var id in
     [v], [(Sparql.var v :> Sparql.expr)]
  | Apply (annot,func,args) ->
    if not annot#defined
    then [], []
    else
      ( match annot#focus_pos with
	| `Above (true, Some pos) ->
	   form_expr_list state (snd (List.nth args (pos-1)))
	| _ ->
	   let l_lv, sparql_list_args =
	     List.split
	       (List.map
		  (fun (conv_opt,arg_expr) ->
		   let lv, le = form_expr_list state arg_expr in
		   lv,
		   List.map (sparql_converter conv_opt) le)
		  args) in
	   List.concat l_lv,
	   Common.list_fold_prod
	     (fun res sparql_args -> expr_apply func sparql_args :: res)
	     [] sparql_list_args )
  | Choice (annot,le) ->
    ( match annot#focus_pos with
    | `Above (true, Some pos) -> form_expr_list state (try List.nth le pos with _ -> assert false)
    | _ ->
       let l_lv, l_le = List.split (List.map (form_expr_list state) le) in
       List.concat l_lv,
       List.concat l_le )
and form_s state (s : annot elt_s) : seq_view * deps * Sparql.view =
  let (_, view as seq_view), lr =
    match s with
    | Return (annot,np) -> (0, Atom (annot#ids,0)), [s]
    | Seq (annot,lr) -> (match annot#seq_view with Some seq_view -> seq_view | None -> assert false), lr
    | _ -> assert false in
  let deps, view = form_view state lr view in
  seq_view, deps, view
and form_view state (lr : annot elt_s list) (v : view) : deps * Sparql.view =
  let lv =
    match v with
    | Unit -> []
    | Atom _ -> [v]
    | InlineAggregs _ -> [v]
    | Aggreg _ -> [v]
    | Join (_,lv) -> lv in
  form_view_list state lr [] Sparql.empty_view lv
and form_view_list state (lr : annot elt_s list) (deps : deps) (view : Sparql.view) : view list -> deps * Sparql.view =
  function
  | [] -> deps, view
  | Unit::lv -> form_view_list state lr deps view lv
  | Atom (ids,sid)::lv ->
    ( match List.nth lr sid with
    | Return (annot,np) ->
      let ids = annot#ids in
      let lx =
	ids.seq
	|> List.filter (fun id -> Ids.mem id ids.defs)
	|> List.map state#id_labelling#get_id_var in
      let q_deps, q = form_s1 state np in
      let form = q (fun t -> Sparql.True) in
      let deps = q_deps (fun x -> []) @ deps in
      form_view_list state lr deps (Sparql.join_views [view; Sparql.simple_view lx form]) lv
    | SExpr (annot,name,id,modif,expr,rel_opt) ->
      let x = state#id_labelling#get_id_var id in
      state#set_modif x modif;
      let ly, sparql_expr_list = form_expr_list state expr in
      let deps, form =
	if sparql_expr_list = []
	then deps, Sparql.True
	else
	  let dep0 = List.map (fun v -> Rdf.Var v) (x::ly) in (* x depends on expression vars *)
	  let d_deps1, d = form_p1_opt state rel_opt in
	  dep0 :: d_deps1 (Rdf.Var x) @ deps,
	  Sparql.formula_and
	    (Sparql.formula_or_list
	       (List.map
		  (fun sparql_expr -> Sparql.Pattern (Sparql.bind sparql_expr (Sparql.var x)))
		  sparql_expr_list))
	    (d (Sparql.var x :> Sparql.term)) in
      form_view_list state lr deps (Sparql.join_views [view; Sparql.simple_view [x] form]) lv
    | SFilter (annot,id,expr) ->
      let x = state#id_labelling#get_id_var id in
      let ly, sparql_expr_list = form_expr_list state expr in
      let deps, view =
	if sparql_expr_list = []
	then deps, view
	else
	  let lx, deps, form =
	    match annot#focus_pos with
	    | `Above _ ->
	       let dep0 = List.map (fun v -> Rdf.Var v) (x::ly) in
	       [x], dep0 :: deps,
	       Sparql.formula_or_list
		 (List.map (fun sparql_expr ->
			    Sparql.Pattern (Sparql.bind sparql_expr (Sparql.var x)))
			   sparql_expr_list)
	    | _ ->
	       [], deps,
	       Sparql.Filter (Sparql.log_or sparql_expr_list) in
	  deps, Sparql.join_views [view; Sparql.simple_view lx form] in
      form_view_list state lr deps view lv
    | _ -> assert false )
  | InlineAggregs (ids,sid,_ids2)::lv ->
    ( match List.nth lr sid with
    | SAggreg (annot, aggregs) ->
      assert (List.exists is_ForEachResult aggregs);
      let aggregs = List.filter is_aggreg aggregs in 
      let l_aggregs = List.map (form_aggreg state) aggregs in
      let ldeps1, lx2 =
	List.split
	  (List.map (fun (deps_aggreg,_,x2,_) -> deps_aggreg, x2) l_aggregs) in
      let vars_dims =
	let sq = view () in (* TODO: avoid this spurious computation *)
	sq.Sparql.projections
	|> List.map snd (* projected variables in view *)
	|> List.filter (fun x -> not (List.mem x lx2)) in
      let deps =
	List.fold_left
	  (fun deps (deps_aggreg,proj,_,_) ->
	   let new_dep = List.map (fun v -> Rdf.Var v) (vars_dims @ [snd proj]) in
	   new_dep :: deps_aggreg @ deps)
	   (* dependency between each aggregate and all dimensions *)
	  deps l_aggregs in
      let projections_aggregs = List.map (fun (_,proj,_,_) -> proj) l_aggregs in
      let havings_aggregs = List.map (fun (_,_,_,hav) -> hav) l_aggregs in
      let view =
	(fun ?limit () ->
	  let sq = view ?limit () in
	  { sq with
	    Sparql.projections = List.filter (fun (_,x) -> List.mem x vars_dims) sq.Sparql.projections @ projections_aggregs;
	    groupings = List.filter (fun x -> List.mem x vars_dims) sq.Sparql.groupings;
	    having = Sparql.log_and (sq.Sparql.having :: havings_aggregs) }) in
      form_view_list state lr deps view lv
    | _ -> assert false )
  | Aggreg (ids,sid,v2)::lv ->
    let deps2, aggregated_view = form_view state lr v2 in
    let deps = deps2 @ deps in
    ( match List.nth lr sid with
    | SAggreg (annot,dims_aggregs) ->
      let dims = List.filter is_dim dims_aggregs in
      let aggregs = List.filter is_aggreg dims_aggregs in
      let l_dims = List.map (form_dim state) dims in
      let l_aggregs = List.map (form_aggreg state) aggregs in
      let deps, terms_dims, projections_dims, vars_dims =
	List.fold_right
	  (fun (deps_dim,term_opt,proj_opt,_,_) (deps,lt,lproj,lv) ->
	   let deps = deps_dim@deps in
	   let lt = match term_opt with None -> lt | Some t -> t::lt in
	   let lproj, lv =
	     match proj_opt with
	     | None -> lproj, lv
	     | Some proj -> proj::lproj, snd proj :: lv in
	   deps,lt,lproj,lv)
	  l_dims (deps,[],[],[]) in
      let deps, projections_aggregs =
	List.fold_right
	  (fun (deps_aggreg,proj,_,_) (deps,lproj) ->
	   let new_dep = terms_dims @ List.map (fun v -> Rdf.Var v) (vars_dims @ [snd proj]) in
	   let deps = new_dep :: deps_aggreg @ deps in
	   (* dependency between each aggregate and all dimensions *)
	   deps, proj::lproj)
	  l_aggregs (deps,[]) in
      let projections = projections_dims @ projections_aggregs in
      let groupings_dims =
	List.fold_right
	  (fun (_,_,_,group_opt,_) res ->
	   match group_opt with None -> res | Some group -> group::res)
	  l_dims [] in
      let lf_dims = List.map (fun (_,_,_,_,hav) -> hav) l_dims in
      let havings_aggregs = List.map (fun (_,_,_,hav) -> hav) l_aggregs in
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
				 (fun (_,_,_,v2_opt,_) res -> match v2_opt with None -> res | Some v2 -> (`Bare,v2)::res) l_dims
				 (List.map (fun (_,_,v2,_) -> (`Bare,v2)) l_aggregs))
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
      form_view_list state lr deps (Sparql.join_views [view; view_aggreg]) lv
    | _ -> assert false)
  | Join (_,lv1)::lv -> form_view_list state lr deps view (lv1@lv)

    
type template = ?hook:(Sparql.term formula_hook) ->
		froms:(Rdf.uri list) ->
		?limit:int -> unit -> string

(* auxiliary function factorizing [make_query] and [make_query_count] *)
let make_query_formula (focus_term_opt : Rdf.term option) (view : Sparql.view) =
  (fun ?hook ?limit () ->
    let sq_view = view ?limit () in
    let sq_view = (* when sq_view makes no proper computation *)
      if sq_view.Sparql.having = Sparql.log_true &&
	List.for_all (function (`Bare,_) -> true | _ -> false) sq_view.Sparql.projections (* implies there are no relevant group-by *)
      then (* and its contents is itself a subquery *)
	match sq_view.Sparql.formula with
	| Sparql.Subquery sq -> sq (* use that subquery instead *)
	| _ -> sq_view
      else sq_view in
    let form_hook =
      let view_form = sq_view.Sparql.formula in
      match focus_term_opt, hook with
      | Some (Rdf.Var v), Some f_hook ->
	 f_hook (Sparql.var v :> Sparql.term) view_form
      | _ -> view_form in
    sq_view, form_hook)

let make_query state (focus_term_opt : Rdf.term option) (view : Sparql.view) : template =
  (fun ?hook ~froms ?limit () ->
   let sq_view, form_hook = make_query_formula focus_term_opt view ?hook ?limit () in
    let visible_projections =
      List.filter
	(fun (_,v) -> state#project v = Select || focus_term_opt = Some (Rdf.Var v))
	sq_view.Sparql.projections in
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
      ?limit
      ~orderings
      (Sparql.pattern_of_formula form_hook) in
    (query :> string))

let make_query_count state (focus_term_opt : Rdf.term option) (view : Sparql.view) : Rdf.var -> template =
  (fun v_count ?hook ~froms ?limit () ->
   let sq_view, form_hook = make_query_formula focus_term_opt view ?hook ?limit () in
    let visible_projections =
      List.filter
	(fun (_,v) -> v = v_count && (state#project v = Select || focus_term_opt = Some (Rdf.Var v)))
	sq_view.Sparql.projections in
    let v, pattern =
      match visible_projections with
      | [`Bare, v] ->
	 v, Sparql.pattern_of_formula form_hook
      | [(`Aggreg _|`Expr _), v] ->
	 v, Sparql.pattern_of_subquery
	      (Sparql.make_subquery
		 ~projections:visible_projections
		 ~groupings:sq_view.Sparql.groupings
		 ~having:sq_view.Sparql.having
		 form_hook)
      | _ -> assert false in
    let query =
      Sparql.select
	~projections:[`Aggreg (Sparql.DistinctCOUNT, (Sparql.var v :> Sparql.term)), "count"]
	~froms
	pattern in
    (query :> string))

	     
type s_sparql =
  { state : state;
    focus_term_opt : Rdf.term option;
    focus_graph_opt : Rdf.term option;
    focus_pred_args_opt : (pred * (arg * Rdf.term) list) option;
    deps : deps;
    query_opt : template option;
    query_count_opt : (Rdf.var -> template) option;
    query_class_opt : template option;
    query_prop_opt : template option;
    query_pred_opt : template option;
    query_arg_opt : template option;
    seq_view : seq_view }
    
let s_annot (id_labelling : Lisql2nl.id_labelling) (fd : focus_descr) (s_annot : annot elt_s) : s_sparql =
  let state = new state id_labelling in
  let seq_view, deps, view = form_s state s_annot in
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
  let query_opt, query_count_opt =
    if Sparql.is_empty_view view
    then None, None
    else Some (make_query state focus_term_opt view),
	 Some (make_query_count state focus_term_opt view) in
  let query_incr_opt (lx : Rdf.var list) (make_pattern : Rdf.term -> Sparql.pattern) =
    let _ = assert (lx <> []) in
    let x = List.hd lx in
    match focus_term_opt with
    | Some t when fd#incr -> (* no increments for this focus term (expressions, aggregations) *)
      let tx = (Sparql.var x :> Sparql.term) in
      Some (fun ?(hook=(fun tx form -> form)) ~froms ?limit () ->
	let form_x = Sparql.Pattern (make_pattern t) in
	let form_x = match focus_graph_opt with None -> form_x | Some tg -> Sparql.formula_graph (Sparql.term tg) form_x in
	let form_x =
	  match focus_term_opt with
	  | Some (Rdf.Var _) -> Sparql.formula_and (Sparql.formula_of_view ?limit view) form_x
	  | _ -> form_x in
	let form_x = hook tx form_x in
	let projections = List.map (fun x -> (`Bare,x)) lx in
	(Sparql.select ~projections ~froms ?limit
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
    deps;
    query_opt;
    query_count_opt;
    query_class_opt;
    query_prop_opt;
    query_pred_opt;
    query_arg_opt;
    seq_view }
