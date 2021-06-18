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
open Lisql_annot

open Js_of_ocaml
open Js
open Jsutils

exception TODO
       
(* configuration : language *)

let config_lang =
  let key = "lang" in
  let select_selector = "#lang-select" in
  let default = "en" in
object (self)
  inherit Config.select_input ~key ~select_selector ~default ()

  method grammar : Grammar.grammar =
    match self#value with
    | "fr" -> Grammar.french
    | "es" -> Grammar.spanish
    | "nl" -> Grammar.dutch
    | _ -> Grammar.english
end

let config_show_datatypes = new Config.boolean_input ~key:"show_datatypes" ~input_selector:"#input-show-datatypes" ~default:false ()
  
(* NL generation from focus *)

type word =
  [ `Thing
  | `Relation
  | `Entity of Rdf.uri * string
  | `Literal of string
  | `TypedLiteral of string * string (* lexical value, datatype/lang *)
  | `Blank of string
  | `Class of Rdf.uri * string
  | `Prop of Rdf.uri * string
  | `Nary of Rdf.uri * string
  | `Func of string
  | `Op of string
  | `Undefined
  | `FocusName
  | `FocusSpan of Lisql.increment (* increment in which is used this FocusSpan word *) ]

let word_text_content grammar : word -> string = function
  | `Thing -> grammar#thing
  | `Relation -> grammar#relation
  | `Entity (uri,s) -> s
  | `Literal s -> s
  | `TypedLiteral (s, dt) -> if config_show_datatypes#value then s ^ " (" ^ dt ^ ")" else s
  | `Blank id -> id
  | `Class (uri,s) -> s
  | `Prop (uri,s) -> s
  | `Nary (uri,s) -> s
  | `Func s -> s
  | `Op s -> s
  | `Undefined -> "?"
  | `FocusSpan _ -> "__"
  | `FocusName -> "thing"

type ng_label =
  [ `Word of word
  | `Expr of annot elt_expr
  | `Ref of Lisql.id
  | `Gen of ng_label * word
  | `Of of word * ng_label
  | `AggregNoun of word * ng_label
  | `AggregAdjective of word * ng_label
  | `Hierarchy of ng_label
  | `Nth of int * ng_label ]
    
type s =
  [ `Return of np
  | `ThereIs of np
  | `ThereIs_That of np * s
  | `Truth of np * vp
  | `PP of pp * s
  | `Where of np (* when expr np acts as a sentence *)
  | `For of np * s
  | `Seq of s list
  | `And of s list
  | `Or of s list
  | `Not of s
  | `Maybe of s
  | `Focus of annot * s ]
and np =
  [ `Void
  | `PN of word * rel
  | `This
  | `TheFactThat of s
  | `Label of ng_label * word option
  | `Qu of qu * adj * ng
  | `QuOneOf of qu * word list
  | `Expr of adj * Grammar.func_syntax * np list * rel
  | `And of np list
  | `Or of np list
  | `Choice of adj * np list * rel
  | `Maybe of np
  | `Not of np
  | `Focus of annot * np ]
and ng =
  [ `That of word * rel
  | `LabelThat of ng_label * rel
  | `OfThat of word * np * rel
  | `Aggreg of bool * ng_aggreg * ng (* the bool indicates suspension *)
  | `Focus of annot * ng ]
and qu = [ `A | `Any of bool | `The | `Every | `Each | `All | `One | `No of bool ]
and adj =
  [ `Nil
  | `Order of word
  | `Optional of bool * adj
  | `Adj of adj * word ]
and ng_aggreg =
  [ `AdjThat of word * rel
  | `NounThatOf of word * rel ]
and rel =
  [ `Nil
  | `That of vp
  | `ThatS of s
  | `Whose of ng * vp
  | `PrepWhich of word * s
  | `AtWhichNoun of word * s
  (*  | `Of of np *)
  | `PP of pp list
  | `Ing of word * np * pp list
  | `InWhich of s
  | `And of rel list
  | `Or of rel list
  | `Maybe of rel
  | `Not of rel
  | `In of np * rel
  | `Ellipsis
  | `Focus of annot * rel ]
and vp =
  [ `IsNP of np * pp list
  | `IsPP of pp
  | `IsTheNounCP of word * cp
  | `IsAdjCP of word * cp
  | `IsInWhich of s
  | `HasProp of word * np * pp list
  | `HasPropCP of word * cp
  | `Has of np * pp list
  | `HasCP of cp
  | `VT of word * np * pp list
  | `VT_CP of word * cp
  | `Subject of np * vp (* np is the subject of vp *)
  | `And of vp list
  | `Or of vp list (* the optional int indicates that the disjunction is in the context of the i-th element *)
  | `Maybe of vp (* the bool indicates whether negation is suspended *)
  | `Not of vp (* the bool indicates whether negation is suspended *)
  | `EpsilonHead of vp
  | `In of np * vp
  | `Ellipsis
  | `Focus of annot * vp ]
and cp =
  [ `Nil
  | `Cons of pp * cp
  | `And of cp list
  | `Or of cp list
  | `Not of cp
  | `Maybe of cp
  | `Focus of annot * cp ]
and pp =
  [ `Bare of np
  | `Prep of word * np
  | `AtNoun of word * np
  | `At of np
  | `PrepBin of word * np * word * np ]

let top_adj : adj = `Nil
let top_rel : rel = `Nil
let top_np : np = `Qu (`A, `Nil, `That (`Thing, top_rel))
let top_expr : np = `PN (`Undefined, top_rel)
let top_s : s = `Return top_np

let focus_span (incr : Lisql.increment) : word = `FocusSpan incr
let focus_span_np (incr : Lisql.increment) : np = `PN (`FocusSpan incr, top_rel)
let focus_name : word = `FocusName
let focus_name_ng : ng = `That (`FocusName, top_rel)
let undefined_np : np = `PN (`Undefined, top_rel)

let np_of_word w : np = `PN (w, top_rel)
let np_of_literal l : np = np_of_word (`Literal l)

let nl_and = function
  | [] -> assert false
  | [x] -> x
  | l -> `And l

let nl_is : np -> vp = fun np -> `IsNP (np, [])
let nl_something : rel -> np = fun rel -> `Qu (`A, `Nil, `That (`Thing, rel))
let nl_that : vp -> rel = fun vp -> `That vp
let nl_there_is : np -> s = fun np -> `ThereIs np
	   
(* verbalization of terms, classes, properties *)

let word_of_entity uri = `Entity (uri, Lexicon.entity_label uri)
let word_of_class uri = `Class (uri, Lexicon.class_label uri)
let word_syntagm_of_property grammar uri =
  let synt, name = Lexicon.property_label uri in
  `Prop (uri, name), synt
let word_syntagm_of_pred_uri grammar uri =
  let synt, name = Lexicon.property_label uri in
  `Nary (uri,name), synt
let word_syntagm_of_arg_uri grammar uri =
  let synt, name = Lexicon.arg_label uri in
  `Nary (uri,name), synt

let word_syntagm_of_pred grammar (pred : pred) =
  match pred with
  | Class c -> word_of_class c, `Noun
  | Prop p -> word_syntagm_of_property grammar p
  | SO (ps,po) -> word_syntagm_of_pred_uri grammar po
  | EO (pe,po) -> word_syntagm_of_pred_uri grammar pe

let rec word_of_term = function
  | Rdf.URI uri -> word_of_entity uri
  | Rdf.Number (f,s,dt) -> word_of_term (if dt="" then Rdf.PlainLiteral (s,"") else Rdf.TypedLiteral (s,dt))
  | Rdf.TypedLiteral (s,dt) -> `TypedLiteral (s, Lexicon.class_label dt)
  | Rdf.PlainLiteral (s,"") -> `Literal s
  | Rdf.PlainLiteral (s,lang) -> `TypedLiteral (s,lang)
  | Rdf.Bnode id -> `Blank id (* should not occur *)
  | Rdf.Var v -> assert false (*`Id (0, `Var v)*) (* should not occur *)

let string_of_term = function
  | Rdf.URI uri -> Lexicon.entity_label uri
  | Rdf.Number (f,s,dt) -> s
  | Rdf.TypedLiteral (s,dt) -> s
  | Rdf.PlainLiteral (s,_) -> s
  | Rdf.Bnode id -> id (* should not occur *)
  | Rdf.Var v -> assert false

let string_of_input_type grammar = function
  | IRIInput -> grammar#uri
  | StringInput -> grammar#string
  | FloatInput -> grammar#number
  | IntegerInput -> grammar#integer
  | DateInput -> grammar#date
  | TimeInput -> grammar#time
  | DateTimeInput -> grammar#date_and_time
  | DurationInput -> grammar#duration
    
let aggreg_syntax grammar g =
  let qu, noun, adj_opt = grammar#aggreg_syntax g in
  let noun_word = if g=Sample then `Op noun else `Func noun in
  let adj_word_opt = match adj_opt with None -> None | Some adj -> Some (if g=Sample then `Op adj else `Func adj) in
  qu, noun, adj_opt, noun_word, adj_word_opt

let word_of_aggreg grammar g =
  let _, _, _, noun_word, adj_word_opt = aggreg_syntax grammar g in
  match adj_word_opt with
  | Some adj_word -> adj_word
  | _ -> noun_word

let string_of_func grammar func =
  match grammar#func_syntax func with
  | `Noun s -> s
  | `Prefix s -> s
  | `Infix s -> s
  | `Brackets (s1,s2) -> String.concat " " [s1;s2]
  | `Pattern l ->
    String.concat " "
      (List.map
	 (function
	 | `Kwd s -> s
	 | `Func s -> s
	 | `Arg i -> "_")
	 l)

let word_of_order grammar = function
  | Unordered -> `Op ""
  | Highest _ -> `Op grammar#order_highest
  | Lowest _ -> `Op grammar#order_lowest

let word_of_selection_op grammar  = function
  | AndSel | NAndSel -> `Op grammar#and_
  | OrSel | NOrSel -> `Op grammar#or_
  | AggregSel -> `Op ""
		 
let word_of_incr grammar = function
  | IncrSelection (selop,_) -> word_of_selection_op grammar selop
  | IncrInput (s,dt) -> `Op (string_of_input_type grammar dt)
  | IncrTerm t -> word_of_term t
  | IncrId (id,_) -> `Thing
  | IncrPred (arg,pred) -> fst (word_syntagm_of_pred grammar pred)
  | IncrArg q -> fst (word_syntagm_of_arg_uri grammar q)
  | IncrType c -> word_of_class c
  | IncrRel (p,_) -> fst (word_syntagm_of_property grammar p)
  | IncrLatLong _ -> `Op grammar#geolocation
  | IncrTriple _ -> `Relation
  | IncrTriplify -> `Relation
  | IncrHierarchy trans_rel -> `Op grammar#in_
  | IncrSim (pred,args,argo) -> fst (word_syntagm_of_pred grammar pred)
  | IncrSimRankIncr -> `Op grammar#rank
  | IncrSimRankDecr -> `Op grammar#rank
  | IncrAnything -> `Op grammar#anything
  | IncrThatIs -> `Op grammar#is
  | IncrSomethingThatIs -> `Op grammar#something
  | IncrAnd -> `Op grammar#and_
  | IncrDuplicate -> `Op grammar#and_
  | IncrOr -> `Op grammar#or_
  | IncrChoice -> `Op grammar#choice
  | IncrMaybe -> `Op grammar#optionally
  | IncrNot -> `Op grammar#not_
  | IncrIn -> `Op grammar#according_to
  | IncrInWhichThereIs -> `Op grammar#according_to
  | IncrUnselect -> `Op grammar#any
  | IncrOrder o -> word_of_order grammar o
  | IncrForeach -> `Thing
  | IncrAggreg g -> word_of_aggreg grammar g
  | IncrForeachResult -> `Op grammar#result
  | IncrForeachId id -> `Thing
  | IncrAggregId (g,id) -> word_of_aggreg grammar g
  | IncrFuncArg (is_pred,func,arity,pos,_,_) -> `Op (string_of_func grammar func)
  | IncrName name -> `Op "="

(* verbalization of IDs *)

type id_label = Rdf.var * ng_label
type id_labelling_list = (Lisql.id * [`Labels of id_label list | `Alias of Lisql.id]) list

let rec get_id_labelling (id : Lisql.id) (lab : id_labelling_list) : id_label list =
  try
    match List.assoc id lab with
    | `Labels ls -> ls
    | `Alias id2 -> get_id_labelling id2 lab
  with Not_found -> []

let var_of_uri (uri : Rdf.uri) : string =
  match Regexp.search (Regexp.regexp "[A-Za-z0-9_]+$") uri 0 with
    | Some (i,res) -> Regexp.matched_string res
    | None -> "thing"

let var_of_pred (pred : pred) : string =
  match pred with
  | Class c -> var_of_uri c
  | Prop p -> var_of_uri p
  | SO (ps,po) -> var_of_uri po
  | EO (pe,po) -> var_of_uri pe
		
let var_of_aggreg = function
  | NumberOf -> "number_of"
  | ListOf -> "list_of"
  | Sample -> "sample"
  | Total _ -> "total"
  | Average _ -> "average"
  | Maximum _ -> "maximum"
  | Minimum _ -> "minimum"

let rec labelling_p1 grammar ~labels : 'a elt_p1 -> id_label list * id_labelling_list = function
  | Is (_,np) -> labelling_s1 ~as_p1:true grammar ~labels np
  | Pred (_,arg,pred,cp) ->
     let v = var_of_pred pred in
     let w, synt = word_syntagm_of_pred grammar pred in
     let ls_cp =
       match arg, synt with
       | S, `Noun
       | O, `InvNoun -> List.map (fun (_,l) -> (v, `Gen (l,w))) labels @ [(v, `Word w)]
       | _ -> [] in
     let ls_cp, lab = labelling_sn grammar ~labels:ls_cp cp in
     let ls =
       match arg, synt with
       | S, `InvNoun
       | O, `Noun -> List.map (fun (_,l) -> (v, `Of (w,l))) ls_cp @ [(v, `Word w)]
       | _ -> [] in
     ls, lab
  | Type (_,c) ->
    let v, w = var_of_uri c, word_of_class c in
    [(v, `Word w)], []
  | Rel (_, p, ori, np) ->
    let v = var_of_uri p in
    let w, synt = word_syntagm_of_property grammar p in
    let ls_np =
      match synt, ori with
	| `Noun, Fwd
	| `InvNoun, Bwd -> List.map (fun (_,l) -> (v, `Gen (l,w))) labels @ [(v, `Word w)]
	| _ -> [] in
    let ls_np, lab = labelling_s1 ~as_p1:false grammar ~labels:ls_np np in
    let ls =
      match synt, ori with
	| `Noun, Bwd
	| `InvNoun, Fwd -> List.map (fun (_,l) -> (v, `Of (w,l))) ls_np @ [(v, `Word w)]
	| _ -> [] in
    ls, lab
  | Hier (_, id, pred, args, argo, np) ->
     (* TODO: how to use pred, args, argo ? *)
     let ls_np, lab_np = labelling_s1 ~as_p1:false grammar ~labels:[] np in
     let labels_id =
       List.map (fun (v,l) -> "hier_"^v, `Hierarchy l) labels in
     ls_np, (id, `Labels labels_id) :: lab_np
  | Sim (_,np,pred,args,argo,rank) -> (* similar to 'np or a pred' *)
     let _ls_np, lab_np = labelling_s1 ~as_p1:false grammar ~labels np in
     let v = var_of_pred pred in
     let w, synt = word_syntagm_of_pred grammar pred in
     [(v, `Word w)], lab_np (* TODO: improve *)
  | LatLong (_,_ll,id1,id2) ->
    let ls_lat = List.map (fun (v,l) -> (v ^ "_lat", `Gen (l, `Op  grammar#latitude))) labels in
    let ls_long = List.map (fun (v,l) -> (v ^ "_long", `Gen (l, `Op grammar#longitude))) labels in 
    [], [(id1, `Labels ls_lat); (id2, `Labels ls_long)]
  | Triple (_,arg,np1,np2) ->
    let v, w = "relation", `Relation in
    let ls_np1 =
      match arg with
	| S -> List.map (fun (_,l) -> (v, `Gen (l,w))) labels @ [(v, `Word w)]
	| _ -> [] in
    let ls_np2 =
      match arg with
	| O -> List.map (fun (_,l) -> (v, `Gen (l,w))) labels @ [(v, `Word w)]
	| _ -> [] in
    let ls_np1, lab1 = labelling_s1 ~as_p1:false grammar ~labels:ls_np1 np1 in
    let ls_np2, lab2 = labelling_s1 ~as_p1:false grammar ~labels:ls_np2 np2 in
    let ls =
      match arg with
	| P -> List.map (fun (_,l) -> (v, `Of (w,l))) ls_np1 @ [(v, `Word w)]
	| _ -> [] in
    ls, lab1 @ lab2
  | Search _ -> [], []
  | Filter _ -> [], []
  | And (_,lr) ->
    let lss, labs = List.split (List.map (labelling_p1 grammar ~labels) lr) in
    List.concat lss, List.concat labs
  | Or (_,lr) ->
    let _lss, labs = List.split (List.map (labelling_p1 grammar ~labels) lr) in
    [], List.concat labs
  | Maybe (_,elt) ->
    let ls, lab = labelling_p1 grammar ~labels elt in
    ls, lab
  | Not (_,elt) ->
    let _ls, lab = labelling_p1 grammar ~labels elt in
    [], lab
  | In (_,npg,elt) ->
    let _, lab1 = labelling_s1 ~as_p1:false grammar ~labels:[] npg in
    let ls, lab2 = labelling_p1 grammar ~labels elt in
    ls, lab1 @ lab2
  | InWhichThereIs (_,np) ->
    let _, lab = labelling_s1 ~as_p1:false grammar ~labels:[] np in
    [], lab
  | IsThere _ -> [], []
and labelling_p1_opt grammar ~labels : 'a elt_p1 option -> id_label list * id_labelling_list = function
  | None -> [], []
  | Some rel -> labelling_p1 grammar ~labels rel
and labelling_sn grammar ~labels : 'a elt_sn -> id_label list * id_labelling_list = function
  | CNil _ -> [], []
  | CCons (_,arg,np,cp) ->
     let ls_np =
       match arg with
       | S | O -> labels
       | P ->
	  let v, w = "relation", `Relation in
	  [(v, `Word w)]
       | Q q ->
	  let v = var_of_uri q in
	  let w, synt = word_syntagm_of_arg_uri grammar q in
	  [(v, `Word w)] in
     let ls_np, lab_np = labelling_s1 ~as_p1:false grammar ~labels:ls_np np in
     let ls_cp, lab_cp = labelling_sn grammar ~labels cp in
     let ls =
       match arg with
       | S | O -> ls_np @ ls_cp
       | _ -> ls_cp in
     ls, lab_np @ lab_cp
  | CAnd (_, lr) ->
    let lss, labs = List.split (List.map (labelling_sn grammar ~labels) lr) in
    List.concat lss, List.concat labs
  | COr (_, lr) ->
    let _lss, labs = List.split (List.map (labelling_sn grammar ~labels) lr) in
    [], List.concat labs
  | CMaybe (_, elt) ->
    let ls, lab = labelling_sn grammar ~labels elt in
    ls, lab
  | CNot (_, elt) ->
    let _ls, lab = labelling_sn grammar ~labels elt in
    [], lab
and labelling_s1 ~as_p1 grammar ~labels : 'a elt_s1 -> id_label list * id_labelling_list = function
  | Det (_, An (id, modif, head), rel_opt) ->
    let ls_head = match head with Thing -> [] | Class c -> [(var_of_uri c, `Word (word_of_class c))] in
    let labels2 = labels @ ls_head in
    let ls_rel, lab_rel = labelling_p1_opt grammar ~labels:labels2 rel_opt in
    ls_head @ ls_rel, if as_p1 then lab_rel else (id, `Labels (labels2 @ ls_rel)) :: lab_rel
  | Det (_, _, rel_opt) ->
    let ls_rel, lab_rel = labelling_p1_opt grammar ~labels rel_opt in
    ls_rel, lab_rel
  | AnAggreg (_, id, modif, g, rel_opt, np) ->
    let ls_np, lab_np = labelling_s1 ~as_p1:false grammar ~labels np in
    let id =
      match id_of_s1 np with
      | Some id -> id
      | None -> assert false in
    let ls_g = labelling_aggreg_op grammar g id in
    ls_np, (id, `Labels ls_g) :: lab_np
  | NAnd (_, lr) ->
    let lss, labs = List.split (List.map (labelling_s1 ~as_p1 grammar ~labels) lr) in
    List.concat lss, List.concat labs
  | NOr (_, lr) ->
    let _lss, labs = List.split (List.map (labelling_s1 ~as_p1 grammar ~labels) lr) in
    [], List.concat labs
  | NMaybe (_, elt) ->
    let ls, lab = labelling_s1 ~as_p1 grammar ~labels elt in
    ls, lab
  | NNot (_, elt) ->
    let _ls, lab = labelling_s1 ~as_p1 grammar ~labels elt in
    [], lab
and labelling_aggreg grammar ~labelling : 'a elt_aggreg -> id_labelling_list = function
  | ForEachResult _ -> labelling
  | ForEach (_, id, modif, rel_opt, id2) ->
    let ls = get_id_labelling id2 labelling in
    let ls_rel, lab_rel = labelling_p1_opt grammar ~labels:ls rel_opt in
    labelling @ (id, `Alias id2) :: lab_rel
  | ForTerm (_, t, id2) -> labelling
  | TheAggreg (_, id, modif, g, rel_opt, id2) ->
    let ls_g = labelling_aggreg_op grammar g id2 in
    let ls_rel, lab_rel = labelling_p1_opt grammar ~labels:ls_g rel_opt in
    labelling @ (id, `Labels ls_g) :: lab_rel
and labelling_aggreg_op grammar g id =
  let v_g = var_of_aggreg g in
  let l_g =
    let qu, noun, adj_opt, noun_word, adj_word_opt = aggreg_syntax grammar g in
    match adj_word_opt with
    | Some adj_word -> `AggregAdjective (adj_word, `Ref id)
    | None -> `AggregNoun (noun_word, `Ref id) in
  [(v_g, l_g)]
and labelling_s grammar ?(labelling = []) : 'a elt_s -> id_labelling_list = function
  | Return (_, np) ->
    let _ls, lab = labelling_s1 ~as_p1:false grammar ~labels:[] np in
    labelling @ lab
  | SAggreg (_,aggregs) ->
    let lab1 = labelling in
    let lab2 = List.fold_left (fun labelling aggreg -> labelling_aggreg grammar ~labelling aggreg) lab1 aggregs in
    lab2
  | SExpr (_,name,id,modif,expr,rel_opt) ->
    let ls_rel, lab_rel = labelling_p1_opt grammar ~labels:[] rel_opt in
    let expr_label = if name="" then `Expr expr else `Word (`Func name) in
    labelling @ (id, `Labels [("expr", expr_label)]) :: lab_rel
  | SFilter (_,id,expr) ->
    labelling @ (id, `Labels [("expr", `Expr expr)]) :: []
  | Seq (_, lr) ->
    List.fold_left
      (fun labelling s -> labelling_s grammar ~labelling s)
      labelling lr

let rec size_ng_label ~(size_id_label : Lisql.id -> int) : ng_label -> int = function
  | `Word w -> 1
  | `Expr _ -> 1
  | `Ref id -> size_id_label id
  | `Gen (l,w) -> size_ng_label ~size_id_label l + 1
  | `Of (w,l) -> 1 + size_ng_label ~size_id_label l
  | `AggregNoun (w,l) -> size_ng_label ~size_id_label l
  | `AggregAdjective (w,l) -> size_ng_label ~size_id_label l
  (* not favoring 'the average' w.r.t. 'the average <prop>' *)
  | `Hierarchy l -> 1 + size_ng_label ~size_id_label l
  | `Nth (k,l) -> 1 + size_ng_label ~size_id_label l


    
class ['a ] counter =
object
  val mutable key_cpt = []
  method rank (key : 'a) : int =
    try
      let cpt = List.assoc key key_cpt in
      key_cpt <- (key,cpt+1)::List.remove_assoc key key_cpt;
      cpt+1
    with Not_found ->
      key_cpt <- (key,1)::key_cpt;
      1
  method count (key : 'a) : int =
    try List.assoc key key_cpt
    with Not_found -> 0
end

class id_labelling (lab : id_labelling_list) =
object (self)
  val label_counter : ng_label counter = new counter
  val mutable id_list : (id * ((Rdf.var * Lisql.id) * ng_label)) list = []
  initializer
    (* normalizing label lists, and attributing ranks with [label_counter] *)
  let lab_rank =
    List.map
      (function
      | (id, `Alias id2) -> (id, `Alias id2)
      | (id, `Labels ls) ->
	let ls = Common.list_to_set ls in (* removing duplicates *)
	let ls = if ls = [] then [("thing", `Word `Thing)] else ls in (* default label *)
	let ls_rank =
	  List.map
	    (fun (var_prefix, ng) ->
	      let k = label_counter#rank ng in
	      var_prefix, (ng, k))
	    ls in
	(id, `Labels ls_rank))
      lab in
  lab_rank |> List.iter
    (function
    | (id, `Alias id2) ->
      let id2_data =
	try List.assoc id2 id_list
	with Not_found -> (("",id2), `Word `Undefined) in (* should not happen *)
      id_list <- (id, id2_data)::id_list
    | (id, `Labels ls_rank) ->
      let _, _, best_label =
	List.fold_left
	  (fun (best_count,best_size,best_label) (_,(ng,_) as label) ->
	    let count = label_counter#count ng in
	    let size =
	      let rec size_id_label id =
		let ng_id =
		  try snd (List.assoc id id_list)
		  with Not_found -> `Word `Undefined (* should not happen *) in
		size_ng_label ~size_id_label ng_id
	      in
	      size_ng_label ~size_id_label ng in
	    if count < best_count then (count,size,label)
	    else if count = best_count && size < best_size then (count,size,label)
	    else (best_count,best_size,best_label))
	  (max_int, max_int, (try List.hd ls_rank with _ -> assert false))
	  ls_rank in
      let best_prefix, (best_ng, best_k) = best_label in
      let best_ng =
	let n = label_counter#count best_ng in
	if n = 1
	then best_ng
	else `Nth (best_k, best_ng) in
      id_list <- (id, ((best_prefix,id), best_ng))::id_list)

  method get_id_label (id : id) : ng_label =
    try snd (List.assoc id id_list)
    with Not_found -> `Word `Undefined (* should not happen *)

  method get_id_var (id : id) : string =
    let prefix, id =
      try fst (List.assoc id id_list)
      with Not_found -> "thing", id in
    prefix ^ "_" ^ string_of_int id
    
  method get_var_id (v : string) : id =
    match Regexp.search (Regexp.regexp "[0-9]+$") v 0 with
      | Some (i,res) -> (try int_of_string (Regexp.matched_string res) with _ -> assert false)
      | None -> assert false
end

let id_labelling_of_s_annot grammar s_annot : id_labelling =
  let lab = labelling_s grammar s_annot in
  new id_labelling lab


      
(* verbalization of focus *)

let rec head_of_modif grammar annot_opt nn rel (modif : modif_s2) : np =
  let qu, adj =
    match modif with
      | Select, order -> qu_adj_of_order grammar `A order
      | Unselect, order ->
	`Any
	  ( match annot_opt with
	  | None -> false
	  | Some annot -> annot#is_at_focus),
	snd (qu_adj_of_order grammar `A order) in
  let nl = `Qu (qu, adj, `That (nn, rel)) in
  match annot_opt with
  | None -> nl
  | Some annot -> `Focus (annot,nl)
and qu_adj_of_modif grammar annot_opt qu modif : qu * adj =
  match modif with
    | Select, order -> qu_adj_of_order grammar qu order
    | Unselect, order -> `Any (match annot_opt with None -> false | Some annot -> annot#is_at_focus), snd (qu_adj_of_order grammar `A order)
and qu_adj_of_order grammar qu : order -> qu * adj = function
  | Unordered -> qu, `Nil
  | Highest _ -> `The, `Order (`Op grammar#order_highest)
  | Lowest _ -> `The, `Order (`Op grammar#order_lowest)

let ng_of_id ~id_labelling id : ng =
  `LabelThat (id_labelling#get_id_label id, top_rel)

let vp_of_sim grammar annot_opt (np : np) pred args argo rank : vp =
  let w, synt = word_syntagm_of_pred grammar pred in
  let nl_rank =
    `AtNoun (`Op grammar#rank, `PN (`TypedLiteral (string_of_int rank, Rdf.xsd_integer), `Nil)) in
  let nl_sim : vp =
    match synt, args, argo with
    | `Noun, S, O
    | `InvNoun, O, S ->
       `IsNP (`Qu (`A, `Nil, `OfThat (w, np, if rank=0 then `Nil else `PP [nl_rank])), [])
    | `InvNoun, S, O
    | `Noun, O, S ->
       `HasProp (w, np, if rank=0 then [] else [nl_rank])
    (*       `IsNP (X (`Qu (`A, `Nil, X (`That (`Thing, X (`That (X (`Subject (np, X (`IsNP (X (`Qu (`A, `Nil, X (`OfThat (w, X `Void, X `Nil)))), if rank=0 then [] else [nl_rank])))))))))), []) *)
    | `TransVerb, S, O ->
       `IsNP (`Qu (`A, `Nil, `That (`Thing, `That (`Subject (np, `VT (w, `Void, if rank=0 then [] else [nl_rank]))))), [])
    | `TransVerb, O, S ->
       `VT (w, np, if rank=0 then [] else [nl_rank])
    | `TransAdj, S, O ->
       `IsNP (`Qu (`A, `Nil, `That (`Thing, `That (`Subject (np, `IsAdjCP (w, if rank=0 then `Nil else `Cons (nl_rank, `Nil)))))), [])
    | `TransAdj, O, S ->
       `IsAdjCP (w, `Cons (`Bare np, if rank=0 then `Nil else `Cons (nl_rank, `Nil)))
    | _ -> failwith "Lisql2nl.np_of_sim: Invalid args/argo" in
  match annot_opt with
  | None -> nl_sim
  | Some annot -> `Focus (annot, nl_sim)
    
let np_of_aggreg grammar annot_opt qu (modif : modif_s2) (g : aggreg) (rel : rel) (ng : ng) =
  let qu, adj = qu_adj_of_modif grammar annot_opt qu modif in
  let qu_aggreg, noun, adj_opt, noun_word, adj_word_opt = aggreg_syntax grammar g in
  let ng_aggreg =
    match adj_word_opt with
    | Some adj_word -> `AdjThat (adj_word, rel)
    | None -> `NounThatOf (noun_word, rel) in
  let qu = if qu = `The then (qu_aggreg :> qu) else qu in (* the sample of --> a sample of *)
  let susp = match annot_opt with None -> false | Some annot -> annot#is_susp_focus in
  let nl = `Qu (qu, adj, `Aggreg (susp, ng_aggreg, ng)) in
  match annot_opt with
  | None -> nl
  | Some annot -> `Focus (annot,nl)
		    
(*    
let syntax_of_func grammar (func : func)
    : [ `Infix of string | `Noun of string | `Const of string ] =
  let s = string_of_func grammar func in
  match func with
  | `Add | `Sub | `Mul | `Div -> `Infix s
  | `Strlen -> `Noun s
  | `NOW -> `Const s
  | _ -> failwith "TODO"
*)
    
let np_of_apply grammar annot_opt adj func (np_args : np list) (rel : rel) : np =
  let nl = `Expr (adj, grammar#func_syntax func, np_args, rel) in
  match annot_opt with
  | None -> nl
  | Some annot -> `Focus (annot, nl)

		       
let rec vp_of_elt_p1 grammar ~id_labelling : annot elt_p1 -> vp = function
  | IsThere annot -> `Focus (annot, `Ellipsis)
  | Is (annot,np) -> `Focus (annot, `IsNP (np_of_elt_s1 grammar ~id_labelling np, []))
  | Pred (annot,arg,pred,cp) -> `Focus (annot, nl_vp_of_arg_pred grammar ~id_labelling arg pred cp)
  | Type (annot,c) -> `Focus (annot, `IsNP (`Qu (`A, `Nil, `That (word_of_class c, top_rel)), []))
  | Rel (annot,p,Fwd,np) ->
    let word, synt = word_syntagm_of_property grammar p in
    let np = np_of_elt_s1 grammar ~id_labelling np in
    ( match synt with
    | `Noun -> `Focus (annot, `HasProp (word, np, []))
    | `InvNoun -> `Focus (annot, `IsNP (`Qu (`The, `Nil, `OfThat (word, np, top_rel)), []))
    | `TransVerb -> `Focus (annot, `VT (word, np, []))
    | `TransAdj -> `Focus (annot, `IsPP (`Prep (word, np))) )
  | Rel (annot,p,Bwd,np) ->
    let word, synt = word_syntagm_of_property grammar p in
    let np = np_of_elt_s1 grammar ~id_labelling np in
    ( match synt with
    | `Noun -> `Focus (annot, `IsNP (`Qu (`The, `Nil, `OfThat (word, np, top_rel)), []))
    | `InvNoun -> `Focus (annot, `HasProp (word, np, []))
    | `TransVerb -> `Focus (annot, `Subject (np, `VT (word, `Void, [])))
    | `TransAdj -> `Focus (annot, `Subject (np, `IsPP (`Prep (word, `Void)))) )
  | Hier (annot, id, pred, args, argo, np) -> (* TODO: render pred, args, argo *)
     `Focus (annot, `IsPP (`Prep (`Op grammar#in_, np_of_elt_s1 grammar ~id_labelling np)))
  | Sim (annot,np,pred,args,argo,rank) ->
     vp_of_sim grammar (Some annot)
	       (np_of_elt_s1 grammar ~id_labelling np)
	       pred args argo rank
  | LatLong (annot,_ll,_id1,_id2) ->
    `Focus (annot, `Has (`Qu (`A, `Nil, `That (`Op grammar#geolocation, `Nil)), []))
  | Triple (annot,arg,np1,np2) ->
    let np1 = np_of_elt_s1 grammar ~id_labelling np1 in
    let np2 = np_of_elt_s1 grammar ~id_labelling np2 in
    ( match arg with
    | S -> (* has relation npp to npo / has property npp with value npo / has p npo *)
      `Focus (annot, `HasProp (`Relation, np1, [`Prep (`Op grammar#rel_to, np2)]))
    | O -> (* has relation npp from nps / is the value of npp of nps / is the p of nps *)
      `Focus (annot, `HasProp (`Relation, np2, [`Prep (`Op grammar#rel_from, np1)]))
    | P -> (* is a relation from nps to npo / is a property of nps with value npo *)
       `Focus (annot, `IsNP (`Qu (`A, `Nil, `That (`Relation, top_rel)), [`Prep (`Op grammar#rel_from, np1); `Prep (`Op grammar#rel_to, np2)]))
    | _ -> assert false )
  | Search (annot,c) -> vp_of_constr grammar annot c
  | Filter (annot,c,ft) -> vp_of_constr grammar annot c
  | And (annot,lr) -> `Focus (annot, `And (List.map (vp_of_elt_p1 grammar ~id_labelling) lr))
  | Or (annot,lr) -> `Focus (annot, `Or (List.map (vp_of_elt_p1 grammar ~id_labelling) lr))
  | Maybe (annot,x) -> `Focus (annot, `Maybe (vp_of_elt_p1 grammar ~id_labelling x))
  | Not (annot,x) -> `Focus (annot, `Not (vp_of_elt_p1 grammar ~id_labelling x))
  | In (annot,npg,x) -> `Focus (annot, `In (np_of_elt_s1 grammar ~id_labelling npg, vp_of_elt_p1 grammar ~id_labelling x))
  | InWhichThereIs (annot,np) -> `Focus (annot, `IsInWhich (`ThereIs (np_of_elt_s1 grammar ~id_labelling np)))
and vp_of_constr grammar annot = function
  | True -> `Focus (annot, `Ellipsis)
  | MatchesAll [pat]
  | MatchesAny [pat] -> `Focus (annot, `VT (`Op grammar#matches, `PN (`Literal pat, `Nil), []))
  | MatchesAll lpat -> `Focus (annot, `VT (`Op grammar#matches, `QuOneOf (`All, List.map (fun pat -> `Literal pat) lpat), []))
  | MatchesAny lpat -> `Focus (annot, `VT (`Op grammar#matches, `QuOneOf (`One, List.map (fun pat -> `Literal pat) lpat), []))
  | IsExactly pat -> `Focus (annot, `VT (`Op grammar#is_exactly, `PN (`Literal pat, `Nil), []))
  | StartsWith pat -> `Focus (annot, `VT (`Op grammar#starts_with, `PN (`Literal pat, `Nil), []))
  | EndsWith pat -> `Focus (annot, `VT (`Op grammar#ends_with, `PN (`Literal pat, `Nil), []))
  | After pat -> `Focus (annot, `IsPP (`Prep (`Op grammar#after, np_of_literal pat)))
  | Before pat -> `Focus (annot, `IsPP (`Prep (`Op grammar#before, np_of_literal pat)))
  | FromTo (pat1,pat2) -> `Focus (annot, `IsPP (`PrepBin (`Op grammar#interval_from, np_of_literal pat1, `Op grammar#interval_to, np_of_literal pat2)))
  | HigherThan pat -> `Focus (annot, `IsPP (`Prep (`Op grammar#higher_or_equal_to, np_of_literal pat)))
  | LowerThan pat -> `Focus (annot, `IsPP (`Prep (`Op grammar#lower_or_equal_to, np_of_literal pat)))
  | Between (pat1,pat2) -> `Focus (annot, `IsPP (`PrepBin (`Op grammar#interval_between, np_of_literal pat1, `Op grammar#interval_and, np_of_literal pat2)))
  | HasLang pat -> `Focus (annot, `Has (`Qu (`A, `Nil, `That (`Op grammar#language, `Ing (`Op grammar#matching, `PN (`Literal pat, top_rel), []))), []))
  | HasDatatype pat -> `Focus (annot, `Has (`Qu (`A, `Nil, `That (`Op grammar#datatype, `Ing (`Op grammar#matching, `PN (`Literal pat, top_rel), []))), []))
  | ExternalSearch (s,_) -> vp_of_search grammar annot s
and vp_of_search grammar annot = function
  | WikidataSearch kwds
  | TextQuery kwds -> `Focus (annot, `VT (`Op grammar#matches, `PN (`Literal (String.concat " " kwds), `Nil), [])) (* TODO: make search kind explicit *)
and rel_of_elt_p1_opt grammar ~id_labelling = function
  | None -> top_rel
  | Some (InWhichThereIs (annot,np)) -> `Focus (annot, `InWhich (`ThereIs (np_of_elt_s1 grammar ~id_labelling np)))
  | Some rel -> `That (vp_of_elt_p1 grammar ~id_labelling rel)
and np_of_elt_s1 grammar ~id_labelling : annot elt_s1 -> np = function
  | Det (annot, det, rel_opt) ->
    let nl_rel = rel_of_elt_p1_opt grammar ~id_labelling rel_opt in
    det_of_elt_s2 grammar ~id_labelling annot nl_rel det
  | AnAggreg (annot,id,modif,g,rel_opt,np) ->
    np_of_aggreg grammar (Some annot)
      `A modif g
      (rel_of_elt_p1_opt grammar ~id_labelling rel_opt)
      (ng_of_elt_s1 grammar ~id_labelling np)
  | NAnd (annot,lr) -> `Focus (annot, `And (List.map (np_of_elt_s1 grammar ~id_labelling) lr))
  | NOr (annot,lr) -> `Focus (annot, `Or (List.map (np_of_elt_s1 grammar ~id_labelling) lr))
  | NMaybe (annot,x) -> `Focus (annot, `Maybe (np_of_elt_s1 grammar ~id_labelling x))
  | NNot (annot,x) -> `Focus (annot, `Not (np_of_elt_s1 grammar ~id_labelling x))
and ng_of_elt_s1 grammar ~id_labelling : annot elt_s1 -> ng = function
  | Det (annot, An (id,modif,head), rel_opt) ->
     `Focus (annot, `That (word_of_elt_head head, rel_of_elt_p1_opt grammar ~id_labelling rel_opt))
  | AnAggreg (annot,id,modif,g,rel_opt,np) ->
    let rel = rel_of_elt_p1_opt grammar ~id_labelling rel_opt in
    let ng_aggreg =
      let qu, noun, adj_opt, noun_word, adj_word_opt = aggreg_syntax grammar g in
      match adj_word_opt with
      | Some adj_word -> `AdjThat (adj_word, rel)
      | None -> `NounThatOf (noun_word, rel) in
    let ng = ng_of_elt_s1 grammar ~id_labelling np in
    `Focus (annot, `Aggreg (annot#is_susp_focus, ng_aggreg, ng))
  | _ -> assert false
and det_of_elt_s2 grammar ~id_labelling annot rel : elt_s2 -> np = function
  | Term t -> `Focus (annot, `PN (word_of_term t, rel))
  | An (id, modif, head) -> head_of_modif grammar (Some annot) (word_of_elt_head head) rel modif
  | The id -> `Focus (annot, `Qu (`The, `Nil, `LabelThat (id_labelling#get_id_label id, rel)))
(*    `Focus (annot, `Ref (id_labelling#get_id_label id, rel)) *)
and word_of_elt_head = function
  | Thing -> `Thing
  | Class c -> word_of_class c
and np_of_elt_aggreg grammar ~id_labelling : annot elt_aggreg -> np = function
  | ForEachResult annot ->
    `Focus (annot, `Qu (`Each, `Nil, `That (`Op grammar#result, `Nil)))
  | ForEach (annot,id,modif,rel_opt,id2) ->
    let qu, adj = qu_adj_of_modif grammar (Some annot) `Each modif in
    `Focus (annot, `Qu (qu, adj, `LabelThat (id_labelling#get_id_label id2, rel_of_elt_p1_opt grammar ~id_labelling rel_opt)))
  | ForTerm (annot,t,id2) ->
    `Focus (annot, `Label (id_labelling#get_id_label id2, Some (word_of_term t)))
  | TheAggreg (annot,id,modif,g,rel_opt,id2) ->
    np_of_aggreg grammar (Some annot) `The modif g
      (rel_of_elt_p1_opt grammar ~id_labelling rel_opt)
      (ng_of_id ~id_labelling id2)
and np_of_elt_expr grammar ~id_labelling adj rel : annot elt_expr -> np = function
  | Undef annot -> `Focus (annot, `PN (`Undefined, rel))
  | Const (annot,t) -> `Focus (annot, `PN (word_of_term t, rel))
  | Var (annot,id) ->
    if rel = top_rel
    then `Focus (annot, `Label (id_labelling#get_id_label id, None))
    else det_of_elt_s2 grammar ~id_labelling annot rel (The id)
  | Apply (annot,func,args) ->
    np_of_apply grammar (Some annot)
      adj
      func
      (List.map (fun (_,arg_expr) -> np_of_elt_expr grammar ~id_labelling top_adj top_rel arg_expr) args)
      rel
  | Choice (annot,le) ->
    let lnp = List.map (fun expr -> np_of_elt_expr grammar ~id_labelling top_adj top_rel expr) le in
    `Focus (annot, `Choice (adj, lnp, rel))
and s_of_elt_expr grammar ~id_labelling : annot elt_expr -> s = function
  | expr -> `Where (np_of_elt_expr grammar ~id_labelling top_adj top_rel expr)
and s_of_elt_s grammar ~id_labelling : annot elt_s -> s = function
  | Return (annot,np) ->
    `Focus (annot, `Return (np_of_elt_s1 grammar ~id_labelling np))
  | SAggreg (annot,dims_aggregs) ->
    let dims, aggregs = List.partition is_dim dims_aggregs in
    let nl_s_aggregs =
      if aggregs = []
      then `Return (`PN (`Undefined, `Nil))
      else `Return (nl_and (List.map (np_of_elt_aggreg grammar ~id_labelling) aggregs)) in
    if dims = []
    then `Focus (annot, nl_s_aggregs)
    else
      let np_dims = nl_and (List.map (np_of_elt_aggreg grammar ~id_labelling) dims) in
      `Focus (annot, `For (np_dims, nl_s_aggregs))
  | SExpr (annot,name,id,modif,expr,rel_opt) ->
    let _qu, adj = qu_adj_of_modif grammar (Some annot) `The modif in
    let rel = rel_of_elt_p1_opt grammar ~id_labelling rel_opt in
    let np_expr = np_of_elt_expr grammar ~id_labelling adj rel expr in
    let np =
      if name=""
      then np_expr
      else `PN (`Func name, `Ing (`Op "=", np_expr, [])) in
    `Focus (annot, `Return np)
  | SFilter (annot,id,expr) ->
    let s = s_of_elt_expr grammar ~id_labelling expr in
    `Focus (annot, s)
  | Seq (annot,lr) ->
     `Focus (annot, `Seq (List.map (s_of_elt_s grammar ~id_labelling) lr))
and nl_vp_of_arg_pred grammar ~id_labelling arg pred cp =
  let word, synt = word_syntagm_of_pred grammar pred in
  match arg with
  | S -> nl_vp_of_S_pred grammar ~id_labelling ~word ~synt cp
  | P -> raise TODO
  | O -> nl_vp_of_O_pred grammar ~id_labelling ~word ~synt cp
  | Q q -> nl_vp_of_Q_pred grammar ~id_labelling q ~word ~synt cp
and nl_vp_of_S_pred grammar ~id_labelling ~word ~synt cp =
  match synt with
  | `Noun -> `HasPropCP (word, cp_of_elt_sn grammar ~id_labelling cp)
  | `InvNoun -> `IsTheNounCP (word, cp_of_elt_sn grammar ~id_labelling ~inv:true cp)
  | `TransVerb -> `VT_CP (word, cp_of_elt_sn grammar ~id_labelling cp)
  | `TransAdj -> `IsAdjCP (word, cp_of_elt_sn grammar ~id_labelling cp)
and nl_vp_of_O_pred grammar ~id_labelling ~word ~synt cp =
  match synt with
  | `Noun -> `IsTheNounCP (word, cp_of_elt_sn grammar ~id_labelling cp)
  | `InvNoun -> `HasPropCP (word, cp_of_elt_sn grammar ~id_labelling ~inv:true cp)
  | `TransVerb -> nl_is (nl_something (`ThatS (s_of_elt_sn grammar ~id_labelling ~word ~synt cp)))
  | `TransAdj -> nl_is (nl_something (`ThatS (s_of_elt_sn grammar ~id_labelling ~word ~synt cp)))
and nl_vp_of_Q_pred grammar ~id_labelling q ~word ~synt cp =
  let word_q, synt_q = word_syntagm_of_arg_uri grammar q in
  match synt_q with
  | `Noun -> nl_is (nl_something (`AtWhichNoun (word_q, s_of_elt_sn grammar ~id_labelling ~word ~synt cp)))
  | `TransAdj -> nl_is (nl_something (`PrepWhich (word_q, s_of_elt_sn grammar ~id_labelling ~word ~synt cp)))
  (*  | `InvNoun -> `HasProp (word_q, X (`TheFactThat (s_of_elt_sn grammar ~id_labelling ~word ~synt cp)), []) *)
  (*  | `TransVerb -> nl_is (something (X (`ThatS (X (`Truth (X (`TheFactThat (s_of_elt_sn grammar ~id_labelling ~word ~synt cp)), X (`VT_CP (word_q, X `Nil)))))))) *)
and s_of_elt_sn grammar ~id_labelling ~word ~synt : annot elt_sn -> s = function
  | CNil annot -> (* missing subject *)
     `Truth (nl_something `Nil, nl_vp_of_S_pred grammar ~id_labelling ~word ~synt (CNil annot))
  | CCons (annot, arg, np, cp) ->
     if arg = S
     then `Focus (annot, `Truth (np_of_elt_s1 grammar ~id_labelling np, nl_vp_of_S_pred grammar ~id_labelling ~word ~synt cp))
     else `Focus (annot, `PP (pp_of_arg_elt_np grammar ~id_labelling arg np, s_of_elt_sn grammar ~id_labelling ~word ~synt cp))
  | CAnd (annot,lr) -> `Focus (annot, `And (List.map (s_of_elt_sn grammar ~id_labelling ~word ~synt) lr))
  | COr (annot,lr) -> `Focus (annot, `Or (List.map (s_of_elt_sn grammar ~id_labelling ~word ~synt) lr))
  | CMaybe (annot,x) -> `Focus (annot, `Maybe (s_of_elt_sn grammar ~id_labelling ~word ~synt x))
  | CNot (annot,x) -> `Focus (annot, `Not (s_of_elt_sn grammar ~id_labelling ~word ~synt x))
and cp_of_elt_sn grammar ~id_labelling ?(inv = false) : annot elt_sn -> cp = function
  | CNil annot -> `Focus (annot, `Nil)
  | CCons (annot, arg, np, cp) ->
     let arg =
       if inv
       then (match arg with S -> O | O -> S | _ -> arg)
       else arg in
     `Focus (annot, `Cons (pp_of_arg_elt_np grammar ~id_labelling arg np, cp_of_elt_sn grammar ~id_labelling cp))
  | CAnd (annot,lr) -> `Focus (annot, `And (List.map (cp_of_elt_sn grammar ~id_labelling ~inv) lr))
  | COr (annot,lr) -> `Focus (annot, `Or (List.map (cp_of_elt_sn grammar ~id_labelling ~inv) lr))
  | CMaybe (annot,x) -> `Focus (annot, `Maybe (cp_of_elt_sn grammar ~id_labelling ~inv x))
  | CNot (annot,x) -> `Focus (annot, `Not (cp_of_elt_sn grammar ~id_labelling ~inv x))
and pp_of_arg_elt_np grammar ~id_labelling arg np =
  let np = np_of_elt_s1 grammar ~id_labelling np in
  match arg with
  | S -> `Prep (`Op grammar#of_,np)
  | O -> `Bare np
  | P -> `Bare np (* in 'has relation P from S to O' *)
  | Q q ->
     let word_q, synt_q = word_syntagm_of_arg_uri grammar q in
     ( match synt_q with
       | `Noun -> `AtNoun (word_q, np)
       | `TransAdj -> `Prep (word_q, np) )

(* linguistic transformations *)

class transf =
object
  method s : s -> s = fun s -> s
  method np : np -> np = fun np -> np
  method ng : ng -> ng = fun ng -> ng
  method adj : adj -> adj = fun adj -> adj
  method ng_aggreg : ng_aggreg -> ng_aggreg = fun ngg -> ngg
  method rel : rel -> rel = fun rel -> rel
  method vp : vp -> vp = fun vp -> vp
  method cp : cp -> cp = fun cp -> cp
  method pp : pp -> pp = fun pp -> pp
end

(* top-down recursive transformation using [transf] like a visitor *)

let rec map_s (transf : transf) s =
  match transf#s s with
  | `Return np -> `Return (map_np transf np)
  | `ThereIs np -> `ThereIs (map_np transf np)
  | `ThereIs_That (np,s) -> `ThereIs_That (map_np transf np, map_s transf s)
  | `Truth (np,vp) -> `Truth (map_np transf np, map_vp transf vp)
  | `PP (pp,s) -> `PP (map_pp transf pp, map_s transf s)
  | `Where np -> `Where (map_np transf np)
  | `For (np,s) -> `For (map_np transf np, map_s transf s)
  | `Seq lr -> `Seq (List.map (map_s transf) lr)
  | `And lr -> `And (List.map (map_s transf) lr)
  | `Or lr -> `Or (List.map (map_s transf) lr)
  | `Maybe rel -> `Maybe (map_s transf s)
  | `Not rel -> `Not (map_s transf s)
  | `Focus (annot,s) -> `Focus (annot, map_s transf s)
and map_np transf np =
  match transf#np np with
  | `Void -> `Void
  | `PN (w,rel) -> `PN (w, map_rel transf rel)
  | `This -> `This
  | `TheFactThat (s) -> `TheFactThat (map_s transf s)
  | `Label (l,w_opt) -> `Label (l,w_opt)
  | `Qu (qu,adj,ng) -> `Qu (qu, map_adj transf adj, map_ng transf ng)
  | `QuOneOf (qu,lw) -> `QuOneOf (qu,lw)
  | `And (lr) -> `And (List.map (map_np transf) lr)
  | `Or (lr) -> `Or (List.map (map_np transf) lr)
  | `Choice (adj,lr,rel) -> `Choice (map_adj transf adj, List.map (map_np transf) lr, map_rel transf rel)
  | `Maybe (np) -> `Maybe (map_np transf np)
  | `Not (np) -> `Not (map_np transf np)
  | `Expr (adj,syntax,lnp,rel) -> `Expr (map_adj transf adj, syntax, List.map (map_np transf) lnp, map_rel transf rel)
  | `Focus (annot,np) -> `Focus (annot, map_np transf np)
and map_ng transf ng =
  match transf#ng ng with
  | `That (w,rel) -> `That (w, map_rel transf rel)
  | `LabelThat (l,rel) -> `LabelThat (l, map_rel transf rel)
  | `OfThat (w,np,rel) -> `OfThat (w, map_np transf np, map_rel transf rel)
  | `Aggreg (susp,ngg,ng) -> `Aggreg (susp, map_ng_aggreg transf ngg, map_ng transf ng)
  | `Focus (annot,ng) -> `Focus (annot, map_ng transf ng)
and map_adj transf adj =
  match transf#adj adj with
  | `Nil -> `Nil
  | `Order w -> `Order w
  | `Optional (susp,adj) -> `Optional (susp, map_adj transf adj)
  | `Adj (adj,w) -> `Adj (map_adj transf adj, w)
and map_ng_aggreg transf ngg =
  match transf#ng_aggreg ngg with
    | `AdjThat (w,rel) -> `AdjThat (w, map_rel transf rel)
    | `NounThatOf (w,rel) -> `NounThatOf (w, map_rel transf rel)
and map_rel transf rel =
  match transf#rel rel with
  | `Nil -> `Nil
  | `That vp -> `That (map_vp transf vp)
  | `ThatS s -> `ThatS (map_s transf s)
  | `Whose (ng,vp) -> `Whose (map_ng transf ng, map_vp transf vp)
  | `PrepWhich (w,s) -> `PrepWhich (w, map_s transf s)
  | `AtWhichNoun (w,s) -> `AtWhichNoun (w, map_s transf s)
    (*    | `Of np -> `Of (map_np transf np) *)
  | `PP (lpp) -> `PP (List.map (map_pp transf) lpp)
  | `Ing (w,np,lpp) -> `Ing (w, map_np transf np, List.map (map_pp transf) lpp)
  | `InWhich (s) -> `InWhich (map_s transf s)
  | `And lr -> `And (List.map (map_rel transf) lr)
  | `Or lr -> `Or (List.map (map_rel transf) lr)
  | `Maybe rel -> `Maybe (map_rel transf rel)
  | `Not rel -> `Not (map_rel transf rel)
  | `In (npg,rel) -> `In (map_np transf npg, map_rel transf rel)
  | `Ellipsis -> `Ellipsis
  | `Focus (annot,rel) -> `Focus (annot, map_rel transf rel)
and map_vp transf vp =
  match transf#vp vp with
  | `IsNP (np,lpp) -> `IsNP (map_np transf np, List.map (map_pp transf) lpp)
  | `IsPP pp -> `IsPP (map_pp transf pp)
  | `IsTheNounCP (w,cp) -> `IsTheNounCP (w, map_cp transf cp)
  | `IsAdjCP (w,cp) -> `IsAdjCP (w,map_cp transf cp)
  | `IsInWhich s -> `IsInWhich (map_s transf s)
  | `HasProp (w,np,lpp) -> `HasProp (w, map_np transf np, List.map (map_pp transf) lpp)
  | `HasPropCP (w,cp) -> `HasPropCP (w, map_cp transf cp)
  | `Has (np,lpp) -> `Has (map_np transf np, List.map (map_pp transf) lpp)
  | `HasCP cp -> `HasCP (map_cp transf cp)
  | `VT (w,np,lpp) -> `VT (w, map_np transf np, List.map (map_pp transf) lpp)
  | `VT_CP (w,cp) -> `VT_CP (w, map_cp transf cp)
  | `Subject (np,vp) -> `Subject (map_np transf np, map_vp transf vp)
  | `And lr -> `And (List.map (map_vp transf) lr)
  | `Or lr -> `Or (List.map (map_vp transf) lr)
  | `Maybe vp -> `Maybe (map_vp transf vp)
  | `Not vp -> `Not (map_vp transf vp)
  | `EpsilonHead vp -> `EpsilonHead (map_vp transf vp)
  | `In (npg,vp) -> `In (map_np transf npg, map_vp transf vp)
  | `Ellipsis -> `Ellipsis
  | `Focus (annot,vp) -> `Focus (annot, map_vp transf vp)
and map_cp transf cp =
  match transf#cp cp with
  | `Nil -> `Nil
  | `Cons (pp,cp) -> `Cons (map_pp transf pp, map_cp transf cp)
  | `And lr -> `And (List.map (map_cp transf) lr)
  | `Or lr -> `Or (List.map (map_cp transf) lr)
  | `Maybe cp -> `Maybe (map_cp transf cp)
  | `Not cp -> `Not (map_cp transf cp)
  | `Focus (annot,cp) -> `Focus (annot, map_cp transf cp)
and map_pp transf pp =
  match transf#pp pp with
    | `Bare np -> `Bare (map_np transf np)  
    | `Prep (w,np) -> `Prep (w, map_np transf np)
    | `AtNoun (w,np) -> `AtNoun (w, map_np transf np)
    | `At np -> `At (map_np transf np)
    | `PrepBin (w1,np1,w2,np2) -> `PrepBin (w1, map_np transf np1, w2, map_np transf np2)


let main_transf =
object (self)
  inherit transf
  method s nl =
    match nl with
    | `Focus (annot,s) -> `Focus (annot, self#s s)
    | `Return (`Focus (a2, `PN (w, `Nil)))
      -> `ThereIs (`Focus (a2, `PN (w, `Nil)))
    | `Return (`Focus (a2, `PN (w, `That vp)))
      -> `Truth (`Focus (a2, `PN (w, top_rel)), vp)
    | `Return (`Focus (a2, `Qu (`A, adj, (`That ((`Thing | `Class _), _) as ng))))
      -> `Return (`Focus (a2, `Qu (`Every, adj, ng)))
    | nl -> nl
  method np = function
  | `Focus (a1, `Qu (_, adj, `That (`Thing, `That (`Focus (a2, `IsNP (`Qu (qu, `Nil, ng), []))))))
    -> `Focus (a1, `Qu (qu, adj, `Focus (a2, ng)))
  | `Qu (`A, `Nil, `That (`Thing, `That (`IsNP (np, [])))) ->
     np
  | `Focus (a1, `Qu (qu, adj, `Focus (a2, `Aggreg (susp, ngg, `Focus (a3, `That (`Thing, `That (`IsNP (`Qu ((`A | `The), `Nil, ng), []))))))))
    -> `Focus (a1, `Qu (qu, adj, `Focus (a2, `Aggreg (susp, ngg, `Focus (a3, ng)))))
  | `Focus (a1, `QuOneOf (_, [w]))
    -> `Focus (a1, `PN (w, top_rel))
  | `Focus (a1, `Maybe (`Focus (a2, `Qu (qu, adj, ng))))
    -> `Focus (a1, `Qu (qu, `Optional (a1#is_susp_focus, adj), `Focus (a2, ng))) (* TODO: adj out of foc1? *)
  | `Focus (a1, `Not (`Focus (a2, `Qu (`A, adj, ng))))
    -> `Focus (a1, `Qu (`No (a1#is_susp_focus), adj, `Focus (a2, ng))) (* TODO: adj out of foc1 *)
  | nl -> nl
  method rel = function
  | `That (`Focus (a1, vp)) -> self#rel (`Focus (a1, `That vp))
  | `Focus (a1, `That `Ellipsis) -> `Focus (a1, `Ellipsis)
  | `Focus (a1, `That (`And lr)) -> `Focus (a1, `And (List.map (fun vp -> `That vp) lr))
  | `Focus (a1, `That (`Or lr)) -> `Focus (a1, `Or (List.map (fun vp -> `That vp) lr))
(*    | `That (`Maybe (susp,vp)) -> `Maybe (susp, `That vp) *)
(*    | `That (`Not (susp,vp)) -> `Not (susp, `That vp) *)
  | `Focus (a1, `That (`HasProp (p,np,lpp))) ->
    ( match np with
    | `Focus (a2, `Qu (`A, `Nil, `That (`Thing, `That vp)))
      -> `Focus (a1, `Whose (`That (p, `PP lpp), `Focus (a2, `EpsilonHead vp)))
    | `Focus (a2, `Qu (qu, adj, `That (`Thing, rel)))
      -> `Focus (a1, `That (`HasProp (p,np,lpp))) (* simplification at VP level *)
    | `Focus (a2, `Qu (qu, adj, `Aggreg (susp, ngg, `Focus (a3, `That (`Thing, rel2)))))
      -> `Focus (a1, `That (`HasProp (p,np,lpp))) (* idem *)
    | _ -> `Focus (a1, `Whose (`That (p, `PP lpp), `IsNP (np,[]))) )
  | `Focus (a1, `That (`IsNP (`Qu (`A, `Nil, `That (`Thing, rel)), []))) -> `Focus (a1, rel)
  | `Focus (a1, `That (`IsPP pp)) -> `Focus (a1, `PP [pp])
  | `Focus (a1, `That (`IsInWhich s)) -> `Focus (a1, `InWhich s)
  | nl -> nl
  method vp nl =
    match nl with
    | `Focus (annot,vp) -> `Focus (annot, self#vp vp)
    | `HasProp (p, `Focus (a2, `Qu (qu, adj, `That (`Thing, rel))), lpp)
      -> `Has (`Focus (a2, `Qu (qu, adj, `That (p, rel))), lpp)
    | `HasProp (p, `Focus (a2, `Qu (qu, adj, `Aggreg (susp, ngg, `Focus (a3, `That (`Thing, rel2))))), lpp)
      -> `Has (`Focus (a2, `Qu (qu, adj, `Aggreg (susp, ngg, `Focus (a3, `That (p, rel2))))), lpp)
    | `HasProp (p, `Focus (a2, `Maybe (`Focus (a3, `Qu (qu, adj, `That (`Thing, rel))))), lpp)
      -> `Has (`Focus (a2, `Qu (qu, `Optional (a3#is_susp_focus, adj), `Focus (a3, `That (p, rel)))), lpp) (* TODO: adj out of a3 *)
    | `HasPropCP (p, `Focus (a2, `Nil))
      -> `Has (`Focus (a2, `Qu (`A, `Nil, `That (p, `Nil))), [])
    | `HasPropCP (p, `Focus (a2, `Cons (`Bare (`Focus (a3, `Qu (qu, adj, `That (`Thing, rel)))), `Focus (a4, cp))))
      -> `HasCP (`Focus (a2, `Cons (`Bare (`Focus (a3, `Qu (qu, adj, `That (p, rel)))), `Focus (a4, cp))))
    (*	 `Has (A (a3, `Qu (qu, adj, X (`That (p, rel)))), []) *)
    | nl -> nl
  method pp = function
    | `AtNoun (prep, `Focus (a2, `Qu (qu, adj, `That (`Thing, rel))))
      -> `At (`Focus (a2, `Qu (qu, adj, `That (prep, rel))))
    | pp -> pp
end

(* tagged serialization - a la XML *)

type xml = node list
and node =
  | Epsilon
  | Kwd of string
  | Word of word
  | Input of input_type
  | Selection of xml (* [xml] represents the selection operator *)
  | Suffix of xml * string (* suffix: eg. !, 's *)
  | Enum of string * xml list (* separator: eg. commas *)
  | Quote of string * xml * string (* quoted xml *)
  | Coord of xml * xml list (* coordination: eg. 'and' *)
  | Focus of bool * focus * xml (* bool for is_current_focus *)
  | Highlight of xml
  | Suspended of xml
  | DeleteIncr

let rec xml_text_content grammar l =
  String.concat " " (List.map (xml_node_text_content grammar) l)
and xml_node_text_content grammar = function
  | Epsilon -> ""
  | Kwd s -> s
  | Word w -> word_text_content grammar w
  | Input typ -> ""
  | Selection xml_selop -> ""
  | Suffix (x,suf) -> xml_text_content grammar x ^ suf
  | Enum (sep, xs) -> String.concat sep (List.map (xml_text_content grammar) xs)
  | Quote (left, x, right) -> left ^ xml_text_content grammar x ^ right
  | Coord (xsep,xs) -> String.concat (" " ^ xml_text_content grammar xsep ^ " ") (List.map (xml_text_content grammar) xs)
  | Focus (curr,foc,x) -> xml_text_content grammar x
  | Highlight x -> xml_text_content grammar x
  | Suspended x -> xml_text_content grammar x
  | DeleteIncr -> ""

(* removing from XML: focus, highlight, quotes if quoted=true *)
let rec xml_label_prune ~quoted l =
  List.concat (List.map (xml_node_label_prune ~quoted) l)
and xml_node_label_prune ~quoted node =
  match node with
  | Epsilon -> []
  | Kwd _
  | Word _
  | Input _
  | Selection _ -> [node]
  | Suffix (x,suf) -> [Suffix (xml_label_prune ~quoted x, suf)]
  | Enum (sep, xs) -> [Enum (sep, List.map (xml_label_prune ~quoted) xs)]
  | Quote (left, x, right) ->
    if quoted
    then xml_label_prune ~quoted x
    else [Quote (left, xml_label_prune ~quoted:true x, right)]
  | Coord (xsep, xs) -> [Coord (xml_label_prune ~quoted xsep, List.map (xml_label_prune ~quoted) xs)]
  | Focus (curr, foc, x) -> xml_label_prune ~quoted x
  | Highlight x -> xml_label_prune ~quoted x
  | Suspended x -> [Suspended (xml_label_prune ~quoted x)]
  | DeleteIncr -> [node]


let xml_a_an grammar xml =
  Kwd (grammar#a_an ~following:(xml_text_content grammar xml)) :: xml
let xml_every grammar xml =
  Kwd grammar#every :: xml
let xml_has_as_a grammar xml =
  Kwd (grammar#has_as_a ~following:(xml_text_content grammar xml)) :: xml

let xml_suspended susp xml =
  if susp
  then [Suspended xml]
  else xml

let xml_seq grammar annot_opt (lr : xml list) =
  let seq_susp : bool list =
    match annot_opt with
    | Some annot ->
      ( match annot#seq_view with
      | Some (_,view) -> List.map (fun sid -> not (sid_in_view sid view)) (Common.from_to 0 (List.length lr - 1))
      | _ -> assert false )
    | None -> List.map (fun _ -> false) lr in
  [ Coord ([Kwd grammar#and_], List.map2 xml_suspended seq_susp lr) ]
let xml_and grammar lr =
  [ Coord ([Kwd grammar#and_], lr) ]
let xml_or grammar annot_opt lr =
  let susp_or = match annot_opt with None -> false | Some annot -> annot#is_susp_focus in
  let coord = [Word (`Op grammar#or_)] in
  [ Coord (xml_suspended susp_or coord, lr) ]
let xml_choice grammar annot_opt xml_adj lr =
  Kwd (grammar#a_an ~following:grammar#choice) :: xml_adj [Word (`Op grammar#choice)] @ Kwd grammar#between :: Enum (", ", lr) :: []
(* xml_adj grammar adj xml *)
(* xml_rel grammar ~id_labelling rel *)
let xml_maybe grammar annot_opt xml =
  let susp = match annot_opt with None -> false | Some annot -> annot#is_susp_focus in
  xml_suspended susp [Word (`Op grammar#optionally)] @ xml
let xml_not grammar annot_opt xml =
  let susp = match annot_opt with None -> false | Some annot -> annot#is_susp_focus in
  xml_suspended susp [Word (`Op grammar#not_)] @ xml
let xml_epsilon_head xml = Epsilon :: xml
let xml_in grammar xml1 xml2 =
  Word (`Op grammar#according_to) :: xml1 @ [Coord ([], [xml2])]
let xml_selection_op grammar (selop : Lisql.selection_op) : xml =
  match selop with
  | AndSel | NAndSel -> [Kwd "..."; Word (`Op grammar#and_); Kwd "..."]
  | OrSel | NOrSel -> [Kwd "..."; Word (`Op grammar#or_); Kwd "..."]
  | AggregSel -> [Kwd "..."]
let xml_ellipsis = [Kwd "..."]

let xml_focus annot xml =
  match annot#focus with
  | None -> xml
  | Some focus ->
     let pos = annot#focus_pos in
     let current_focus, xml =
       match pos with
       | `At -> true, [Highlight xml]
       | `Below -> false, [Highlight xml]
       | `Aside true -> false, [Suspended xml]
       | _ -> false, xml in
     [Focus (current_focus, focus, xml)]

let rec xml_s grammar ~id_labelling ?(annot_opt = None) (s : s) =
  match s with
  | `Return np -> Kwd grammar#give_me :: xml_np grammar ~id_labelling np
  | `ThereIs np -> Kwd grammar#there_is :: xml_np grammar ~id_labelling np
  | `ThereIs_That (np,s) -> Kwd grammar#there_is :: xml_np grammar ~id_labelling np @ Kwd grammar#relative_that_object :: xml_s grammar ~id_labelling s
  | `Truth (np,vp) -> (*Kwd grammar#it_is_true_that ::*) xml_np grammar ~id_labelling np @ xml_vp grammar ~id_labelling vp
  | `PP (pp,s) -> xml_pp grammar ~id_labelling pp @ xml_s grammar ~id_labelling s
  | `Where np -> Kwd grammar#where :: xml_np grammar ~id_labelling np
  | `For (np,s) -> Kwd grammar#for_ :: xml_np grammar ~id_labelling np @ Coord ([], [xml_s grammar ~id_labelling s]) :: []    
      (* [Enum (", ", [Kwd grammar#for_ :: xml_np grammar ~id_labelling np;
	 xml_s grammar ~id_labelling s])] *)
  | `Seq lr -> xml_seq grammar annot_opt (List.map (xml_s grammar ~id_labelling) lr)
  | `And lr -> xml_and grammar (List.map (xml_s grammar ~id_labelling) lr)
  | `Or lr -> xml_or grammar annot_opt (List.map (xml_s grammar ~id_labelling) lr)
  | `Maybe s -> xml_maybe grammar annot_opt (xml_s grammar ~id_labelling s)
  | `Not s -> xml_not grammar annot_opt (xml_s grammar ~id_labelling s)
  | `Focus (annot,s) -> xml_focus annot (xml_s grammar ~id_labelling ~annot_opt:(Some annot) s)
and xml_np grammar ~id_labelling ?(annot_opt = None) np =
  match np with
  | `Void -> []
  | `PN (w,rel) -> Word w :: xml_rel grammar ~id_labelling rel
  | `This -> [Kwd grammar#this]
  | `TheFactThat (s) -> Kwd grammar#the_fact_that :: xml_s grammar ~id_labelling s
  | `Label (l,w_opt) -> xml_np_label grammar ~id_labelling l @ (match w_opt with None -> [] | Some w -> [Word w])
  | `Qu (qu,adj,ng) -> xml_qu grammar qu (xml_adj grammar adj (xml_ng grammar ~id_labelling ng))
  | `QuOneOf (qu,lw) -> xml_qu grammar qu (Kwd grammar#quantif_of :: Enum (", ", List.map (fun w -> [Word w]) lw) :: [])
  | `And lr -> xml_and grammar (List.map (xml_np grammar ~id_labelling) lr)
  | `Or lr -> xml_or grammar annot_opt (List.map (xml_np grammar ~id_labelling) lr)
  | `Choice (adj,lr,rel) -> xml_choice grammar annot_opt (xml_adj grammar adj) (List.map (xml_np grammar ~id_labelling) lr) @ xml_rel grammar ~id_labelling rel
  | `Maybe np -> xml_maybe grammar annot_opt (xml_np grammar ~id_labelling np)
  | `Not np -> xml_not grammar annot_opt (xml_np grammar ~id_labelling np)
  | `Expr (adj,syntax,lnp,rel) -> xml_adj grammar adj (xml_expr grammar syntax (List.map (xml_np grammar ~id_labelling) lnp) @ xml_rel grammar ~id_labelling rel)
  | `Focus (annot,np) -> xml_focus annot (xml_np grammar ~id_labelling ~annot_opt:(Some annot) np)
and xml_expr grammar syntax lnp =
  match syntax with
  | `Noun s -> Kwd grammar#the :: Word (`Func s) :: Kwd grammar#of_ :: List.concat lnp
  | `Prefix s -> Word (`Func s) :: List.concat lnp
  | `Infix s -> [Enum (s, lnp)]
  | `Brackets (s1,s2) -> Kwd s1 :: List.concat lnp @ [Kwd s2]
  | `Pattern l ->
    List.concat
      (List.map
	 (function
	 | `Kwd s -> [Kwd s]
	 | `Func s -> [Word (`Func s)]
	 | `Arg i -> (try List.nth lnp (i-1) with _ -> [Word `Undefined]))
	 l)
and xml_ng grammar ~id_labelling rel =
  match rel with
  | `That (w,rel) -> Word w :: xml_rel grammar ~id_labelling rel
  | `LabelThat (l,rel) -> xml_ng_label grammar ~id_labelling l @ xml_rel grammar ~id_labelling rel
  | `OfThat (w,np,rel) -> Word w :: Word (`Op grammar#of_) :: xml_np grammar ~id_labelling np @ xml_rel grammar ~id_labelling rel
  | `Aggreg (susp,ngg,ng) -> xml_ng_aggreg grammar ~id_labelling susp (xml_ng grammar ~id_labelling ng) ngg
  | `Focus (annot,rel) -> xml_focus annot (xml_ng grammar ~id_labelling rel)
and xml_qu grammar qu xml =
  match xml with
    | Word `Thing :: xml_rem ->
      ( match qu with
	| `A -> Kwd grammar#something :: xml_rem
	| `Any susp -> xml_suspended susp [Word (`Op grammar#anything)] @ xml_rem
	| `The -> Kwd grammar#the :: xml
	| `Every -> Kwd grammar#everything :: xml_rem
	| `Each -> Kwd grammar#each :: xml
	| `All -> Kwd grammar#everything :: xml_rem
	| `One -> Kwd grammar#quantif_one :: xml
	| `No susp -> xml_suspended susp [Word (`Op grammar#nothing)] @ xml_rem )
    | _ ->
      ( match qu with
	| `A -> xml_a_an grammar xml
	| `Any susp -> xml_suspended susp [Word (`Op grammar#any)] @ xml
	| `The -> Kwd grammar#the :: xml
	| `Every -> Kwd grammar#every :: xml
	| `Each -> Kwd grammar#each :: xml
	| `All -> Kwd grammar#all :: xml
	| `One -> Kwd grammar#quantif_one :: xml
	| `No susp -> xml_suspended susp [Word (`Op grammar#no)] @ xml )
and xml_adj grammar adj xml_ng =
  let append xml_adj xml_ng =
    if grammar#adjective_before_noun
    then xml_adj @ xml_ng
    else xml_ng @ xml_adj
  in
  match adj with
    | `Nil -> xml_ng
    | `Order w -> append [Word w] xml_ng
    | `Optional (susp,adj) -> append (xml_suspended susp [Word (`Op grammar#optional)]) (xml_adj grammar adj xml_ng)
    | `Adj (adj,w) -> append (xml_adj grammar adj [Word w]) xml_ng
and xml_ng_aggreg grammar ~id_labelling susp xml_ng = function
  | `AdjThat (g,rel) ->
    let xml_g_rel = Word g :: xml_rel grammar ~id_labelling rel in
    if grammar#adjective_before_noun
    then xml_suspended susp xml_g_rel @ xml_ng
    else xml_ng @ xml_suspended susp xml_g_rel
  | `NounThatOf (g,rel) -> xml_suspended susp (Word g :: xml_rel grammar ~id_labelling rel @ [Word (`Op grammar#of_)]) @ xml_ng
and xml_rel grammar ~id_labelling ?(annot_opt = None) = function
  | `Nil -> []
  | `That vp -> Kwd grammar#relative_that :: xml_vp grammar ~id_labelling vp
  | `ThatS s -> Kwd grammar#relative_that_object :: xml_s grammar ~id_labelling s
  | `Whose (ng,vp) -> Kwd grammar#whose :: xml_ng grammar ~id_labelling ng @ xml_vp grammar ~id_labelling vp
  | `PrepWhich (w,s) -> Word w :: Kwd grammar#which :: xml_s grammar ~id_labelling s
  | `AtWhichNoun (w,s) -> Kwd grammar#with_ :: Kwd grammar#which :: Word w :: xml_s grammar ~id_labelling s
      (*      | `Of np -> Kwd grammar#of_ :: xml_np grammar ~id_labelling np *)
  | `PP lpp -> xml_pp_list grammar ~id_labelling lpp
  | `Ing (w,np,lpp) -> Word w :: xml_np grammar ~id_labelling np @ xml_pp_list grammar ~id_labelling lpp
  | `InWhich s -> xml_in_which grammar ~id_labelling s
  | `And lr -> xml_and grammar (List.map (xml_rel grammar ~id_labelling) lr)
  | `Or lr -> xml_or grammar annot_opt (List.map (xml_rel grammar ~id_labelling) lr)
  | `Maybe rel -> xml_maybe grammar annot_opt (xml_rel grammar ~id_labelling rel)
  | `Not rel -> xml_not grammar annot_opt (xml_rel grammar ~id_labelling rel)
  | `In (npg,rel) -> xml_in grammar (xml_np grammar ~id_labelling npg) (xml_rel grammar ~id_labelling rel)
  | `Ellipsis -> xml_ellipsis
  | `Focus (a1, `Maybe (`Focus (a2, `That vp))) -> xml_focus a1 (Kwd grammar#relative_that :: xml_vp_mod grammar ~id_labelling `Maybe a1 a2 vp)
  | `Focus (a1, `Not (`Focus (a2, `That vp))) -> xml_focus a1 (Kwd grammar#relative_that :: xml_vp_mod grammar ~id_labelling `Not a1 a2 vp)
  | `Focus (annot,rel) -> xml_focus annot (xml_rel grammar ~id_labelling ~annot_opt:(Some annot) rel)
and xml_vp grammar ~id_labelling ?(annot_opt = None) = function
  | `IsNP (np,lpp) -> Kwd grammar#is :: xml_np grammar ~id_labelling np @ xml_pp_list grammar ~id_labelling lpp
  | `IsPP pp -> Kwd grammar#is :: xml_pp grammar ~id_labelling pp
  | `IsTheNounCP (w,cp) -> Kwd grammar#is :: Kwd grammar#the :: Word w :: xml_cp grammar ~id_labelling cp
  | `IsAdjCP (w,cp) -> Kwd grammar#is :: Word w :: xml_cp grammar ~id_labelling cp
  | `IsInWhich s -> Kwd grammar#is :: Kwd grammar#something :: xml_in_which grammar ~id_labelling s
  | `HasProp (p,np,lpp) -> xml_has_as_a grammar [Word p] @ xml_np grammar ~id_labelling np @ xml_pp_list grammar ~id_labelling lpp
  | `HasPropCP (w,cp) -> xml_has_as_a grammar [Word w] @ xml_cp grammar ~id_labelling cp
  | `Has (np,lpp) -> Kwd grammar#has :: xml_np grammar ~id_labelling np @ xml_pp_list grammar ~id_labelling lpp
  | `HasCP cp -> Kwd grammar#has :: xml_cp grammar ~id_labelling cp
  | `VT (w,np,lpp) -> Word w :: xml_np grammar ~id_labelling np @ xml_pp_list grammar ~id_labelling lpp
  | `VT_CP (w,cp) -> Word w :: xml_cp grammar ~id_labelling cp
  | `Subject (np,vp) -> xml_np grammar ~id_labelling np @ xml_vp grammar ~id_labelling vp
  | `And lr -> xml_and grammar (List.map (xml_vp grammar ~id_labelling) lr)
  | `Or lr -> xml_or grammar annot_opt (List.map (xml_vp grammar ~id_labelling) lr)
  | `Maybe vp -> xml_maybe grammar annot_opt (xml_vp grammar ~id_labelling vp)
  | `Not vp -> xml_not grammar annot_opt (xml_vp grammar ~id_labelling vp)
  | `EpsilonHead vp -> xml_epsilon_head (xml_vp grammar ~id_labelling vp)
  | `In (npg,vp) -> xml_in grammar (xml_np grammar ~id_labelling npg) (xml_vp grammar ~id_labelling vp)
  | `Ellipsis -> xml_ellipsis
  | `Focus (a1, `Maybe (`Focus (a2, vp))) -> xml_focus a1 (xml_vp_mod grammar ~id_labelling `Maybe a1 a2 vp)
  | `Focus (a1, `Not (`Focus (a2, vp))) -> xml_focus a1 (xml_vp_mod grammar ~id_labelling `Not a1 a2 vp) (* negation inversion *)
  | `Focus (annot,vp) -> xml_focus annot (xml_vp grammar ~id_labelling ~annot_opt:(Some annot) vp)
and xml_in_which grammar ~id_labelling s =
  Word (`Op grammar#according_to) :: Kwd grammar#which :: Coord ([], [xml_s grammar ~id_labelling s]) :: []
and xml_vp_mod grammar ~id_labelling (op_mod : [`Not | `Maybe]) annot_mod annot_vp vp =
  let f_xml_mod = match op_mod with `Maybe -> xml_maybe | `Not -> xml_not in
  let xml_mod = xml_focus (annot_mod#down) (f_xml_mod grammar (Some annot_mod) []) in
  match op_mod, vp with
    | (`Not | `Maybe), `IsNP (np,lpp) -> xml_focus annot_vp (Kwd grammar#is :: xml_mod @ xml_np grammar ~id_labelling np @ xml_pp_list grammar ~id_labelling lpp)
    | (`Not | `Maybe), `IsPP pp -> xml_focus annot_vp (Kwd grammar#is :: xml_mod @ xml_pp grammar ~id_labelling pp)
    | (`Not | `Maybe), `IsInWhich s -> xml_focus annot_vp (Kwd grammar#is :: xml_mod @ Kwd grammar#something :: xml_in_which grammar ~id_labelling s)
    | `Not, `HasProp (p,np,lpp) -> xml_focus annot_vp (xml_has_as_a grammar (xml_mod @ [Word p]) @ xml_np grammar ~id_labelling np @ xml_pp_list grammar ~id_labelling lpp)
    | `Not, `Has (np,lpp) -> xml_focus annot_vp (Kwd grammar#has :: xml_mod @ xml_np grammar ~id_labelling np @ xml_pp_list grammar ~id_labelling lpp)
    | _, vp -> xml_mod @ xml_focus annot_vp (xml_vp grammar ~id_labelling vp)
and xml_cp grammar ~id_labelling ?(annot_opt = None) cp =
  match cp with
  | `Nil -> xml_epsilon_head []
  | `Cons (pp,cp) -> xml_pp grammar ~id_labelling pp @ xml_cp grammar ~id_labelling cp
  | `And lr -> xml_and grammar (List.map (xml_cp grammar ~id_labelling) lr)
  | `Or lr -> xml_or grammar annot_opt (List.map (xml_cp grammar ~id_labelling) lr)
  | `Maybe cp -> xml_maybe grammar annot_opt (xml_cp grammar ~id_labelling cp)
  | `Not cp -> xml_not grammar annot_opt (xml_cp grammar ~id_labelling cp)
  | `Focus (annot,cp) -> xml_focus annot (xml_cp grammar ~id_labelling ~annot_opt:(Some annot) cp)
and xml_pp_list grammar ~id_labelling lpp =
  List.concat (List.map (xml_pp grammar ~id_labelling) lpp)
and xml_pp grammar ~id_labelling = function
  | `Bare np -> xml_epsilon_head (xml_np grammar ~id_labelling np)
  | `Prep (w,np) -> Word w :: xml_np grammar ~id_labelling np
  | `AtNoun (w,np) -> Kwd grammar#with_ :: Word w :: xml_np grammar ~id_labelling np
  | `At np -> Kwd grammar#with_ :: xml_np grammar ~id_labelling np
  | `PrepBin (prep1,np1,prep2,np2) -> Word prep1 :: xml_np grammar ~id_labelling np1 @ Word prep2 :: xml_np grammar ~id_labelling np2
and xml_ng_label ?(isolated = false) grammar ~id_labelling = function
  | `Word w -> [Word w]
  | `Expr expr ->
    let xml = xml_np_label ~isolated grammar ~id_labelling (`Expr expr) in
    if isolated
    then xml
    else Kwd grammar#value_ :: Word (`Op grammar#of_) :: xml
  | `Ref id ->
    xml_ng_label ~isolated grammar ~id_labelling (id_labelling#get_id_label id)
  | `Nth (k, `Expr expr) -> xml_ng_label grammar ~id_labelling (`Expr expr) (* equal exprs are equal! *)
  | `Gen (ng, w) ->
    ( match grammar#genetive_suffix with
      | Some suf -> Suffix (xml_ng_label grammar ~id_labelling ng, suf) :: Word w :: []
      | None -> xml_ng_label grammar ~id_labelling (`Of (w,ng)) )
  | `Of (w,ng) -> Word w :: Word (`Op grammar#of_) :: xml_np_label grammar ~id_labelling ng
  | `AggregNoun (w,ng) -> Word w :: Kwd grammar#of_ :: xml_ng_label grammar ~id_labelling ng
  | `AggregAdjective (w,ng) ->
    if grammar#adjective_before_noun
    then Word w :: xml_ng_label grammar ~id_labelling ng
    else xml_ng_label grammar ~id_labelling ng @ [Word w]
  | `Hierarchy ng -> xml_ng_label grammar ~id_labelling ng @ [Word (`Op grammar#hierarchy)]
  | `Nth (k,ng) -> Word (`Op (grammar#n_th k)) :: xml_ng_label grammar ~id_labelling ng
and xml_np_label ?(isolated = false) grammar ~id_labelling ng =
  match ng with
  | `Expr expr ->
    let np = np_of_elt_expr grammar ~id_labelling top_adj top_rel expr in
    let xml ~quoted = xml_label_prune ~quoted (xml_np grammar ~id_labelling np) in
    if isolated
    then xml ~quoted:false
    else [Quote ("``", xml ~quoted:true, "''")]
  | `Nth (k, `Expr expr) -> xml_np_label grammar ~id_labelling (`Expr expr) (* equal exprs are equal! *)
  | _ -> Word (`Op grammar#the) :: xml_ng_label grammar ~id_labelling ng

let xml_of_elt_s grammar ~id_labelling (s : annot elt_s) : xml =
  let nl_s = s_of_elt_s grammar ~id_labelling s in
  let nl_s = map_s main_transf nl_s in
  xml_s grammar ~id_labelling nl_s

let xml_of_constr grammar ~id_labelling (c : Lisql.constr) : xml =
  let nl = vp_of_constr grammar Lisql_annot.dummy_annot c in
  let nl = map_vp main_transf nl in
  let xml = xml_vp grammar ~id_labelling nl in
  xml_label_prune ~quoted:false xml
	
let xml_ng_id ?isolated grammar ~id_labelling id = xml_ng_label ?isolated grammar ~id_labelling (id_labelling#get_id_label id)
let xml_np_id ?isolated grammar ~id_labelling id = xml_np_label ?isolated grammar ~id_labelling (id_labelling#get_id_label id)

let xml_incr_coordinate grammar focus xml = xml
(*  match focus with
  | AtSn _
  | AtS1 _
  | AtP1 (IsThere _, _) -> xml
  | _ -> Kwd grammar#and_ :: xml *)

let xml_of_incr grammar ~id_labelling (focus : focus) (incr : increment) : xml =
  let focus_span = focus_span incr in
  xml_label_prune ~quoted:false
  ( match incr with
  | IncrSelection (selop,_) ->
     [Selection (xml_selection_op grammar selop)]
  | IncrInput (_,typ) ->
    let xml_input = [Input typ] in
    let kwd_type = string_of_input_type grammar typ in
    Word (`Literal grammar#the) :: Word (`Literal kwd_type) :: xml_input
  | IncrTerm t ->
    let xml_t = [Word (word_of_term t)] in
    ( match focus with
      | AtSn (CCons (_,_,Det (_, Term t0, _),_), _) -> xml_t @ [DeleteIncr]
      | AtS1 (Det (_, Term t0, _), _) when t0 = t -> xml_t @ [DeleteIncr]
      | AtSn _ | AtS1 _ | AtExpr _ -> xml_t
      | AtAggreg (aggreg, _) when is_dim aggreg -> xml_t (* for ForTerm dimensions *)
      | AtP1 (Hier _, _) -> xml_t
      | _ -> 
	 xml_incr_coordinate
	   grammar focus
	   (Kwd grammar#relative_that :: Kwd grammar#is :: xml_t) )
  | IncrId (id,_) ->
    let xml = xml_np_id grammar ~id_labelling id in
    ( match focus with
      | AtSn _ | AtS1 _ | AtExpr _ -> xml
      | AtAggreg (aggreg, _) when is_dim aggreg -> xml (* for ForTerm dimensions *)
      | _ ->
	 xml_incr_coordinate
	   grammar focus
	   (Kwd grammar#relative_that :: Kwd grammar#is :: xml) )
  | IncrPred (arg,pred) ->
     let cp =
       match arg, pred with
       | S, Class _ -> CNil dummy_annot
       | S, _ -> CCons (dummy_annot, O, dummy_s1, CNil dummy_annot)
       | _, Class _
       | O, _ -> CCons (dummy_annot, S, dummy_s1, CNil dummy_annot)
       | _ -> CCons (dummy_annot, S, dummy_s1,
		     CCons (dummy_annot, O, dummy_s1,
			    CNil dummy_annot)) in
     let rel = `Focus (dummy_annot, `That (nl_vp_of_arg_pred grammar ~id_labelling arg pred cp)) in
     let rel = map_rel main_transf rel in
     xml_incr_coordinate grammar focus (xml_rel grammar ~id_labelling rel)
  | IncrArg q ->
     let w, synt = word_syntagm_of_arg_uri grammar q in
     ( match synt with
       | `Noun -> Kwd grammar#with_ :: Word w :: xml_ellipsis
       | `TransAdj -> Word w :: xml_ellipsis )
  | IncrType c ->
    let xml_c = [Word (word_of_class c)] in
    ( match focus with
      | AtSn (cp,ctx) ->
	 let xml_delete_opt =
	  match cp with
	  | CCons (_, _, Det (_, An (_, _, Class c0), _), _) when c0 = c -> [DeleteIncr]
	  | _ -> [] in
	 Kwd grammar#is :: xml_a_an grammar xml_c @ xml_delete_opt
      | AtS1 (Det (_, An (_, _, head), _), ctx) ->
	 let xml_delete_opt =
	   if head = Class c
	   then [DeleteIncr]
	   else [] in
	 let xml_qu =
	   match ctx with
	   | ReturnX _ when head = Thing || head = Class c -> xml_every
	   | _ -> xml_a_an in
	 let xml = xml_qu grammar xml_c @ xml_delete_opt in
	 if head = Thing || head = Class c
	 then xml
	 else Kwd grammar#relative_that :: Kwd grammar#is :: xml
      | AtS1 (np,ctx) -> xml_a_an grammar xml_c
      | _ ->
	 xml_incr_coordinate
	   grammar focus
	   (Kwd grammar#relative_that :: Kwd grammar#is :: xml_a_an grammar xml_c) )
  | IncrRel (p,Lisql.Fwd) ->
     xml_incr_coordinate
       grammar focus
       (Kwd grammar#relative_that ::
	  let word, synt = word_syntagm_of_property grammar p in
	  (match synt with
	   | `Noun -> Kwd grammar#has :: xml_a_an grammar [Word word]
	   | `InvNoun -> Kwd grammar#is :: Kwd grammar#the :: Word word :: Word (`Op grammar#of_) :: xml_ellipsis
	   | `TransVerb -> Word word :: xml_ellipsis
	   | `TransAdj -> Kwd grammar#is :: Word word :: xml_ellipsis))
  | IncrRel (p,Lisql.Bwd) ->
     xml_incr_coordinate grammar focus
      (Kwd grammar#relative_that ::
       let word, synt = word_syntagm_of_property grammar p in
       (match synt with
	 | `Noun -> Kwd grammar#is :: Kwd grammar#the :: Word word :: Word (`Op grammar#of_) :: xml_ellipsis
	 | `InvNoun -> Kwd grammar#has :: xml_a_an grammar [Word word]
	 | `TransVerb -> xml_ellipsis @ Word word :: []
	 | `TransAdj -> xml_ellipsis @ Kwd grammar#is :: Word word :: []))
  | IncrLatLong _ll ->
     xml_incr_coordinate grammar focus
      (Kwd grammar#relative_that :: Kwd grammar#has :: xml_a_an grammar [Word (`Op grammar#geolocation)])
  | IncrTriple (S | O as arg) ->
    xml_incr_coordinate grammar focus
      (Kwd grammar#relative_that :: Kwd grammar#has :: xml_a_an grammar [Word `Relation] @ (if arg = S then Kwd grammar#rel_to :: xml_ellipsis else Kwd grammar#rel_from :: xml_ellipsis))
  | IncrTriple P ->
    xml_incr_coordinate grammar focus
      (Kwd grammar#relative_that :: Kwd grammar#is :: xml_a_an grammar [Word `Relation] @ Kwd grammar#rel_from :: xml_ellipsis @ Kwd grammar#rel_to :: xml_ellipsis)
  | IncrTriple (Q _) -> assert false
  | IncrTriplify -> Kwd grammar#has :: xml_a_an grammar [Word `Relation] @ Kwd (grammar#rel_from ^ "/" ^ grammar#rel_to) :: []
  | IncrHierarchy trans_rel ->
     let xml = [Word (`Op grammar#in_); Word focus_span] in
     if trans_rel
     then Word (`Prop ("", "...")) :: xml
     else xml
  | IncrSim (pred,args,argo) ->
     let vp = vp_of_sim grammar None (focus_span_np incr) pred args argo 1 in
     let np = `Qu (`A, `Nil, `That (`Thing, `That vp)) in
     let np = main_transf#np np in
     xml_np grammar ~id_labelling np
  | IncrSimRankIncr -> Kwd grammar#with_ :: Word (`Op grammar#rank) :: Word (`Op "+ 1") :: []
  | IncrSimRankDecr -> Kwd grammar#with_ :: Word (`Op grammar#rank) :: Word (`Op "- 1") :: []
  | IncrAnything -> [Word (`Op grammar#anything)]
  | IncrThatIs -> Word focus_span :: xml_incr_coordinate grammar focus (Kwd grammar#relative_that :: Kwd grammar#is :: xml_ellipsis)
  | IncrSomethingThatIs -> Kwd grammar#something :: Kwd grammar#relative_that :: Kwd grammar#is :: Word focus_span :: []
  | IncrAnd -> Word focus_span :: Kwd grammar#and_ :: xml_ellipsis
  | IncrDuplicate -> Word focus_span :: Kwd grammar#and_ :: Word focus_span :: []
  | IncrOr -> Word focus_span :: Word (`Op grammar#or_) :: xml_ellipsis
  | IncrChoice -> [Kwd (grammar#a_an ~following:grammar#choice); Word (`Op grammar#choice); Kwd grammar#between; Word focus_span; Kwd ", "; Word `Undefined]
  | IncrMaybe -> xml_maybe grammar None [Word focus_span]
  | IncrNot -> xml_not grammar None [Word focus_span]
  | IncrIn -> [Suffix (Word (`Op grammar#according_to) :: xml_ellipsis, ","); Word focus_span]
  | IncrInWhichThereIs -> Word (`Op grammar#according_to) :: Kwd grammar#which :: Kwd grammar#there_is :: xml_ellipsis
  | IncrUnselect -> xml_np grammar ~id_labelling (head_of_modif grammar None focus_name top_rel (Unselect,Unordered))
  | IncrOrder order -> xml_np grammar ~id_labelling (head_of_modif grammar None focus_name top_rel (Select,order))
  | IncrForeach -> Kwd grammar#for_ :: Kwd grammar#each :: Word focus_name :: Kwd grammar#give_me :: xml_ellipsis
  | IncrAggreg g -> Kwd grammar#give_me :: xml_np grammar ~id_labelling (np_of_aggreg grammar None `The Lisql.factory#top_modif g top_rel focus_name_ng)
  | IncrForeachResult ->
     let xml_delete_opt =
       let has_foreach_result =
	 match focus with
	 | AtS (SAggreg (_, aggregs), _) -> List.exists is_ForEachResult aggregs
	 | AtAggreg (ForEachResult _, _) -> true
	 | AtAggreg (_, SAggregX ((ll,rr), _)) -> List.exists is_ForEachResult ll || List.exists is_ForEachResult rr
	 | _ -> false in
       if has_foreach_result
       then [DeleteIncr]
       else [] in
     Kwd grammar#for_ :: Kwd grammar#each :: Word (`Op grammar#result) :: xml_delete_opt
  | IncrForeachId id -> Kwd grammar#for_ :: Kwd grammar#each :: xml_ng_id grammar ~id_labelling id
  | IncrAggregId (g,id) -> xml_np grammar ~id_labelling (np_of_aggreg grammar None `The Lisql.factory#top_modif g top_rel (ng_of_id ~id_labelling id))
  | IncrFuncArg (is_pred,func,arity,pos,_,_) ->
    xml_np grammar ~id_labelling
      (np_of_apply grammar None
	 top_adj
	 func
	 (List.map
	    (fun i -> if i=pos then focus_span_np incr else undefined_np)
	    (Common.from_to 1 arity))
      	 top_rel)
  | IncrName name -> [Input StringInput; Word (`Op "="); Word focus_span])

		       
(* main verbalization functions *)



