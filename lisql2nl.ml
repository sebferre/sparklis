
open Lisql
open Lisql_annot
open Js
open Jsutils

(* configuration : language *)

let config_lang =
  let key = "lang" in
  let select_selector = "#lang-select" in
  let default = "en" in
object (self)
  inherit Config.input
  val mutable init_v : string = default
  val mutable current_v : string = default

  method value : string = current_v
  method grammar : Grammar.grammar =
    match current_v with
      | "fr" -> Grammar.french
      | _ -> Grammar.english

  method private set_select (v : string) : unit =
    if v <> current_v then begin
      jquery_select select_selector (fun select -> select##value <- string v);
      current_v <- v;
      has_changed <- true
    end

  method get_permalink =
    if current_v <> init_v
    then [(key, current_v)]
    else []
  method set_permalink args =
    try self#set_select (List.assoc key args)
    with _ -> ()

  method init =
    jquery_select select_selector (fun select ->
      init_v <- to_string select##value;
      current_v <- init_v;
      onchange
	(fun select ev ->
	  current_v <- to_string select##value;
	  has_changed <- true)
	select)
  method reset = self#set_select init_v
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
  | `Op of string
  | `DummyFocus ]

let word_text_content grammar = function
  | `Thing -> grammar#thing
  | `Relation -> grammar#relation
  | `Entity (uri,s) -> s
  | `Literal s -> s
  | `TypedLiteral (s, dt) -> if config_show_datatypes#value then s ^ " (" ^ dt ^ ")" else s
  | `Blank id -> id
  | `Class (uri,s) -> s
  | `Prop (uri,s) -> s
  | `Op s -> s
  | `DummyFocus -> ""

(* type np_label =
   [ `The of int option * ng_label ] *)
type ng_label =
  [ `Word of word
  | `Gen of ng_label * word
  | `Of of word * ng_label
  | `AggregNoun of word * ng_label
  | `AggregAdjective of word * ng_label
  | `Nth of int * ng_label ]

type ('a,'b) annotated = X of 'b | A of 'a * 'b
    
type 'a s = ('a, 'a nl_s) annotated
and 'a nl_s =
  [ `Return of 'a np
  | `ThereIs of 'a np
  | `Truth of 'a np * 'a vp
  | `For of 'a np * 'a s
  | `Seq of 'a s list ]
and 'a np = ('a, 'a nl_np) annotated
and 'a nl_np =
  [ `Void
  | `PN of word * 'a rel
  (*  | `Ref of np_label * 'a rel (* TODO: replace by Qu _, with np_label as ng *) *)
  | `Qu of qu * adj * 'a ng
  | `QuOneOf of qu * word list
  | `And of 'a np list
  | `Or of 'a np list (* (* the optional int indicates that the disjunction is in the context of the i-th element *) *)
  | `Maybe of 'a np (* (* the bool indicates whether negation is suspended *) *)
  | `Not of 'a np ] (* (* the bool indicates whether negation is suspended *) *)
and 'a ng = ('a, 'a nl_ng) annotated
and 'a nl_ng =
  [ `That of word * 'a rel
  | `LabelThat of ng_label * 'a rel
  | `Aggreg of bool * 'a ng_aggreg * 'a ng ] (* the bool indicates suspension *)
and qu = [ `A | `Any of bool | `The | `Each | `All | `One | `No of bool ]
and adj =
  [ `Nil
  | `Order of word
  | `Optional of bool * adj
  | `Adj of adj * word ]
and 'a ng_aggreg =
  [ `AdjThat of word * 'a rel
  | `NounThatOf of word * 'a rel ]
and 'a rel = ('a, 'a nl_rel) annotated
and 'a nl_rel =
  [ `Nil
  | `That of 'a vp
  | `Whose of 'a ng * 'a vp
  | `Of of 'a np
  | `PP of 'a pp list
  | `Ing of word * 'a np
  | `And of 'a rel list
  | `Or of 'a rel list
  | `Maybe of 'a rel
  | `Not of 'a rel
  | `Ellipsis ]
and 'a vp = ('a, 'a nl_vp) annotated
and 'a nl_vp =
  [ `IsNP of 'a np * 'a pp list
  | `IsPP of 'a pp
  | `HasProp of word * 'a np * 'a pp list
  | `Has of 'a np * 'a pp list
  | `VT of word * 'a np * 'a pp list
  | `Subject of 'a np * 'a vp (* np is the subject of vp *)
  | `And of 'a vp list
  | `Or of 'a vp list (* the optional int indicates that the disjunction is in the context of the i-th element *)
  | `Maybe of 'a vp (* the bool indicates whether negation is suspended *)
  | `Not of 'a vp (* the bool indicates whether negation is suspended *)
  | `Ellipsis ]
and 'a pp =
  [ `Prep of word * 'a np
  | `PrepBin of word * 'a np * word * 'a np ]

let top_rel : 'a rel = X `Nil
let top_np : 'a np = X (`Qu (`A, `Nil, X (`That (`Thing, top_rel))))
let top_s : 'a s = X (`Return top_np)

let dummy_word : word = `DummyFocus
let dummy_ng : 'a ng = X (`That (`DummyFocus, top_rel))

let np_of_word w : 'a np = X (`PN (w, top_rel))
let np_of_literal l : 'a np = np_of_word (`Literal l)

(* verbalization of terms, classes, properties *)

let word_of_entity uri = `Entity (uri, Lexicon.config_entity_lexicon#value#info uri)
let word_of_class uri = `Class (uri, Lexicon.config_class_lexicon#value#info uri)
let word_syntagm_of_property uri =
  let synt, name = Lexicon.config_property_lexicon#value#info uri in
  `Prop (uri, name), synt

let rec word_of_term = function
  | Rdf.URI uri -> word_of_entity uri
  | Rdf.Number (f,s,dt) -> word_of_term (Rdf.TypedLiteral (s,dt))
  | Rdf.TypedLiteral (s,dt) -> `TypedLiteral (s, Lexicon.config_class_lexicon#value#info dt)
  | Rdf.PlainLiteral (s,"") -> `Literal s
  | Rdf.PlainLiteral (s,lang) -> `TypedLiteral (s,lang)
  | Rdf.Bnode id -> `Blank id (* should not occur *)
  | Rdf.Var v -> assert false (*`Id (0, `Var v)*) (* should not occur *)

let string_pos_of_aggreg grammar = function
  | NumberOf -> grammar#aggreg_number
  | ListOf -> grammar#aggreg_list
  | Total -> grammar#aggreg_total
  | Average -> grammar#aggreg_average
  | Maximum -> grammar#aggreg_maximum
  | Minimum -> grammar#aggreg_minimum
  | Sample -> grammar#aggreg_sample
  | Given -> grammar#aggreg_given

let word_of_aggreg grammar g =
  let s_g, pos_g = string_pos_of_aggreg grammar g in
  match pos_g with
    | `Noun -> `Op s_g
    | `Adjective -> `Op s_g

let word_of_order grammar = function
  | Unordered -> `Op ""
  | Highest -> `Op grammar#order_highest
  | Lowest -> `Op grammar#order_lowest

let word_of_incr grammar = function
  | IncrTerm t -> word_of_term t
  | IncrId id -> `Thing
  | IncrType c -> word_of_class c
  | IncrRel (p,_) -> fst (word_syntagm_of_property p)
  | IncrTriple _ -> `Relation
  | IncrTriplify -> `Relation
  | IncrIs -> `Op grammar#is
  | IncrAnd -> `Op grammar#and_
  | IncrOr -> `Op grammar#or_
  | IncrMaybe -> `Op grammar#optionally
  | IncrNot -> `Op grammar#not_
  | IncrUnselect -> `Op grammar#any
  | IncrOrder o -> word_of_order grammar o
  | IncrAggreg g -> word_of_aggreg grammar g
  | IncrForeach id -> `Thing
  | IncrAggregId (g,id) -> word_of_aggreg grammar g

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

let var_of_aggreg = function
  | NumberOf -> "number_of"
  | ListOf -> "list_of"
  | Total -> "total"
  | Average -> "average"
  | Maximum -> "maximum"
  | Minimum -> "minimum"
  | Sample -> "sample"
  | Given -> "given"

let rec labelling_p1 grammar ~labels : 'a elt_p1 -> id_label list * id_labelling_list = function
  | Is (_,np) -> labelling_s1 grammar ~labels np (* TODO: avoid keeping np.id *)
  | Type (_,c) ->
    let v, w = var_of_uri c, word_of_class c in
    [(v, `Word w)], []
  | Rel (_, p, m, np) ->
    let v = var_of_uri p in
    let w, synt = word_syntagm_of_property p in
    let ls_np =
      match synt, m with
	| `Noun, Fwd
	| `InvNoun, Bwd -> List.map (fun (_,l) -> (v, `Gen (l,w))) labels @ [(v, `Word w)]
	| _ -> [] in
    let ls_np, lab = labelling_s1 grammar ~labels:ls_np np in
    let ls =
      match synt, m with
	| `Noun, Bwd
	| `InvNoun, Fwd -> List.map (fun (_,l) -> (v, `Of (w,l))) ls_np @ [(v, `Word w)]
	| _ -> [] in
    ls, lab
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
    let ls_np1, lab1 = labelling_s1 grammar ~labels:ls_np1 np1 in
    let ls_np2, lab2 = labelling_s1 grammar ~labels:ls_np2 np2 in
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
  | IsThere _ -> [], []
and labelling_p1_opt grammar ~labels : 'a elt_p1 option -> id_label list * id_labelling_list = function
  | None -> [], []
  | Some rel -> labelling_p1 grammar ~labels rel
and labelling_s1 grammar ~labels : 'a elt_s1 -> id_label list * id_labelling_list = function
  | Det (_, An (id, modif, head), rel_opt) ->
    let ls_head = match head with Thing -> [] | Class c -> [(var_of_uri c, `Word (word_of_class c))] in
    let labels2 = labels @ ls_head in
    let ls_rel, lab_rel = labelling_p1_opt grammar ~labels:labels2 rel_opt in
    ls_head @ ls_rel, (id, `Labels (labels2 @ ls_rel)) :: lab_rel
  | Det (_, _, rel_opt) ->
    let ls_rel, lab_rel = labelling_p1_opt grammar ~labels rel_opt in
    ls_rel, lab_rel
  | AnAggreg (_, id, modif, g, rel_opt, np) ->
(*
    let v = var_of_aggreg g in
    let w, make_aggreg =
      let s_g, pos_g = string_pos_of_aggreg grammar g in
      let w = `Op s_g in
      match pos_g with
	| `Noun -> w, (fun l -> `AggregNoun (w, l))
	| `Adjective -> w, (fun l -> `AggregAdjective (w, l)) in
    let ls_np, lab_np = labelling_s1 grammar ~labels np in
    let ls_g =
      match id_of_s1 np with
      | Some id ->
	let l_np = try List.assoc id lab_np with _ -> [] in
	List.map (fun (u,l) -> (v ^ "_" ^ u, make_aggreg l)) l_np @ [(v, `Word w)]
      | None -> assert false in
*)
    let ls_np, lab_np = labelling_s1 grammar ~labels np in
    let l_np =
      match id_of_s1 np with
      | Some id -> get_id_labelling id lab_np
      | None -> assert false in
    let ls_g = labelling_aggreg_op grammar g l_np in
    ls_np, (id, `Labels ls_g) :: lab_np
  | NAnd (_, lr) ->
    let lss, labs = List.split (List.map (labelling_s1 grammar ~labels) lr) in
    List.concat lss, List.concat labs
  | NOr (_, lr) ->
    let _lss, labs = List.split (List.map (labelling_s1 grammar ~labels) lr) in
    [], List.concat labs
  | NMaybe (_, elt) ->
    let ls, lab = labelling_s1 grammar ~labels elt in
    ls, lab
  | NNot (_, elt) ->
    let _ls, lab = labelling_s1 grammar ~labels elt in
    [], lab
and labelling_dim grammar ~labelling : 'a elt_dim -> id_labelling_list = function
  | Foreach (_, id, modif, rel_opt, id2) ->
    let ls = get_id_labelling id2 labelling in
    let ls_rel, lab_rel = labelling_p1_opt grammar ~labels:ls rel_opt in
    (id, `Alias id2) :: lab_rel @ labelling
and labelling_aggreg grammar ~labelling : 'a elt_aggreg -> id_labelling_list = function
  | TheAggreg (_, id, modif, g, rel_opt, id2) ->
    let ls = get_id_labelling id2 labelling in
    let ls_g = labelling_aggreg_op grammar g ls in
    let ls_rel, lab_rel = labelling_p1_opt grammar ~labels:ls_g rel_opt in
    (id, `Labels ls_g) :: lab_rel @ labelling
and labelling_aggreg_op grammar g ls =
  let v = var_of_aggreg g in
  let w, make_aggreg =
    let s_g, pos_g = string_pos_of_aggreg grammar g in
    let w = `Op s_g in
    match pos_g with
    | `Noun -> w, (fun l -> `AggregNoun (w, l))
    | `Adjective -> w, (fun l -> `AggregAdjective (w, l)) in
  List.map (fun (u,l) -> (v ^ "_" ^ u, make_aggreg l)) ls @ [(v, `Word w)]
and labelling_s grammar ?(labelling = []) : 'a elt_s -> id_labelling_list = function
  | Return (_, np) ->
    let _ls, lab = labelling_s1 grammar ~labels:[] np in
    labelling @ lab
  | SAggreg (_,dims,aggregs) ->
    let lab1 = labelling in
    let lab2 = List.fold_left (fun labelling dim -> labelling_dim grammar ~labelling dim) lab1 dims in
    let lab3 = List.fold_left (fun labelling aggreg -> labelling_aggreg grammar ~labelling aggreg) lab2 aggregs in
    lab3
  | Seq (_, lr) ->
    List.fold_left
      (fun labelling s -> labelling_s grammar ~labelling s)
      labelling lr

      
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
  val mutable id_list : (id * [`Label of Rdf.var * (ng_label * int) | `Alias of id]) list = []
  initializer
    id_list <- List.map
      (function
      | (id, `Alias id2) -> (id, `Alias id2)
      | (id, `Labels ls) ->
	let ls = Common.list_to_set ls in (* removing duplicates *)
	let ls = if ls = [] then [("thing", `Word `Thing)] else ls in (* default label *)
	let vss =
	  List.map
	    (fun (var_prefix, ng) ->
	      let k = label_counter#rank ng in
	      var_prefix, (ng, k))
	    ls in
	(id, `Label (List.hd vss)))
      lab

  method private get_id_var_label (id : id) : Rdf.var * (ng_label * int) =
    try match List.assoc id id_list with
    | `Label (v,ng_k) -> (v,ng_k)
    | `Alias id2 -> self#get_id_var_label id2
    with Not_found -> assert false
      
  method get_id_label (id : id) : ng_label (* string *) =
    let _, (ng, k) = self#get_id_var_label id in
    let n = label_counter#count ng in
    if n = 1
    then ng
    else `Nth (k, ng)

  method get_id_var (id : id) : string =
    let prefix = try fst (self#get_id_var_label id) with _ -> "thing" in
    prefix ^ "_" ^ string_of_int id

  method get_var_id (v : string) : id =
    match Regexp.search (Regexp.regexp "[0-9]+$") v 0 with
      | Some (i,res) -> (try int_of_string (Regexp.matched_string res) with _ -> assert false)
      | None -> assert false
end

let id_labelling_of_s_annot grammar s_annot : id_labelling =
  let lab = labelling_s grammar s_annot (*elt_s_of_focus focus*) in
  new id_labelling lab

(* verbalization of focus *)

let rec head_of_modif grammar annot_opt nn rel (modif : modif_s2) : annot np =
  let qu, adj =
    match modif with
      | Select, order -> qu_adj_of_order grammar `A order
      | Unselect, order -> `Any (match annot_opt with None -> false | Some annot -> annot#is_at_focus), snd (qu_adj_of_order grammar `A order) in
  let nl = `Qu (qu, adj, X (`That (nn, rel))) in
  match annot_opt with
  | None -> X nl
  | Some annot -> A (annot,nl)
and qu_adj_of_modif grammar annot_opt qu modif : qu * adj =
  match modif with
    | Select, order -> qu_adj_of_order grammar qu order
    | Unselect, order -> `Any (match annot_opt with None -> false | Some annot -> annot#is_at_focus), snd (qu_adj_of_order grammar `A order)
and qu_adj_of_order grammar qu : order -> qu * adj = function
  | Unordered -> qu, `Nil
  | Highest -> `The, `Order (`Op grammar#order_highest)
  | Lowest -> `The, `Order (`Op grammar#order_lowest)

let ng_of_id ~id_labelling id : annot ng =
  X (`LabelThat (id_labelling#get_id_label id, X `Nil))

let np_of_aggreg grammar annot_opt qu (modif : modif_s2) (g : aggreg) (rel : annot rel) (ng : annot ng) =
  let qu, adj = qu_adj_of_modif grammar annot_opt qu modif in
  let ng_aggreg =
    let s_g, pos_g = string_pos_of_aggreg grammar g in
    match pos_g with
    | `Noun -> `NounThatOf (`Op s_g, rel)
    | `Adjective -> `AdjThat (`Op s_g, rel) in
  let susp = match annot_opt with None -> false | Some annot -> annot#is_susp_focus in
  let nl = `Qu (qu, adj, X (`Aggreg (susp, ng_aggreg, ng))) in
  match annot_opt with
  | None -> X nl
  | Some annot -> A (annot,nl)


let rec vp_of_elt_p1 grammar ~id_labelling : annot elt_p1 -> annot vp = function
  | IsThere annot -> A (annot, `Ellipsis)
  | Is (annot,np) -> A (annot, `IsNP (np_of_elt_s1 grammar ~id_labelling np, []))
  | Type (annot,c) -> A (annot, `IsNP (X (`Qu (`A, `Nil, X (`That (word_of_class c, top_rel)))), []))
  | Rel (annot,p,Fwd,np) ->
    let word, synt = word_syntagm_of_property p in
    let np = np_of_elt_s1 grammar ~id_labelling np in
    ( match synt with
    | `Noun -> A (annot, `HasProp (word, np, []))
    | `InvNoun -> A (annot, `IsNP (X (`Qu (`The, `Nil, X (`That (word, X (`Of np))))), []))
    | `TransVerb -> A (annot, `VT (word, np, []))
    | `TransAdj -> A (annot, `IsPP (`Prep (word, np))) )
  | Rel (annot,p,Bwd,np) ->
    let word, synt = word_syntagm_of_property p in
    let np = np_of_elt_s1 grammar ~id_labelling np in
    ( match synt with
    | `Noun -> A (annot, `IsNP (X (`Qu (`The, `Nil, X (`That (word, X (`Of np))))), []))
    | `InvNoun -> A (annot, `HasProp (word, np, []))
    | `TransVerb -> A (annot, `Subject (np, X (`VT (word, X `Void, []))))
    | `TransAdj -> A (annot, `Subject (np, X (`IsPP (`Prep (word, X `Void))))) )
  | Triple (annot,arg,np1,np2) ->
    let np1 = np_of_elt_s1 grammar ~id_labelling np1 in
    let np2 = np_of_elt_s1 grammar ~id_labelling np2 in
    ( match arg with
    | S -> (* has relation npp to npo / has property npp with value npo / has p npo *)
      A (annot, `HasProp (`Relation, np1, [`Prep (`Op grammar#rel_to, np2)]))
    | O -> (* has relation npp from nps / is the value of npp of nps / is the p of nps *)
      A (annot, `HasProp (`Relation, np2, [`Prep (`Op grammar#rel_from, np1)]))
    | P -> (* is a relation from nps to npo / is a property of nps with value npo *)
      A (annot, `IsNP (X (`Qu (`A, `Nil, X (`That (`Relation, top_rel)))), [`Prep (`Op grammar#rel_from, np1); `Prep (`Op grammar#rel_to, np2)])) )
  | Search (annot,c) -> vp_of_constr grammar annot c
  | Filter (annot,c) -> vp_of_constr grammar annot c
  | And (annot,lr) -> A (annot, `And (List.map (vp_of_elt_p1 grammar ~id_labelling) lr))
  | Or (annot,lr) -> A (annot, `Or (List.map (vp_of_elt_p1 grammar ~id_labelling) lr))
  | Maybe (annot,x) -> A (annot, `Maybe (vp_of_elt_p1 grammar ~id_labelling x))
  | Not (annot,x) -> A (annot, `Not (vp_of_elt_p1 grammar ~id_labelling x))
and vp_of_constr grammar annot = function
  | True -> A (annot, `Ellipsis)
  | MatchesAll lpat -> A (annot, `VT (`Op grammar#matches, X (`QuOneOf (`All, List.map (fun pat -> `Literal pat) lpat)), []))
  | MatchesAny lpat -> A (annot, `VT (`Op grammar#matches, X (`QuOneOf (`One, List.map (fun pat -> `Literal pat) lpat)), []))
  | After pat -> A (annot, `IsPP (`Prep (`Op grammar#after, np_of_literal pat)))
  | Before pat -> A (annot, `IsPP (`Prep (`Op grammar#before, np_of_literal pat)))
  | FromTo (pat1,pat2) -> A (annot, `IsPP (`PrepBin (`Op grammar#interval_from, np_of_literal pat1, `Op grammar#interval_to, np_of_literal pat2)))
  | HigherThan pat -> A (annot, `IsPP (`Prep (`Op grammar#higher_or_equal_to, np_of_literal pat)))
  | LowerThan pat -> A (annot, `IsPP (`Prep (`Op grammar#lower_or_equal_to, np_of_literal pat)))
  | Between (pat1,pat2) -> A (annot, `IsPP (`PrepBin (`Op grammar#interval_between, np_of_literal pat1, `Op grammar#interval_and, np_of_literal pat2)))
  | HasLang pat -> A (annot, `Has (X (`Qu (`A, `Nil, X (`That (`Op grammar#language, X (`Ing (`Op grammar#matching, X (`PN (`Literal pat, top_rel)))))))), []))
  | HasDatatype pat -> A (annot, `Has (X (`Qu (`A, `Nil, X (`That (`Op grammar#datatype, X (`Ing (`Op grammar#matching, X (`PN (`Literal pat, top_rel)))))))), []))
and rel_of_elt_p1_opt grammar ~id_labelling = function
  | None -> top_rel
  | Some rel -> X (`That (vp_of_elt_p1 grammar ~id_labelling rel))
and np_of_elt_s1 grammar ~id_labelling : annot elt_s1 -> annot np = function
  | Det (annot, det, rel_opt) ->
    let nl_rel = rel_of_elt_p1_opt grammar ~id_labelling rel_opt in
    det_of_elt_s2 grammar ~id_labelling annot nl_rel det
  | AnAggreg (annot,id,modif,g,rel_opt,np) ->
    np_of_aggreg grammar (Some annot)
      `A modif g
      (rel_of_elt_p1_opt grammar ~id_labelling rel_opt)
      (ng_of_elt_s1 grammar ~id_labelling np)
  | NAnd (annot,lr) -> A (annot, `And (List.map (np_of_elt_s1 grammar ~id_labelling) lr))
  | NOr (annot,lr) -> A (annot, `Or (List.map (np_of_elt_s1 grammar ~id_labelling) lr))
  | NMaybe (annot,x) -> A (annot, `Maybe (np_of_elt_s1 grammar ~id_labelling x))
  | NNot (annot,x) -> A (annot, `Not (np_of_elt_s1 grammar ~id_labelling x))
and ng_of_elt_s1 grammar ~id_labelling : annot elt_s1 -> annot ng = function
  | Det (annot, An (id,modif,head), rel_opt) ->
    A (annot, `That (word_of_elt_head head, rel_of_elt_p1_opt grammar ~id_labelling rel_opt))
  | AnAggreg (annot,id,modif,g,rel_opt,np) ->
    let rel = rel_of_elt_p1_opt grammar ~id_labelling rel_opt in
    let ng_aggreg =
      let s_g, pos_g = string_pos_of_aggreg grammar g in
      match pos_g with
      | `Noun -> `NounThatOf (`Op s_g, rel)
      | `Adjective -> `AdjThat (`Op s_g, rel) in
    let ng = ng_of_elt_s1 grammar ~id_labelling np in
    A (annot, `Aggreg (annot#is_susp_focus, ng_aggreg, ng))
  | _ -> assert false
and det_of_elt_s2 grammar ~id_labelling annot rel : elt_s2 -> annot np = function
  | Term t -> A (annot, `PN (word_of_term t, rel))
  | An (id, modif, head) -> head_of_modif grammar (Some annot) (word_of_elt_head head) rel modif
  | The id -> A (annot, `Qu (`The, `Nil, X (`LabelThat (id_labelling#get_id_label id, rel))))
(*    A (annot, `Ref (id_labelling#get_id_label id, rel)) *)
and word_of_elt_head = function
  | Thing -> `Thing
  | Class c -> word_of_class c
and np_of_elt_dim grammar ~id_labelling : annot elt_dim -> annot np = function
  | Foreach (annot,id,modif,rel_opt,id2) ->
    A (annot, `Qu (`Each, `Nil, X (`LabelThat (id_labelling#get_id_label id2, rel_of_elt_p1_opt grammar ~id_labelling rel_opt))))
and np_of_elt_aggreg grammar ~id_labelling : annot elt_aggreg -> annot np = function
  | TheAggreg (annot,id,modif,g,rel_opt,id2) ->
    np_of_aggreg grammar (Some annot) `The modif g
      (rel_of_elt_p1_opt grammar ~id_labelling rel_opt)
      (ng_of_id ~id_labelling id2)
and s_of_elt_s grammar ~id_labelling : annot elt_s -> annot s = function
  | Return (annot,np) ->
    A (annot, `Return (np_of_elt_s1 grammar ~id_labelling np))
  | SAggreg (annot,dims,aggregs) ->
    let nl_s_aggregs =
      `Return
	( match aggregs with
	| [] -> assert false
	| [aggreg] -> np_of_elt_aggreg grammar ~id_labelling aggreg
	| _ -> X (`And (List.map (np_of_elt_aggreg grammar ~id_labelling) aggregs)) ) in
    if dims = []
    then A (annot, nl_s_aggregs)
    else
      let np_dims =
	match dims with
	| [] -> assert false
	| [dim] -> np_of_elt_dim grammar ~id_labelling dim
	| _ -> X (`And (List.map (np_of_elt_dim grammar ~id_labelling) dims)) in
      A (annot, `For (np_dims, X nl_s_aggregs))
  | Seq (annot,lr) ->
    A (annot, `Seq (List.map (s_of_elt_s grammar ~id_labelling) lr))


(* linguistic transformations *)

class transf =
object
  method s : annot s -> annot s = fun s -> s
  method np : annot np -> annot np = fun np -> np
  method ng : annot ng -> annot ng = fun ng -> ng
  method adj : adj -> adj = fun adj -> adj
  method ng_aggreg : annot ng_aggreg -> annot ng_aggreg = fun ngg -> ngg
  method rel : annot rel -> annot rel = fun rel -> rel
  method vp : annot vp -> annot vp = fun vp -> vp
  method pp : annot pp -> annot pp = fun pp -> pp
end

(* top-down recursive transformation using [transf] like a visitor *)

let map_annotated x map_nl_x =
  match x with
  | A (annot,nl) -> A (annot, map_nl_x nl)
  | X nl -> X (map_nl_x nl)
  
let rec map_s (transf : transf) s =
  map_annotated (transf#s s)
    ( function
    | `Return np -> `Return (map_np transf np)
    | `ThereIs np -> `ThereIs (map_np transf np)
    | `Truth (np,vp) -> `Truth (map_np transf np, map_vp transf vp)
    | `For (np,s) -> `For (map_np transf np, map_s transf s)
    | `Seq lr -> `Seq (List.map (map_s transf) lr) )
and map_np transf np =
  map_annotated (transf#np np)
    ( function
    | `Void -> `Void
    | `PN (w,rel) -> `PN (w, map_rel transf rel)
    (*    | `Ref (np_label,rel) -> `Ref (np_label, map_rel transf rel) *)
    | `Qu (qu,adj,ng) -> `Qu (qu, map_adj transf adj, map_ng transf ng)
    | `QuOneOf (qu,lw) -> `QuOneOf (qu,lw)
    | `And (lr) -> `And (List.map (map_np transf) lr)
    | `Or (lr) -> `Or (List.map (map_np transf) lr)
    | `Maybe (np) -> `Maybe (map_np transf np)
    | `Not (np) -> `Not (map_np transf np) )
and map_ng transf ng =
  map_annotated (transf#ng ng)
    ( function
    | `That (w,rel) -> `That (w, map_rel transf rel)
    | `LabelThat (l,rel) -> `LabelThat (l, map_rel transf rel)
    | `Aggreg (susp,ngg,ng) -> `Aggreg (susp, map_ng_aggreg transf ngg, map_ng transf ng) )
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
  map_annotated (transf#rel rel)
    ( function
    | `Nil -> `Nil
    | `That vp -> `That (map_vp transf vp)
    | `Whose (ng,vp) -> `Whose (map_ng transf ng, map_vp transf vp)
    | `Of np -> `Of (map_np transf np)
    | `PP (lpp) -> `PP (List.map (map_pp transf) lpp)
    | `Ing (w,np) -> `Ing (w, map_np transf np)
    | `And lr -> `And (List.map (map_rel transf) lr)
    | `Or lr -> `Or (List.map (map_rel transf) lr)
    | `Maybe rel -> `Maybe (map_rel transf rel)
    | `Not rel -> `Not (map_rel transf rel)
    | `Ellipsis -> `Ellipsis )
and map_vp transf vp =
  map_annotated (transf#vp vp)
    ( function
    | `IsNP (np,lpp) -> `IsNP (map_np transf np, List.map (map_pp transf) lpp)
    | `IsPP pp -> `IsPP (map_pp transf pp)
    | `HasProp (w,np,lpp) -> `HasProp (w, map_np transf np, List.map (map_pp transf) lpp)
    | `Has (np,lpp) -> `Has (map_np transf np, List.map (map_pp transf) lpp)
    | `VT (w,np,lpp) -> `VT (w, map_np transf np, List.map (map_pp transf) lpp)
    | `Subject (np,vp) -> `Subject (map_np transf np, map_vp transf vp)
    | `And lr -> `And (List.map (map_vp transf) lr)
    | `Or lr -> `Or (List.map (map_vp transf) lr)
    | `Maybe vp -> `Maybe (map_vp transf vp)
    | `Not vp -> `Not (map_vp transf vp)
    | `Ellipsis -> `Ellipsis )
and map_pp transf pp =
  match transf#pp pp with
    | `Prep (w,np) -> `Prep (w, map_np transf np)
    | `PrepBin (w1,np1,w2,np2) -> `PrepBin (w1, map_np transf np1, w2, map_np transf np2)


let main_transf =
object (self)
  inherit transf
  method s nl =
    map_annotated nl
      (function
      | `Return (A (a2, `Qu (`A, adj, X (`Aggreg (susp,ngg,ng)))))
	-> `Return (A (a2, `Qu (`The, adj, X (`Aggreg (susp, ngg, ng)))))
      | `Return (A (a2, `PN (w, X `Nil)))
	-> `ThereIs (A (a2, `PN (w, X `Nil)))
      | `Return (A (a2, `PN (w, X (`That vp))))
	-> `Truth (A (a2, `PN (w, X `Nil)), vp)
      | nl -> nl)
  method np = function
  | A (a1, `Qu (qu, adj, X (`That (`Thing, X (`That (A (a2, `IsNP (X (`Qu ((`A | `The), `Nil, X ng)), []))))))))
    -> A (a1, `Qu (qu, adj, A (a2, ng)))
  | A (a1, `Qu (qu, adj, A (a2, `Aggreg (susp, ngg, A (a3, `That (`Thing, X (`That (X (`IsNP (X (`Qu ((`A | `The), `Nil, X ng)), []))))))))))
    -> A (a1, `Qu (qu, adj, A (a2, `Aggreg (susp, ngg, A (a3, ng)))))
  | A (a1, `QuOneOf (_, [w]))
    -> A (a1, `PN (w, top_rel))
  | A (a1, `Maybe (A (a2, `Qu (qu, adj, X ng))))
    -> A (a1, `Qu (qu, `Optional (a1#is_susp_focus, adj), A (a2, ng))) (* TODO: adj out of foc1? *)
  | A (a1, `Not (A (a2, `Qu (`A, adj, X ng))))
    -> A (a1, `Qu (`No (a1#is_susp_focus), adj, A (a2, ng))) (* TODO: adj out of foc1 *)
  | nl -> nl
  method rel = function
  | X (`That (A (a1, vp))) -> self#rel (A (a1, `That (X vp)))
  | A (a1, `That (X `Ellipsis)) -> A (a1, `Ellipsis)
  | A (a1, `That (X (`And lr))) -> A (a1, `And (List.map (fun vp -> X (`That vp)) lr))
  | A (a1, `That (X (`Or lr))) -> A (a1, `Or (List.map (fun vp -> X (`That vp)) lr))
(*    | `That (`Maybe (susp,vp)) -> `Maybe (susp, `That vp) *)
(*    | `That (`Not (susp,vp)) -> `Not (susp, `That vp) *)
  | A (a1, `That (X (`HasProp (p,np,lpp)))) ->
    ( match np with
    | A (a2, `Qu (`A, `Nil, X (`That (`Thing, X (`That vp)))))
      -> let vp = match vp with X nl -> A (a2, nl) | A (a3,nl) -> A (a3,nl) in
	 A (a1, `Whose (A (a2, `That (p, X (`PP lpp))), vp))
    | A (a2, `Qu (qu, adj, X (`That (`Thing, rel))))
      -> A (a1, `That (X (`HasProp (p,np,lpp)))) (* simplification at VP level *)
    | A (a2, `Qu (qu, adj, X (`Aggreg (susp, ngg, A (a3, `That (`Thing, rel2))))))
      -> A (a1, `That (X (`HasProp (p,np,lpp)))) (* idem *)
    | _ -> A (a1, `Whose (X (`That (p, X (`PP lpp))), X (`IsNP (np,[])))) )
  | A (a1, `That (X (`IsPP pp))) -> A (a1, `PP [pp])
  | nl -> nl
  method vp nl =
    map_annotated nl
      (function
      | `HasProp (p, A (a2, `Qu (qu, adj, X (`That (`Thing, rel)))), lpp)
	-> `Has (A (a2, `Qu (qu, adj, X (`That (p, rel)))), lpp)
      | `HasProp (p, A (a2, `Qu (qu, adj, X (`Aggreg (susp, ngg, A (a3, `That (`Thing, rel2)))))), lpp)
	-> `Has (A (a2, `Qu (qu, adj, X (`Aggreg (susp, ngg, A (a3, `That (p, rel2)))))), lpp)
      | `HasProp (p, A (a2, `Maybe (A (a3, `Qu (qu, adj, X (`That (`Thing, rel)))))), lpp)
	-> `Has (A (a2, `Qu (qu, `Optional (a3#is_susp_focus, adj), A (a3, `That (p, rel)))), lpp) (* TODO: adj out of a3 *)
      | nl -> nl)
end

(* tagged serialization - a la XML *)

type xml = node list
and node =
  | Kwd of string
  | Word of word
  | Suffix of xml * string (* suffix: eg. !, 's *)
  | Enum of string * xml list (* separator: eg. commas *)
  | Coord of xml * xml list (* coordination: eg. 'and' *)
  | Focus of focus * xml
  | Highlight of xml
  | Suspended of xml
  | DeleteCurrentFocus
  | DeleteIncr

let rec xml_text_content grammar l =
  String.concat " " (List.map (xml_node_text_content grammar) l)
and xml_node_text_content grammar = function
  | Kwd s -> s
  | Word w -> word_text_content grammar w
  | Suffix (x,suf) -> xml_text_content grammar x ^ suf
  | Enum (sep, xs) -> String.concat sep (List.map (xml_text_content grammar) xs)
  | Coord (xsep,xs) -> String.concat (" " ^ xml_text_content grammar xsep ^ " ") (List.map (xml_text_content grammar) xs)
  | Focus (foc,x) -> xml_text_content grammar x
  | Highlight x -> xml_text_content grammar x
  | Suspended x -> xml_text_content grammar x
  | DeleteCurrentFocus -> ""
  | DeleteIncr -> ""

let rec xml_ng_label grammar = function
  | `Word w -> [Word w]
  | `Gen (ng, w) ->
    ( match grammar#genetive_suffix with
      | Some suf -> Suffix (xml_ng_label grammar ng, suf) :: Word w :: []
      | None -> xml_ng_label grammar (`Of (w,ng)) )
  | `Of (w,ng) -> Word w :: Kwd grammar#of_ :: Kwd grammar#the :: xml_ng_label grammar ng
  | `AggregNoun (w,ng) -> Word w :: Kwd grammar#of_ :: xml_ng_label grammar ng
  | `AggregAdjective (w,ng) ->
    if grammar#adjective_before_noun
    then Word w :: xml_ng_label grammar ng
    else xml_ng_label grammar ng @ [Word w]
  | `Alias id -> assert false
  | `Nth (k,ng) -> Word (`Op (grammar#n_th k)) :: xml_ng_label grammar ng


let xml_a_an grammar xml =
  Kwd (grammar#a_an ~following:(xml_text_content grammar xml)) :: xml

let xml_suspended susp xml =
  if susp
  then [Suspended xml]
  else xml

let xml_seq grammar annot_opt (lr : xml list) =
  let seq_susp : bool list =
    match annot_opt with
    | Some annot ->
      ( match annot#seq_ids with
      | Some seq_ids -> List.map (function None -> true | _ -> false) seq_ids
      | _ -> assert false )
    | None -> List.map (fun _ -> false) lr in
  [ Coord ([Kwd grammar#and_], List.map2 (fun susp xml -> if susp then [Suspended xml] else xml) seq_susp lr) ]
let xml_and grammar lr =
  [ Coord ([Kwd grammar#and_], lr) ]
let xml_or grammar annot_opt lr =
  let susp_or = match annot_opt with None -> false | Some annot -> annot#is_susp_focus in
(*  let susp_or = isusp <> None in
    let susp_elt i = isusp <> None && isusp <> Some i in *)
  let coord = [Word (`Op grammar#or_)] in
  [ Coord ((if susp_or then [Suspended coord] else coord), lr) ]
let xml_maybe grammar annot_opt xml =
  let susp = match annot_opt with None -> false | Some annot -> annot#is_susp_focus in
  xml_suspended susp [Word (`Op grammar#optionally)] @ xml
let xml_not grammar annot_opt xml =
  let susp = match annot_opt with None -> false | Some annot -> annot#is_susp_focus in
  xml_suspended susp [Word (`Op grammar#not_)] @ xml
let xml_ellipsis = [Kwd "..."]

let xml_focus annot xml =
  let pos = annot#focus_pos in
  let focus = annot#focus in
  let xml =
    match pos with
    | `At -> [Highlight (xml @ [DeleteCurrentFocus])]
    | `Below -> [Highlight xml]
    | `Aside true -> [Suspended xml]
    | _ -> xml in
  [Focus (focus, xml)]

let xml_annotated x_annot f =
  match x_annot with
  | X x -> f None x
  | A (annot,x) -> xml_focus annot (f (Some annot) x)

let rec xml_s grammar (s : annot s) =
  xml_annotated s
    ( fun annot_opt -> function
    | `Return np -> Kwd grammar#give_me :: xml_np grammar np
    | `ThereIs np -> Kwd grammar#there_is :: xml_np grammar np
    | `Truth (np,vp) -> Kwd grammar#it_is_true_that :: xml_np grammar np @ xml_vp grammar vp
    | `For (np,s) -> [Enum (", ", [Kwd grammar#for_ :: xml_np grammar np;
				   xml_s grammar s])]
    | `Seq lr -> xml_seq grammar annot_opt (List.map (xml_s grammar) lr) )
and xml_np grammar np =
  xml_annotated np
    ( fun annot_opt -> function
    | `Void -> []
    | `PN (w,rel) -> Word w :: xml_rel grammar rel
    (*    | `Ref (np_label,rel) -> xml_np_label grammar np_label @ xml_rel grammar rel *)
    | `Qu (qu,adj,ng) -> xml_qu grammar qu (xml_adj grammar adj (xml_ng grammar ng))
    | `QuOneOf (qu,lw) -> xml_qu grammar qu (Kwd grammar#quantif_of :: Enum (", ", List.map (fun w -> [Word w]) lw) :: [])
    | `And lr -> xml_and grammar (List.map (xml_np grammar) lr)
    | `Or lr -> xml_or grammar annot_opt (List.map (xml_np grammar) lr)
    | `Maybe np -> xml_maybe grammar annot_opt (xml_np grammar np)
    | `Not np -> xml_not grammar annot_opt (xml_np grammar np) )
and xml_ng grammar rel =
  xml_annotated rel
    ( fun annot_opt -> function
    | `That (w,rel) -> Word w :: xml_rel grammar rel
    | `LabelThat (l,rel) -> xml_ng_label grammar l @ xml_rel grammar rel
    | `Aggreg (susp,ngg,ng) -> xml_ng_aggreg grammar susp (xml_ng grammar ng) ngg )
and xml_qu grammar qu xml =
  match xml with
    | Word `Thing :: xml_rem ->
      ( match qu with
	| `A -> Kwd grammar#something :: xml_rem
	| `Any susp -> xml_suspended susp [Word (`Op grammar#anything)] @ xml_rem
	| `The -> Kwd grammar#the :: xml
	| `Each -> Kwd grammar#each :: xml
	| `All -> Kwd grammar#everything :: xml_rem
	| `One -> Kwd grammar#quantif_one :: xml
	| `No susp -> xml_suspended susp [Word (`Op grammar#nothing)] @ xml_rem )
    | _ ->
      ( match qu with
	| `A -> xml_a_an grammar xml
	| `Any susp -> xml_suspended susp [Word (`Op grammar#any)] @ xml
	| `The -> Kwd grammar#the :: xml
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
and xml_ng_aggreg grammar susp xml_ng = function
  | `AdjThat (g,rel) ->
    let xml_g_rel = Word g :: xml_rel grammar rel in
    if grammar#adjective_before_noun
    then xml_suspended susp xml_g_rel @ xml_ng
    else xml_ng @ xml_suspended susp xml_g_rel
  | `NounThatOf (g,rel) -> xml_suspended susp (Word g :: xml_rel grammar rel @ [Kwd grammar#of_]) @ xml_ng
and xml_rel grammar = function
  | A (a1, `Maybe (A (a2, `That (X vp)))) -> xml_focus a1 (Kwd grammar#relative_that :: xml_vp_mod grammar `Maybe a1 a2 vp)
  | A (a1, `Not (A (a2, `That (X vp)))) -> xml_focus a1 (Kwd grammar#relative_that :: xml_vp_mod grammar `Not a1 a2 vp)
  | rel ->
    xml_annotated rel
      (fun annot_opt -> function
      | `Nil -> []
      | `That vp -> Kwd grammar#relative_that :: xml_vp grammar vp
      | `Whose (ng,vp) -> Kwd grammar#whose :: xml_ng grammar ng @ xml_vp grammar vp
      | `Of np -> Kwd grammar#of_ :: xml_np grammar np
      | `PP lpp -> xml_pp_list grammar lpp
      | `Ing (w,np) -> Word w :: xml_np grammar np
      | `And lr -> xml_and grammar (List.map (xml_rel grammar) lr)
      | `Or lr -> xml_or grammar annot_opt (List.map (xml_rel grammar) lr)
      | `Maybe rel -> xml_maybe grammar annot_opt (xml_rel grammar rel)
      | `Not rel -> xml_not grammar annot_opt (xml_rel grammar rel)
      | `Ellipsis -> xml_ellipsis )
and xml_vp grammar = function
  | A (a1, `Maybe (A (a2, vp))) -> xml_focus a1 (xml_vp_mod grammar `Maybe a1 a2 vp)
  | A (a1, `Not (A (a2, vp))) -> xml_focus a1 (xml_vp_mod grammar `Not a1 a2 vp) (* negation inversion *)
  | vp ->
    xml_annotated vp
      (fun annot_opt -> function
      | `IsNP (np,lpp) -> Kwd grammar#is :: xml_np grammar np @ xml_pp_list grammar lpp
      | `IsPP pp -> Kwd grammar#is :: xml_pp grammar pp
      | `HasProp (p,np,lpp) -> Kwd grammar#has_as_a :: Word p :: xml_np grammar np @ xml_pp_list grammar lpp
      | `Has (np,lpp) -> Kwd grammar#has :: xml_np grammar np @ xml_pp_list grammar lpp
      | `VT (w,np,lpp) -> Word w :: xml_np grammar np @ xml_pp_list grammar lpp
      | `Subject (np,vp) -> xml_np grammar np @ xml_vp grammar vp
      | `And lr -> xml_and grammar (List.map (xml_vp grammar) lr)
      | `Or lr -> xml_or grammar annot_opt (List.map (xml_vp grammar) lr)
      | `Maybe vp -> xml_maybe grammar annot_opt (xml_vp grammar vp)
      | `Not vp -> xml_not grammar annot_opt (xml_vp grammar vp)
      | `Ellipsis -> xml_ellipsis )
and xml_vp_mod grammar (op_mod : [`Not | `Maybe]) annot_mod annot_vp vp =
  let f_xml_mod = match op_mod with `Maybe -> xml_maybe | `Not -> xml_not in
  let xml_mod = xml_focus (annot_mod#down) (f_xml_mod grammar (Some annot_mod) []) in
  match op_mod, vp with
    | (`Not | `Maybe), `IsNP (np,lpp) -> xml_focus annot_vp (Kwd grammar#is :: xml_mod @ xml_np grammar np @ xml_pp_list grammar lpp)
    | (`Not | `Maybe), `IsPP pp -> xml_focus annot_vp (Kwd grammar#is :: xml_mod @ xml_pp grammar pp)
    | `Not, `HasProp (p,np,lpp) -> xml_focus annot_vp (Kwd grammar#has_as_a :: xml_mod @ Word p :: xml_np grammar np @ xml_pp_list grammar lpp)
    | `Not, `Has (np,lpp) -> xml_focus annot_vp (Kwd grammar#has :: xml_mod @ xml_np grammar np @ xml_pp_list grammar lpp)
    | _, vp -> xml_mod @ xml_focus annot_vp (xml_vp grammar (X vp))
and xml_pp_list grammar lpp =
  List.concat (List.map (xml_pp grammar) lpp)
and xml_pp grammar = function
  | `Prep (prep,np) -> Word prep :: xml_np grammar np
  | `PrepBin (prep1,np1,prep2,np2) -> Word prep1 :: xml_np grammar np1 @ Word prep2 :: xml_np grammar np2

let xml_ng_id grammar ~id_labelling id = xml_ng_label grammar (id_labelling#get_id_label id)
let xml_np_id grammar ~id_labelling id = Word (`Op grammar#the) :: xml_ng_id grammar ~id_labelling id

let xml_incr_coordinate grammar focus xml =
  match focus with
    | AtS1 _ -> xml
    | AtP1 (IsThere _, _) -> xml
    | _ -> Kwd grammar#and_ :: xml

let xml_incr grammar ~id_labelling (focus : focus) = function
  | IncrTerm t ->
    let xml_t = [Word (word_of_term t)] in
    ( match focus with
      | AtS1 (Det (_, Term t0, _), _) when t0 = t -> xml_t @ [DeleteIncr]
      | AtS1 _ -> xml_t
      | _ ->
	xml_incr_coordinate grammar focus
	  (Kwd grammar#relative_that :: Kwd grammar#is :: xml_t) )
  | IncrId id ->
    let xml = xml_np_id grammar ~id_labelling id in
    ( match focus with
      | AtS1 _ -> xml
      | _ ->
	xml_incr_coordinate grammar focus
	  (Kwd grammar#relative_that :: Kwd grammar#is :: xml) )
  | IncrType c ->
    let xml_c = [Word (word_of_class c)] in
    ( match focus with
      | AtS1 (Det (_, An (_, _, Class c0), _), _) when c0 = c ->
	xml_a_an grammar xml_c @ [DeleteIncr]
      | AtS1 _ -> xml_a_an grammar xml_c
      | _ ->
	xml_incr_coordinate grammar focus
	  (Kwd grammar#relative_that :: Kwd grammar#is :: xml_a_an grammar xml_c) )
  | IncrRel (p,Lisql.Fwd) ->
    xml_incr_coordinate grammar focus
      (Kwd grammar#relative_that ::
       let word, synt = word_syntagm_of_property p in
       match synt with
	 | `Noun -> Kwd grammar#has :: xml_a_an grammar [Word word]
	 | `InvNoun -> Kwd grammar#is :: Kwd grammar#the :: Word word :: Kwd grammar#of_ :: xml_ellipsis
	 | `TransVerb -> Word word :: xml_ellipsis
	 | `TransAdj -> Kwd grammar#is :: Word word :: xml_ellipsis)
  | IncrRel (p,Lisql.Bwd) ->
    xml_incr_coordinate grammar focus
      (Kwd grammar#relative_that ::
       let word, synt = word_syntagm_of_property p in
       match synt with
	 | `Noun -> Kwd grammar#is :: Kwd grammar#the :: Word word :: Kwd grammar#of_ :: xml_ellipsis
	 | `InvNoun -> Kwd grammar#has :: xml_a_an grammar [Word word]
	 | `TransVerb -> xml_ellipsis @ Word word :: []
	 | `TransAdj -> xml_ellipsis @ Kwd grammar#is :: Word word :: [])
  | IncrTriple (S | O as arg) ->
    xml_incr_coordinate grammar focus
      (Kwd grammar#relative_that :: Kwd grammar#has :: xml_a_an grammar [Word `Relation] @ (if arg = S then Kwd grammar#rel_to :: xml_ellipsis else Kwd grammar#rel_from :: xml_ellipsis))
  | IncrTriple P ->
    xml_incr_coordinate grammar focus
      (Kwd grammar#relative_that :: Kwd grammar#is :: xml_a_an grammar [Word `Relation] @ Kwd grammar#rel_from :: xml_ellipsis @ Kwd grammar#rel_to :: xml_ellipsis)
  | IncrTriplify -> Kwd grammar#has :: xml_a_an grammar [Word `Relation] @ Kwd (grammar#rel_from ^ "/" ^ grammar#rel_to) :: []
  | IncrIs -> xml_incr_coordinate grammar focus (Kwd grammar#relative_that :: Kwd grammar#is :: xml_ellipsis)
  | IncrAnd -> Kwd grammar#and_ :: xml_ellipsis
  | IncrOr -> Word (`Op grammar#or_) :: xml_ellipsis
  | IncrMaybe -> xml_maybe grammar None [Word dummy_word]
  | IncrNot -> xml_not grammar None [Word dummy_word]
  | IncrUnselect -> xml_np grammar (head_of_modif grammar None dummy_word top_rel (Unselect,Unordered))
  | IncrAggreg g -> xml_np grammar (np_of_aggreg grammar None `The Lisql.factory#top_modif g top_rel dummy_ng)
  | IncrOrder order -> xml_np grammar (head_of_modif grammar None dummy_word top_rel (Select,order))
  | IncrForeach id -> Word (`Op grammar#for_) :: Word (`Op grammar#each) :: xml_ng_id grammar ~id_labelling id
  | IncrAggregId (g,id) -> xml_np grammar (np_of_aggreg grammar None `The Lisql.factory#top_modif g top_rel (ng_of_id ~id_labelling id))
