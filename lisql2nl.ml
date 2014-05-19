
open Jsutils
open Lisql

(* NL generation from focus *)

type word =
  [ `Thing
  | `Relation
  | `Id of id * string
  | `Entity of Rdf.uri * string
  | `Literal of string
  | `TypedLiteral of string * string (* string, datatype/lang *)
  | `Class of Rdf.uri * string
  | `Prop of Rdf.uri * string
  | `Op of string
  | `DummyFocus ]

type nl_focus =
  [ `NoFocus
  | `Focus of focus * [ `In | `At | `Out | `Ex ] ]

type s = nl_focus *
  [ `Return of np ]
and np = nl_focus *
  [ `PN of word * rel
  | `Qu of qu * adj * word * rel
  | `QuOneOf of qu * word list
  | `And of np array
  | `Or of int option * np array (* the optional int indicates that the disjunction is in the context of the i-th element *)
  | `Maybe of bool * np (* the bool indicates whether negation is suspended *)
  | `Not of bool * np ] (* the bool indicates whether negation is suspended *)
and qu = [ `A | `Any of bool | `The | `All | `One ]
and adj =
  [ `Nil
  | `Order of word
  | `Aggreg of bool * adj * word (* the bool is for 'suspended' *)
  | `Adj of adj * word ]
and rel = nl_focus *
  [ `Nil
  | `That of vp
  | `Of of np
  | `Ing of word * np
  | `And of rel array
  | `Or of int option * rel array ]
and vp = nl_focus *
  [ `IsThere
  | `IsNP of np * pp list
  | `IsPP of pp
  | `HasProp of word * np * pp list
  | `Has of np * pp list
  | `VT of word * np * pp list
  | `And of vp array
  | `Or of int option * vp array (* the optional int indicates that the disjunction is in the context of the i-th element *)
  | `Maybe of bool * vp (* the bool indicates whether negation is suspended *)
  | `Not of bool * vp (* the bool indicates whether negation is suspended *)
  | `DummyFocus ]
and pp =
  [ `Prep of word * np
  | `PrepBin of word * np * word * np ]

let top_vp = `Nofocus, `IsThere
let top_rel = `NoFocus, `Nil
let top_np = `NoFocus, `Qu (`A, `Nil, `Thing, top_rel)
let top_s = `NoFocus, `Return top_np

let np_of_word w = `NoFocus, `PN (w, top_rel)
let np_of_literal l = np_of_word (`Literal l)

(* verbalization of terms, classes, properties *)

let name_of_uri uri =
  let uri = Js.to_string (Js.decodeURI (Js.string uri)) in
  match Regexp.search (Regexp.regexp "[^/#]+$") uri 0 with
    | Some (_,res) ->
      ( match Regexp.matched_string res with "" -> uri | name -> name )
    | None -> uri

let word_of_entity uri = `Entity (uri, name_of_uri uri)
let word_of_class uri = `Class (uri, name_of_uri uri)
let word_of_property uri = `Prop (uri, name_of_uri uri)

let rec word_of_term = function
  | Rdf.URI uri -> word_of_entity uri
  | Rdf.Number (f,s,dt) -> word_of_term (Rdf.TypedLiteral (s,dt))
  | Rdf.TypedLiteral (s,dt) -> `TypedLiteral (s, name_of_uri dt)
  | Rdf.PlainLiteral (s,"") -> `Literal s
  | Rdf.PlainLiteral (s,lang) -> `TypedLiteral (s,lang)
  | Rdf.Bnode id -> `Entity ("_:" ^ id, id) (* should not occur *)
  | Rdf.Var v -> `Id (0, v) (* should not occur *)


(* verbalization of IDs *)

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

class lexicon =
object (self)
  val label_counter : string counter = new counter

  method private var_of_uri (uri : Rdf.uri) : string =
    match Regexp.search (Regexp.regexp "[A-Za-z0-9_]+$") uri 0 with
      | Some (i,res) -> Regexp.matched_string res
      | None -> "thing"

  val mutable id_rev_list : (id * (Rdf.var * (string * int))) list = []

  method set_id_words (id : id) (words : word list) : unit =
    let words = list_to_set words in (* removing duplicates *)
    let words = if words = [] then [`Thing] else words in (* default label *)
    let l =
      List.map
	(fun w ->
	  let var_prefix, s =
	    match w with
	      | `Thing -> "thing", "thing"
	      | `Relation -> "relation", "relation"
	      | `Class (uri,s) -> self#var_of_uri uri, s
	      | `Prop (uri,s) -> self#var_of_uri uri, s
	      | _ -> assert false in
	  let k = label_counter#rank s in
	  var_prefix, (s,k))
	words in
    id_rev_list <- (id, List.hd l)::id_rev_list

  method get_id_label (id : id) : string =
    try
      let _, (s, k) = List.assoc id id_rev_list in
      let n = label_counter#count s in
      if n = 1
      then s
      else
	let s_th_ =
	  if k mod 10 = 1 && not (k mod 100 = 11) then "st "
	  else if k mod 10 = 2 && not (k mod 100 = 12) then "nd "
	  else if k mod 10 = 3 && not (k mod 100 = 13) then "rd "
	  else "th " in
	string_of_int k ^ s_th_ ^ s
    with _ -> assert false

  method get_id_var (id : id) : string =
    let prefix = try fst (List.assoc id id_rev_list) with _ -> "thing" in
    prefix ^ "_" ^ string_of_int id

  method get_var_id (v : string) : id =
    match Regexp.search (Regexp.regexp "[0-9]+$") v 0 with
      | Some (i,res) -> (try int_of_string (Regexp.matched_string res) with _ -> assert false)
      | None -> assert false
end

let words_of_arg0 = function P -> [`Relation] | S | O -> []
let words_of_arg1 = function S -> [`Relation] | P | O -> []
let words_of_arg2 = function O -> [`Relation] | S | P -> []

let rec words_elt_p1 lex : elt_p1 -> word list = function
  | Is np -> words_elt_s1 lex ~words:[] np
  | Type c -> [word_of_class c]
  | Has (p,np) -> let _ = words_elt_s1 lex ~words:[word_of_property p] np in []
  | IsOf (p,np) -> let _ = words_elt_s1 lex ~words:[] np in [word_of_property p]
  | Triple (arg,np1,np2) ->
    let _ = words_elt_s1 lex ~words:(words_of_arg1 arg) np1 in
    let _ = words_elt_s1 lex ~words:(words_of_arg2 arg) np2 in
    words_of_arg0 arg
  | Search c -> []
  | Filter c -> []
  | And ar ->
    let ar_words = Array.map (fun f -> words_elt_p1 lex f) ar in
    List.concat (Array.to_list ar_words)
  | Or ar -> Array.iter (fun f -> ignore (words_elt_p1 lex f)) ar; []
  | Maybe f -> ignore (words_elt_p1 lex f); []
  | Not f -> ignore (words_elt_p1 lex f); []
  | IsThere -> []
and words_elt_s1 lex ~words : elt_s1 -> word list = function
  | Det (An (id, modif, head), rel_opt) ->
    let l_head = match head with Thing -> [] | Class c -> [word_of_class c] in
    let l_rel_opt = match rel_opt with None -> [] | Some rel -> words_elt_p1 lex rel in
    let words = words @ l_head @ l_rel_opt in
    lex#set_id_words id words;
    words
  | Det (_,rel_opt) ->
    let l_rel_opt = match rel_opt with None -> [] | Some rel -> words_elt_p1 lex rel in
    words @ l_rel_opt
  | NAnd ar -> Array.iter (fun f -> ignore (words_elt_s1 lex ~words f)) ar; []
  | NOr ar -> Array.iter (fun f -> ignore (words_elt_s1 lex ~words f)) ar; []
  | NMaybe f -> ignore (words_elt_s1 lex ~words f); []
  | NNot f -> ignore (words_elt_s1 lex ~words f); []
and words_elt_s lex : elt_s -> unit = function
  | Return np -> ignore (words_elt_s1 lex ~words:[] np)

let lexicon_of_focus focus : lexicon =
  let lex = new lexicon in
  words_elt_s lex (elt_s_of_focus focus);
  lex

(* verbalization of focus *)

let focus_pos_down = function `In -> `In | `At -> `In | `Out -> `Out | `Ex -> `Ex

let rec head_of_modif foc nn rel (modif : modif_s2) : np =
  let susp = match foc with `Focus (_, `At) -> true | _ -> false in
  let qu, adj =
    match modif with
      | Select, order -> qu_adj_of_order order
      | Unselect, order -> `Any susp, snd (qu_adj_of_order order)
      | Aggreg (g,gorder), _ ->
	let qu_order, adj_order = qu_adj_of_order gorder in
	qu_order, adj_of_aggreg ~suspended:susp adj_order g in
  foc, `Qu (qu, adj, nn, rel)
and qu_adj_of_order : order -> qu * adj = function
  | Unordered -> `A, `Nil
  | Highest -> `The, `Order (`Op "highest-to-lowest")
  | Lowest -> `The, `Order (`Op "lowest-to-highest")
and adj_of_aggreg ~suspended adj : aggreg -> adj = function
  | NumberOf -> `Aggreg (suspended, adj, `Op "number of")
  | ListOf -> `Aggreg (suspended, adj, `Op "list of")
  | Total -> `Aggreg (suspended, adj, `Op "total")
  | Average -> `Aggreg (suspended, adj, `Op "average")
  | Maximum -> `Aggreg (suspended, adj, `Op "maximum")
  | Minimum -> `Aggreg (suspended, adj, `Op "minimum")

let word_of_id lexicon id = `Id (id, lexicon#get_id_label id)

let vp_of_elt_p1_Is (np : np) = `IsNP (np, [])
let vp_of_elt_p1_Type (c : Rdf.uri) = `IsNP ((`NoFocus, `Qu (`A, `Nil, word_of_class c, top_rel)), [])
let vp_of_elt_p1_Has (p : Rdf.uri) (np : np) = `HasProp (word_of_property p, np, [])
let vp_of_elt_p1_IsOf (p : Rdf.uri) (np : np) = `IsNP ((`NoFocus, `Qu (`The, `Nil, word_of_property p, (`NoFocus, `Of np))), [])
let vp_of_elt_p1_Triple (arg : arg) (np1 : np) (np2 : np) =
  match arg with
    | S -> (* has relation npp to npo / has property npp with value npo / has p npo *)
      `HasProp (`Relation, np1, [`Prep (`Op "to", np2)])
    | O -> (* has relation npp from nps / is the value of npp of nps / is the p of nps *)
      `HasProp (`Relation, np2, [`Prep (`Op "from", np1)])
    | P -> (* is a relation from nps to npo / is a property of nps with value npo *)
      `IsNP ((`NoFocus, `Qu (`A, `Nil, `Relation, top_rel)), [`Prep (`Op "from", np1); `Prep (`Op "to", np2)])

let rec vp_of_elt_p1 lexicon pos ctx f : vp =
  let nl =
    match f with
      | IsThere -> `IsThere
      | Is np -> vp_of_elt_p1_Is (np_of_elt_s1 lexicon (focus_pos_down pos) (IsX ctx) np)
      | Type c -> vp_of_elt_p1_Type c
      | Has (p,np) -> vp_of_elt_p1_Has p (np_of_elt_s1 lexicon (focus_pos_down pos) (HasX (p,ctx)) np)
      | IsOf (p,np) -> vp_of_elt_p1_IsOf p (np_of_elt_s1 lexicon (focus_pos_down pos) (IsOfX (p,ctx)) np)
      | Triple (arg,np1,np2) ->
	vp_of_elt_p1_Triple arg
	  (np_of_elt_s1 lexicon (focus_pos_down pos) (TripleX1 (arg,np2,ctx)) np1)
	  (np_of_elt_s1 lexicon (focus_pos_down pos) (TripleX2 (arg,np1,ctx)) np2)
      | Search c -> vp_of_constr c
      | Filter c -> vp_of_constr c
      | And ar -> `And (Array.mapi (fun i elt -> vp_of_elt_p1 lexicon (focus_pos_down pos) (AndX (i,ar,ctx)) elt) ar)
      | Or ar -> `Or (None, Array.mapi (fun i elt -> vp_of_elt_p1 lexicon (focus_pos_down pos) (OrX (i,ar,ctx)) elt) ar)
      | Maybe elt -> `Maybe (false, vp_of_elt_p1 lexicon (focus_pos_down pos) (MaybeX ctx) elt)
      | Not elt -> `Not (false, vp_of_elt_p1 lexicon (focus_pos_down pos) (NotX ctx) elt) in
  `Focus (AtP1 (f,ctx), pos), nl
and vp_of_constr = function
  | True -> `IsThere
  | MatchesAll lpat -> `VT (`Op "matches", (`NoFocus, `QuOneOf (`All, List.map (fun pat -> `Literal pat) lpat)), [])
  | MatchesAny lpat -> `VT (`Op "matches", (`NoFocus, `QuOneOf (`One, List.map (fun pat -> `Literal pat) lpat)), [])
  | After pat -> `IsPP (`Prep (`Op "after", np_of_literal pat))
  | Before pat -> `IsPP (`Prep (`Op "before", np_of_literal pat))
  | FromTo (pat1,pat2) -> `IsPP (`PrepBin (`Op "from", np_of_literal pat1, `Op "to", np_of_literal pat2))
  | HigherThan pat -> `IsPP (`Prep (`Op "higher than", np_of_literal pat))
  | LowerThan pat -> `IsPP (`Prep (`Op "lower than", np_of_literal pat))
  | Between (pat1,pat2) -> `IsPP (`PrepBin (`Op "between", np_of_literal pat1, `Op "and", np_of_literal pat2))
  | HasLang pat -> `Has ((`NoFocus, `Qu (`A, `Nil, `Op "language", (`NoFocus, `Ing (`Op "matching", (`NoFocus, `PN (`Literal pat, top_rel)))))), [])
  | HasDatatype pat -> `Has ((`NoFocus, `Qu (`A, `Nil, `Op "datatype", (`NoFocus, `Ing (`Op "matching", (`NoFocus, `PN (`Literal pat, top_rel)))))), [])
and np_of_elt_s1 lexicon pos ctx f : np =
  let foc = `Focus (AtS1 (f,ctx),pos) in
  match f with
    | Det (det, None) -> det_of_elt_s2 lexicon foc top_rel det
    | Det (det, Some rel) ->
      let foc_rel, nl_rel = vp_of_elt_p1 lexicon (focus_pos_down pos) (DetThatX (det,ctx)) rel in
      det_of_elt_s2 lexicon foc (foc_rel, `That (`NoFocus, nl_rel)) det
    | NAnd ar -> foc, `And (Array.mapi (fun i elt -> np_of_elt_s1 lexicon (focus_pos_down pos) (NAndX (i,ar,ctx)) elt) ar)
    | NOr ar -> foc, `Or (None, Array.mapi (fun i elt -> np_of_elt_s1 lexicon (focus_pos_down pos) (NOrX (i,ar,ctx)) elt) ar)
    | NMaybe elt -> foc, `Maybe (false, np_of_elt_s1 lexicon (focus_pos_down pos) (NMaybeX ctx) elt)
    | NNot elt -> foc, `Not (false, np_of_elt_s1 lexicon (focus_pos_down pos) (NNotX ctx) elt)
and det_of_elt_s2 lexicon foc rel : elt_s2 -> np = function
  | Term t -> foc, `PN (word_of_term t, rel)
  | An (id, modif, head) -> head_of_modif foc (match head with Thing -> `Thing | Class c -> word_of_class c) rel modif
  | The id -> foc, `Qu (`The, `Nil, word_of_id lexicon id, top_rel)
and s_of_elt_s lexicon pos : elt_s -> s = function
  | Return np -> `Focus (AtS (Return np), pos), `Return (np_of_elt_s1 lexicon (focus_pos_down pos) ReturnX np)

let rec s_of_ctx_p1 lexicon f (foc,nl as foc_nl) ctx : s =
  match ctx with
    | DetThatX (det,ctx2) ->
      let f2 = Det (det, Some f) in
      let nl2 = det_of_elt_s2 lexicon (`Focus (AtS1 (f2,ctx2), `Out)) (foc, `That (`NoFocus, nl)) det in
      s_of_ctx_s1 lexicon f2 nl2 ctx2
    | AndX (i,ar,ctx2) ->
      let f2 = ar.(i) <- f; And ar in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 =
	`And (Array.mapi
		(fun j elt -> if j=i then foc_nl else vp_of_elt_p1 lexicon `Out (AndX (j,ar,ctx2)) elt)
		ar) in
      s_of_ctx_p1 lexicon f2 (foc2,nl2) ctx2
    | OrX (i,ar,ctx2) ->
      ar.(i) <- f;
      let f2 = Or ar in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Ex) in
      let nl2 =
	`Or (Some i,
	     Array.mapi
	       (fun j elt -> if j=i then foc_nl else vp_of_elt_p1 lexicon `Ex (OrX (j,ar,ctx2)) elt)
	       ar) in
      s_of_ctx_p1 lexicon f2 (foc2,nl2) ctx2
   | MaybeX ctx2 ->
      let f2 = Maybe f in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Ex) in
      let nl2 = `Maybe (true, foc_nl) in
      s_of_ctx_p1 lexicon f2 (foc2,nl2) ctx2
   | NotX ctx2 ->
      let f2 = Not f in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Ex) in
      let nl2 = `Not (true, foc_nl) in
      s_of_ctx_p1 lexicon f2 (foc2,nl2) ctx2
and s_of_ctx_s1 lexicon f (foc,nl as foc_nl) ctx =
  match ctx with
    | IsX ctx2 ->
      let f2 = Is f in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Is foc_nl in
      s_of_ctx_p1 lexicon f2 (foc2,nl2) ctx2
    | HasX (p,ctx2) ->
      let f2 = Has (p,f) in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Has p foc_nl in
      s_of_ctx_p1 lexicon f2 (foc2,nl2) ctx2
    | IsOfX (p,ctx2) ->
      let f2 = IsOf (p,f) in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_IsOf p foc_nl in
      s_of_ctx_p1 lexicon f2 (foc2,nl2) ctx2
    | TripleX1 (arg,np2,ctx2) ->
      let f2 = Triple (arg,f,np2) in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Triple arg foc_nl (np_of_elt_s1 lexicon `Out (TripleX2 (arg,f,ctx2)) np2) in
      s_of_ctx_p1 lexicon f2 (foc2,nl2) ctx2
    | TripleX2 (arg,np1,ctx2) ->
      let f2 = Triple (arg,np1,f) in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Triple arg (np_of_elt_s1 lexicon `Out (TripleX1 (arg,f,ctx2)) np1) foc_nl in
      s_of_ctx_p1 lexicon f2 (foc2,nl2) ctx2
    | ReturnX ->
      let f2 = Return f in
      let foc2 = `Focus (AtS f2, `Out) in
      let nl2 = `Return foc_nl in
      (foc2,nl2)
    | NAndX (i,ar,ctx2) ->
      let f2 = ar.(i) <- f; NAnd ar in
      let foc2 = `Focus (AtS1 (f2,ctx2), `Out) in
      let nl2 =
	`And (Array.mapi
		(fun j elt -> if j=i then foc_nl else np_of_elt_s1 lexicon `Out (NAndX (j,ar,ctx2)) elt)
		ar) in
      s_of_ctx_s1 lexicon f2 (foc2,nl2) ctx2
    | NOrX (i,ar,ctx2) ->
      ar.(i) <- f;
      let f2 = NOr ar in
      let foc2 = `Focus (AtS1 (f2,ctx2), `Ex) in
      let nl2 =
	`Or (Some i,
	     Array.mapi
	       (fun j elt -> if j=i then foc_nl else np_of_elt_s1 lexicon `Ex (NOrX (j,ar,ctx2)) elt)
	       ar) in
      s_of_ctx_s1 lexicon f2 (foc2,nl2) ctx2
   | NMaybeX ctx2 ->
      let f2 = NMaybe f in
      let foc2 = `Focus (AtS1 (f2,ctx2), `Ex) in
      let nl2 = `Maybe (true, foc_nl) in
      s_of_ctx_s1 lexicon f2 (foc2,nl2) ctx2
   | NNotX ctx2 ->
      let f2 = NNot f in
      let foc2 = `Focus (AtS1 (f2,ctx2), `Ex) in
      let nl2 = `Not (true, foc_nl) in
      s_of_ctx_s1 lexicon f2 (foc2,nl2) ctx2

let s_of_focus lexicon : focus -> s = function
  | AtP1 (f,ctx) -> s_of_ctx_p1 lexicon f (vp_of_elt_p1 lexicon `At ctx f) ctx
  | AtS1 (f,ctx) -> s_of_ctx_s1 lexicon f (np_of_elt_s1 lexicon `At ctx f) ctx
  | AtS f -> s_of_elt_s lexicon `Out f
