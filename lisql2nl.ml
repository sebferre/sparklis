
open Lisql

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

type np_label =
  [ `The of int option * ng_label ]
and ng_label =
  [ `Word of word
  | `Gen of ng_label * word
  | `Of of word * ng_label
  | `Aggreg of word * ng_label ]

type focus_pos = [ `In | `At | `Out | `Ex ]

type nl_focus = focus * focus_pos

type s =
  [ `Return of np
  | `ThereIs of np
  | `Truth of np * vp
  | `Focus of nl_focus * s ]
and np =
  [ `Void
  | `PN of word * rel
  | `Ref of np_label * rel
  | `Qu of qu * adj * ng
  | `QuAggreg of bool * qu * adj * ng_aggreg * ng
  | `QuOneOf of qu * word list
  | `And of np array
  | `Or of int option * np array (* the optional int indicates that the disjunction is in the context of the i-th element *)
  | `Maybe of bool * np (* the bool indicates whether negation is suspended *)
  | `Not of bool * np (* the bool indicates whether negation is suspended *)
  | `Focus of nl_focus * np ]
and ng =
  [ `That of word * rel
  | `Focus of nl_focus * ng ]
and qu = [ `A | `Any of bool | `The | `All | `One | `No of bool ]
and adj =
  [ `Nil
  | `Order of word
  | `Aggreg of bool * adj * word (* the bool is for 'suspended' *)
  | `Optional of bool * adj
  | `Adj of adj * word ]
and ng_aggreg =
  [ `That of word * rel
  | `ThatOf of word * rel ]
and rel =
  [ `Nil
  | `That of vp
  | `Whose of ng * vp
  | `Of of np
  | `PP of pp list
  | `Ing of word * np
  | `And of rel array
  | `Or of int option * rel array
  | `Maybe of bool * rel
  | `Not of bool * rel
  | `Ellipsis
  | `Focus of nl_focus * rel ]
and vp =
  [ `IsNP of np * pp list
  | `IsPP of pp
  | `HasProp of word * np * pp list
  | `Has of np * pp list
  | `VT of word * np * pp list
  | `Subject of np * vp (* np is the subject of vp *)
  | `And of vp array
  | `Or of int option * vp array (* the optional int indicates that the disjunction is in the context of the i-th element *)
  | `Maybe of bool * vp (* the bool indicates whether negation is suspended *)
  | `Not of bool * vp (* the bool indicates whether negation is suspended *)
  | `Ellipsis
  | `Focus of nl_focus * vp ]
and pp =
  [ `Prep of word * np
  | `PrepBin of word * np * word * np ]

let top_rel = `Nil
let top_np = `Qu (`A, `Nil, `That (`Thing, top_rel))
let top_s = `Return top_np

let dummy_word : word = `DummyFocus
let dummy_ng : ng = `That (`DummyFocus, top_rel)

let np_of_word w = `PN (w, top_rel)
let np_of_literal l = np_of_word (`Literal l)

(* verbalization of terms, classes, properties *)

let name_of_uri uri =
  let uri = Js.to_string (Js.decodeURI (Js.string uri)) in
  match Regexp.search (Regexp.regexp "[^/#]+$") uri 0 with
    | Some (_,res) ->
      ( match Regexp.matched_string res with "" -> uri | name -> name )
    | None -> uri

let name_of_uri_entity =
  let re_white = Regexp.regexp "_" in
  fun uri ->
    let name = name_of_uri uri in
    try Regexp.global_replace re_white name " "
    with _ -> name

let word_of_entity uri = `Entity (uri, name_of_uri_entity uri)

let name_of_uri_concept =
  fun uri ->
    let name = name_of_uri uri in
    try Common.uncamel name
    with _ -> name

type property_syntagm = Noun | InvNoun | TransVerb | TransAdj

let prepositions = ["by"; "for"; "with"; "on"; "from"; "to"; "off"; "in"; "about"; "after"; "at"; "down"; "up"; "into"; "over"; "until"; "upon"; "within"; "without"]

let syntagm_of_property_name (name : string) : property_syntagm * string =
  if Common.has_suffix name " of" then InvNoun, String.sub name 0 (String.length name - 3)
  else if Common.has_prefix name "has " then Noun, String.sub name 4 (String.length name - 4)
  else if Common.has_suffix name "ed" || List.exists (fun prep -> Common.has_suffix name ("s " ^ prep)) prepositions then TransVerb, name
  else if List.exists (fun prep -> Common.has_suffix name (" " ^ prep)) prepositions then TransAdj, name
  else Noun, name

let word_of_class uri = `Class (uri, name_of_uri_concept uri)
let word_syntagm_of_property uri = 
  let name = name_of_uri_concept uri in
  let synt, name = syntagm_of_property_name name in
  `Prop (uri, name), synt

let rec word_of_term = function
  | Rdf.URI uri -> word_of_entity uri
  | Rdf.Number (f,s,dt) -> word_of_term (Rdf.TypedLiteral (s,dt))
  | Rdf.TypedLiteral (s,dt) -> `TypedLiteral (s, name_of_uri_concept dt)
  | Rdf.PlainLiteral (s,"") -> `Literal s
  | Rdf.PlainLiteral (s,lang) -> `TypedLiteral (s,lang)
  | Rdf.Bnode id -> `Blank id (* should not occur *)
  | Rdf.Var v -> assert false (*`Id (0, `Var v)*) (* should not occur *)

(* verbalization of IDs *)

type id_label = Rdf.var * ng_label
type id_labelling = (Lisql.id * id_label list) list

let var_of_uri (uri : Rdf.uri) : string =
  match Regexp.search (Regexp.regexp "[A-Za-z0-9_]+$") uri 0 with
    | Some (i,res) -> Regexp.matched_string res
    | None -> "thing"

let rec labelling_p1 ~labels : elt_p1 -> id_label list * id_labelling = function
  | Is np -> labelling_s1 ~labels np (* TODO: avoid keeping np.id *)
  | Type c ->
    let v, w = var_of_uri c, word_of_class c in
    [(v, `Word w)], []
  | Rel (p, m, np) ->
    let v = var_of_uri p in
    let w, synt = word_syntagm_of_property p in
    let ls_np =
      match synt, m with
	| Noun, Fwd
	| InvNoun, Bwd -> List.map (fun (_,l) -> (v, `Gen (l,w))) labels @ [(v, `Word w)]
	| Noun, _
	| InvNoun, _ -> [(v, `Word w)]
	| _ -> [] in
    let ls_np, lab = labelling_s1 ~labels:ls_np np in
    let ls =
      match synt, m with
	| Noun, Bwd
	| InvNoun, Fwd -> List.map (fun (_,l) -> (v, `Of (w,l))) ls_np @ [(v, `Word w)]
	| Noun, _
	| InvNoun, _ -> [(v, `Word w)]
	| _ -> [] in
    ls, lab
  | Triple (arg,np1,np2) ->
    let v, w = "relation", `Relation in
    let ls_np1 =
      match arg with
	| S -> List.map (fun (_,l) -> (v, `Gen (l,w))) labels @ [(v, `Word w)]
	| _ -> [] in
    let ls_np2 =
      match arg with
	| O -> List.map (fun (_,l) -> (v, `Gen (l,w))) labels @ [(v, `Word w)]
	| _ -> [] in
    let ls_np1, lab1 = labelling_s1 ~labels:ls_np1 np1 in
    let ls_np2, lab2 = labelling_s1 ~labels:ls_np2 np2 in
    let ls =
      match arg with
	| P -> List.map (fun (_,l) -> (v, `Of (w,l))) ls_np1 @ [(v, `Word w)]
	| _ -> [] in
    ls, lab1 @ lab2
  | Search _ -> [], []
  | Filter _ -> [], []
  | And ar ->
    let lss, labs = List.split (Array.to_list (Array.map (labelling_p1 ~labels) ar)) in
    List.concat lss, List.concat labs
  | Or ar ->
    let _lss, labs = List.split (Array.to_list (Array.map (labelling_p1 ~labels) ar)) in
    [], List.concat labs
  | Maybe elt ->
    let ls, lab = labelling_p1 ~labels elt in
    ls, lab
  | Not elt ->
    let _ls, lab = labelling_p1 ~labels elt in
    [], lab
  | IsThere -> [], []
and labelling_s1 ~labels : elt_s1 -> id_label list * id_labelling = function
  | Det (An (id, modif, head), rel_opt) ->
    let ls_head = match head with Thing -> [] | Class c -> [(var_of_uri c, `Word (word_of_class c))] in
    let labels2 = labels @ ls_head in
    let ls_rel, lab_rel = match rel_opt with None -> [], [] | Some rel -> labelling_p1 ~labels:labels2 rel in
    ls_head @ ls_rel, (id, labels2 @ ls_rel) :: lab_rel
  | Det (_, rel_opt) ->
    let ls_rel, lab_rel = match rel_opt with None -> [], [] | Some rel -> labelling_p1 ~labels rel in
    ls_rel, lab_rel
  | AnAggreg (id, modif, g, rel_opt, np) ->
    let v, w =
      match g with
	| NumberOf -> "number_of", `Op "number of"
	| ListOf -> "list_of", `Op "list of"
	| Total -> "total", `Op "total"
	| Average -> "average", `Op "average"
	| Maximum -> "maximum", `Op "maximum"
	| Minimum -> "minimum", `Op "minimum" in
    let ls_np, lab_np = labelling_s1 ~labels np in
    let ls_g = List.map (fun (u,l) -> (v ^ "_" ^ u, `Aggreg (w,l))) (labels @ ls_np) @ [(v, `Word w)] in
    ls_np, (id, ls_g) :: lab_np
  | NAnd ar ->
    let lss, labs = List.split (Array.to_list (Array.map (labelling_s1 ~labels) ar)) in
    List.concat lss, List.concat labs
  | NOr ar ->
    let _lss, labs = List.split (Array.to_list (Array.map (labelling_s1 ~labels) ar)) in
    [], List.concat labs
  | NMaybe elt ->
    let ls, lab = labelling_s1 ~labels elt in
    ls, lab
  | NNot elt ->
    let _ls, lab = labelling_s1 ~labels elt in
    [], lab
and labelling_s : elt_s -> id_labelling = function
  | Return np ->
    let _ls, lab = labelling_s1 ~labels:[] np in
    lab

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

class lexicon (lab : id_labelling) =
object
  val label_counter : ng_label counter = new counter
  val mutable id_list : (id * (Rdf.var * (ng_label * int))) list = []
  initializer
    id_list <- List.map
      (fun (id,ls) ->
	let ls = Common.list_to_set ls in (* removing duplicates *)
	let ls = if ls = [] then [("thing", `Word `Thing)] else ls in (* default label *)
	let vss =
	  List.map
	    (fun (var_prefix, ng) ->
	      (*let var_prefix, s = id_label_aggregate l in*)
	      let k = label_counter#rank ng in
	      var_prefix, (ng,k))
	    ls in
	(id, List.hd vss))
      lab

  method get_id_label (id : id) : np_label (* string *) =
    try
      let _, (ng, k) = List.assoc id id_list in
      let n = label_counter#count ng in
      if n = 1
      then `The (None, ng)
      else `The (Some k, ng)
    with _ -> assert false

  method get_id_var (id : id) : string =
    let prefix = try fst (List.assoc id id_list) with _ -> "thing" in
    prefix ^ "_" ^ string_of_int id

  method get_var_id (v : string) : id =
    match Regexp.search (Regexp.regexp "[0-9]+$") v 0 with
      | Some (i,res) -> (try int_of_string (Regexp.matched_string res) with _ -> assert false)
      | None -> assert false
end

let lexicon_of_focus focus : lexicon =
  let lab = labelling_s (elt_s_of_focus focus) in
  new lexicon lab

(* verbalization of focus *)

let focus_pos_down = function `In -> `In | `At -> `In | `Out -> `Out | `Ex -> `Ex

let focus_down (focus,pos) = (focus, focus_pos_down pos)

let is_suspended_focus = function
  | (_, `At) -> true
  | _ -> false

let rec head_of_modif ~suspended nn rel (modif : modif_s2) : np =
  let qu, adj =
    match modif with
      | Select, order -> qu_adj_of_order order
      | Unselect, order -> `Any suspended, snd (qu_adj_of_order order) in
  `Qu (qu, adj, `That (nn, rel))
and qu_adj_of_modif ~suspended modif : qu * adj =
  match modif with
    | Select, order -> qu_adj_of_order order
    | Unselect, order -> `Any suspended, snd (qu_adj_of_order order)
and qu_adj_of_order : order -> qu * adj = function
  | Unordered -> `A, `Nil
  | Highest -> `The, `Order (`Op "highest-to-lowest")
  | Lowest -> `The, `Order (`Op "lowest-to-highest")


let vp_of_elt_p1_Is (np : np) = `IsNP (np, [])

let vp_of_elt_p1_Type (c : Rdf.uri) = `IsNP (`Qu (`A, `Nil, `That (word_of_class c, top_rel)), [])

let vp_of_elt_p1_Has (p : Rdf.uri) (np : np) =
  let word, synt = word_syntagm_of_property p in
  match synt with
    | Noun -> `HasProp (word, np, [])
    | InvNoun -> `IsNP (`Qu (`The, `Nil, `That (word, `Of np)), [])
    | TransVerb -> `VT (word, np, [])
    | TransAdj -> `IsPP (`Prep (word, np))
let vp_of_elt_p1_IsOf (p : Rdf.uri) (np : np) =
  let word, synt = word_syntagm_of_property p in
  match synt with
    | Noun -> `IsNP (`Qu (`The, `Nil, `That (word, `Of np)), [])
    | InvNoun -> `HasProp (word, np, [])
    | TransVerb -> `Subject (np, `VT (word, `Void, []))
    | TransAdj -> `Subject (np, `IsPP (`Prep (word, `Void)))

let vp_of_elt_p1_Rel (p : Rdf.uri) (m : modif_p2) (np : np) =
  match m with
    | Fwd -> vp_of_elt_p1_Has p np
    | Bwd -> vp_of_elt_p1_IsOf p np

let vp_of_elt_p1_Triple (arg : arg) (np1 : np) (np2 : np) =
  match arg with
    | S -> (* has relation npp to npo / has property npp with value npo / has p npo *)
      `HasProp (`Relation, np1, [`Prep (`Op "to", np2)])
    | O -> (* has relation npp from nps / is the value of npp of nps / is the p of nps *)
      `HasProp (`Relation, np2, [`Prep (`Op "from", np1)])
    | P -> (* is a relation from nps to npo / is a property of nps with value npo *)
      `IsNP (`Qu (`A, `Nil, `That (`Relation, top_rel)), [`Prep (`Op "from", np1); `Prep (`Op "to", np2)])

let np_of_elt_s1_AnAggreg ~suspended (modif : modif_s2) (g : aggreg) (rel : rel) (ng : ng) =
  let qu, adj = qu_adj_of_modif ~suspended modif in
  let ng_aggreg =
    match g with
      | NumberOf -> `ThatOf (`Op "number", rel)
      | ListOf -> `ThatOf (`Op "list", rel)
      | Total -> `That (`Op "total", rel)
      | Average -> `That (`Op "average", rel)
      | Maximum -> `That (`Op "maximum", rel)
      | Minimum -> `That (`Op "minimum", rel) in
  `QuAggreg (suspended, qu, adj, ng_aggreg, ng)


let rec vp_of_elt_p1 lexicon pos ctx f : vp =
  let nl =
    match f with
      | IsThere -> `Ellipsis
      | Is np -> vp_of_elt_p1_Is (np_of_elt_s1 lexicon (focus_pos_down pos) (IsX ctx) np)
      | Type c -> vp_of_elt_p1_Type c
      | Rel (p,m,np) -> vp_of_elt_p1_Rel p m (np_of_elt_s1 lexicon (focus_pos_down pos) (RelX (p,m,ctx)) np)
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
  `Focus ((AtP1 (f,ctx), pos), nl)
and vp_of_constr = function
  | True -> `Ellipsis
  | MatchesAll lpat -> `VT (`Op "matches", `QuOneOf (`All, List.map (fun pat -> `Literal pat) lpat), [])
  | MatchesAny lpat -> `VT (`Op "matches", `QuOneOf (`One, List.map (fun pat -> `Literal pat) lpat), [])
  | After pat -> `IsPP (`Prep (`Op "after", np_of_literal pat))
  | Before pat -> `IsPP (`Prep (`Op "before", np_of_literal pat))
  | FromTo (pat1,pat2) -> `IsPP (`PrepBin (`Op "from", np_of_literal pat1, `Op "to", np_of_literal pat2))
  | HigherThan pat -> `IsPP (`Prep (`Op "higher or equal to", np_of_literal pat))
  | LowerThan pat -> `IsPP (`Prep (`Op "lower or equal to", np_of_literal pat))
  | Between (pat1,pat2) -> `IsPP (`PrepBin (`Op "between", np_of_literal pat1, `Op "and", np_of_literal pat2))
  | HasLang pat -> `Has (`Qu (`A, `Nil, `That (`Op "language", `Ing (`Op "matching", `PN (`Literal pat, top_rel)))), [])
  | HasDatatype pat -> `Has (`Qu (`A, `Nil, `That (`Op "datatype", `Ing (`Op "matching", `PN (`Literal pat, top_rel)))), [])
and rel_of_elt_p1_opt lexicon pos ctx = function
  | None -> top_rel
  | Some rel -> `That (vp_of_elt_p1 lexicon pos ctx rel)
and np_of_elt_s1 lexicon pos ctx f : np =
  let foc = (AtS1 (f,ctx),pos) in
  match f with
    | Det (det, rel_opt) ->
      let nl_rel = rel_of_elt_p1_opt lexicon (focus_pos_down pos) (DetThatX (det,ctx)) rel_opt in
      det_of_elt_s2 lexicon foc nl_rel det
    | AnAggreg (id,modif,g,rel_opt,np) ->
      let nl =
	np_of_elt_s1_AnAggreg ~suspended:false
	  modif g
	  (rel_of_elt_p1_opt lexicon (focus_pos_down pos) (AnAggregThatX (id,modif,g,np,ctx)) rel_opt)
	  (ng_of_elt_s1 lexicon (focus_pos_down pos) (AnAggregX (id,modif,g,rel_opt,ctx)) np) in
      `Focus (foc, nl)
    | NAnd ar -> `Focus (foc, `And (Array.mapi (fun i elt -> np_of_elt_s1 lexicon (focus_pos_down pos) (NAndX (i,ar,ctx)) elt) ar))
    | NOr ar -> `Focus (foc, `Or (None, Array.mapi (fun i elt -> np_of_elt_s1 lexicon (focus_pos_down pos) (NOrX (i,ar,ctx)) elt) ar))
    | NMaybe elt -> `Focus (foc, `Maybe (false, np_of_elt_s1 lexicon (focus_pos_down pos) (NMaybeX ctx) elt))
    | NNot elt -> `Focus (foc, `Not (false, np_of_elt_s1 lexicon (focus_pos_down pos) (NNotX ctx) elt))
and ng_of_elt_s1 lexicon pos ctx f =
  let foc = (AtS1 (f,ctx), pos) in
  match f with
    | Det (An (id,modif,head) as det, rel_opt) ->
      `Focus (foc, `That (word_of_elt_head head, rel_of_elt_p1_opt lexicon (focus_pos_down pos) (DetThatX (det, ctx)) rel_opt))
    | _ -> assert false
and det_of_elt_s2 lexicon foc rel : elt_s2 -> np = function
  | Term t -> `Focus (foc, `PN (word_of_term t, rel))
  | An (id, modif, head) -> `Focus (foc, head_of_modif ~suspended:(is_suspended_focus foc) (word_of_elt_head head) rel modif)
  | The id -> `Focus (foc, `Ref (lexicon#get_id_label id, rel))
and word_of_elt_head = function
  | Thing -> `Thing
  | Class c -> word_of_class c
and s_of_elt_s lexicon pos : elt_s -> s = function
  | Return np ->
    let foc = (AtS (Return np), pos) in
    `Focus (foc, `Return (np_of_elt_s1 lexicon (focus_pos_down pos) ReturnX np))

(* in *_of_ctx_*, [pos = `At] if semantically at current focus *)
let rec s_of_ctx_p1 lexicon pos f foc_nl ctx : s =
  match ctx with
    | DetThatX (det,ctx2) ->
      let f2 = Det (det, Some f) in
      let foc2_nl2 = det_of_elt_s2 lexicon (AtS1 (f2,ctx2), `Out) (`That foc_nl) det in
      s_of_ctx_s1 lexicon pos f2 foc2_nl2 ctx2
    | AnAggregThatX (id,modif,g,np,ctx2) ->
      let f2 = AnAggreg (id, modif, g, Some f, np) in
      let foc2 = (AtS1 (f2,ctx2), `Out) in
      let nl2 = np_of_elt_s1_AnAggreg ~suspended:false modif g
	(`That foc_nl)
	(ng_of_elt_s1 lexicon `Out (AnAggregX (id, modif, g, Some f, ctx2)) np) in
      s_of_ctx_s1 lexicon pos f2 (`Focus (foc2,nl2)) ctx2
    | AndX (i,ar,ctx2) ->
      let f2 = ar.(i) <- f; And ar in
      let foc2 = (AtP1 (f2,ctx2), `Out) in
      let nl2 =
	`And (Array.mapi
		(fun j elt -> if j=i then foc_nl else vp_of_elt_p1 lexicon `Out (AndX (j,ar,ctx2)) elt)
		ar) in
      s_of_ctx_p1 lexicon pos f2 (`Focus (foc2,nl2)) ctx2
    | OrX (i,ar,ctx2) ->
      ar.(i) <- f;
      let f2 = Or ar in
      let foc2 = (AtP1 (f2,ctx2), `Ex) in
      let nl2 =
	`Or (Some i,
	     Array.mapi
	       (fun j elt -> if j=i then foc_nl else vp_of_elt_p1 lexicon `Ex (OrX (j,ar,ctx2)) elt)
	       ar) in
      s_of_ctx_p1 lexicon pos f2 (`Focus (foc2,nl2)) ctx2
   | MaybeX ctx2 ->
      let f2 = Maybe f in
      let foc2 = (AtP1 (f2,ctx2), `Ex) in
      let nl2 = `Maybe (true, foc_nl) in
      s_of_ctx_p1 lexicon pos f2 (`Focus (foc2,nl2)) ctx2
   | NotX ctx2 ->
      let f2 = Not f in
      let foc2 = (AtP1 (f2,ctx2), `Ex) in
      let nl2 = `Not (true, foc_nl) in
      s_of_ctx_p1 lexicon pos f2 (`Focus (foc2,nl2)) ctx2
and s_of_ctx_s1 lexicon pos f foc_nl ctx =
  match ctx with
    | IsX ctx2 ->
      let f2 = Is f in
      let foc2 = (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Is foc_nl in
      s_of_ctx_p1 lexicon pos f2 (`Focus (foc2,nl2)) ctx2
    | RelX (p,m,ctx2) ->
      let f2 = Rel (p,m,f) in
      let foc2 = (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Rel p m foc_nl in
      s_of_ctx_p1 lexicon `Out f2 (`Focus (foc2,nl2)) ctx2
    | TripleX1 (arg,np2,ctx2) ->
      let f2 = Triple (arg,f,np2) in
      let foc2 = (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Triple arg foc_nl (np_of_elt_s1 lexicon `Out (TripleX2 (arg,f,ctx2)) np2) in
      s_of_ctx_p1 lexicon `Out f2 (`Focus (foc2,nl2)) ctx2
    | TripleX2 (arg,np1,ctx2) ->
      let f2 = Triple (arg,np1,f) in
      let foc2 = (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Triple arg (np_of_elt_s1 lexicon `Out (TripleX1 (arg,f,ctx2)) np1) foc_nl in
      s_of_ctx_p1 lexicon `Out f2 (`Focus (foc2,nl2)) ctx2
    | ReturnX ->
      let f2 = Return f in
      let foc2 = (AtS f2, `Out) in
      let nl2 = `Return foc_nl in
      `Focus (foc2,nl2)
    | AnAggregX (id,modif,g,rel_opt,ctx2) ->
      let f2 = AnAggreg (id, modif, g, rel_opt, f) in
      let foc2 = (AtS1 (f2,ctx2), `Out) in
      let nl2 = np_of_elt_s1_AnAggreg ~suspended:(pos = `At) (*is_suspended_focus foc*) modif g
	(rel_of_elt_p1_opt lexicon `Out (AnAggregThatX (id, modif, g, f, ctx2)) rel_opt)
        ( match foc_nl with `Focus (foc, `Qu (_,_,ng)) -> `Focus (foc, ng) | `Qu (_,_,ng) -> ng | _ -> assert false )  (* TODO: what to do with hidden modif/adj *) in
      s_of_ctx_s1 lexicon `Out f2 (`Focus (foc2,nl2)) ctx2
    | NAndX (i,ar,ctx2) ->
      let f2 = ar.(i) <- f; NAnd ar in
      let foc2 = (AtS1 (f2,ctx2), `Out) in
      let nl2 =
	`And (Array.mapi
		(fun j elt -> if j=i then foc_nl else np_of_elt_s1 lexicon `Out (NAndX (j,ar,ctx2)) elt)
		ar) in
      s_of_ctx_s1 lexicon pos f2 (`Focus (foc2,nl2)) ctx2
    | NOrX (i,ar,ctx2) ->
      ar.(i) <- f;
      let f2 = NOr ar in
      let foc2 = (AtS1 (f2,ctx2), `Ex) in
      let nl2 =
	`Or (Some i,
	     Array.mapi
	       (fun j elt -> if j=i then foc_nl else np_of_elt_s1 lexicon `Ex (NOrX (j,ar,ctx2)) elt)
	       ar) in
      s_of_ctx_s1 lexicon pos f2 (`Focus (foc2,nl2)) ctx2
   | NMaybeX ctx2 ->
      let f2 = NMaybe f in
      let foc2 = (AtS1 (f2,ctx2), `Ex) in
      let nl2 = `Maybe (true, foc_nl) in
      s_of_ctx_s1 lexicon pos f2 (`Focus (foc2,nl2)) ctx2
   | NNotX ctx2 ->
      let f2 = NNot f in
      let foc2 = (AtS1 (f2,ctx2), `Ex) in
      let nl2 = `Not (true, foc_nl) in
      s_of_ctx_s1 lexicon pos f2 (`Focus (foc2,nl2)) ctx2

let s_of_focus lexicon : focus -> s = function
  | AtP1 (f,ctx) -> s_of_ctx_p1 lexicon `At f (vp_of_elt_p1 lexicon `At ctx f) ctx
  | AtS1 (f,ctx) -> s_of_ctx_s1 lexicon `At f (np_of_elt_s1 lexicon `At ctx f) ctx
  | AtS f -> s_of_elt_s lexicon `Out f

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
  method pp : pp -> pp = fun pp -> pp
end

(* top-down recursive transformation using [transf] like a visitor *)
let rec map_s (transf : transf) s =
  match transf#s s with
    | `Return np -> `Return (map_np transf np)
    | `ThereIs np -> `ThereIs (map_np transf np)
    | `Truth (np,vp) -> `Truth (map_np transf np, map_vp transf vp)
    | `Focus (foc,s) -> `Focus (foc, map_s transf s)
and map_np transf np =
  match transf#np np with
    | `Void -> `Void
    | `PN (w,rel) -> `PN (w, map_rel transf rel)
    | `Ref (np_label,rel) -> `Ref (np_label, map_rel transf rel)
    | `Qu (qu,adj,ng) -> `Qu (qu, map_adj transf adj, map_ng transf ng)
    | `QuAggreg (susp,qu,adj,ngg,ng) -> `QuAggreg (susp, qu, map_adj transf adj, map_ng_aggreg transf ngg, map_ng transf ng)
    | `QuOneOf (qu,lw) -> `QuOneOf (qu,lw)
    | `And ar -> `And (Array.map (map_np transf) ar)
    | `Or (isusp,ar) -> `Or (isusp, Array.map (map_np transf) ar)
    | `Maybe (susp,np) -> `Maybe (susp, map_np transf np)
    | `Not (susp,np) -> `Not (susp, map_np transf np)
    | `Focus (foc,np) -> `Focus (foc, map_np transf np)
and map_ng transf ng =
  match transf#ng ng with
    | `That (w,rel) -> `That (w, map_rel transf rel)
    | `Focus (foc,ng) -> `Focus (foc, map_ng transf ng)
and map_adj transf adj =
  match transf#adj adj with
    | `Nil -> `Nil
    | `Order w -> `Order w
    | `Aggreg (susp,adj,w) -> `Aggreg (susp, map_adj transf adj, w)
    | `Optional (susp,adj) -> `Optional (susp, map_adj transf adj)
    | `Adj (adj,w) -> `Adj (map_adj transf adj, w)
and map_ng_aggreg transf ngg =
  match transf#ng_aggreg ngg with
    | `That (w,rel) -> `That (w, map_rel transf rel)
    | `ThatOf (w,rel) -> `ThatOf (w, map_rel transf rel)
and map_rel transf rel =
  match transf#rel rel with
    | `Nil -> `Nil
    | `That vp -> `That (map_vp transf vp)
    | `Whose (ng,vp) -> `Whose (map_ng transf ng, map_vp transf vp)
    | `Of np -> `Of (map_np transf np)
    | `PP lpp -> `PP (List.map (map_pp transf) lpp)
    | `Ing (w,np) -> `Ing (w, map_np transf np)
    | `And ar -> `And (Array.map (map_rel transf) ar)
    | `Or (isusp,ar) -> `Or (isusp, Array.map (map_rel transf) ar)
    | `Maybe (susp,rel) -> `Maybe (susp, map_rel transf rel)
    | `Not (susp,rel) -> `Not (susp, map_rel transf rel)
    | `Ellipsis -> `Ellipsis
    | `Focus (foc, rel) -> `Focus (foc, map_rel transf rel)
and map_vp transf vp =
  match transf#vp vp with
    | `IsNP (np,lpp) -> `IsNP (map_np transf np, List.map (map_pp transf) lpp)
    | `IsPP pp -> `IsPP (map_pp transf pp)
    | `HasProp (w,np,lpp) -> `HasProp (w, map_np transf np, List.map (map_pp transf) lpp)
    | `Has (np,lpp) -> `Has (map_np transf np, List.map (map_pp transf) lpp)
    | `VT (w,np,lpp) -> `VT (w, map_np transf np, List.map (map_pp transf) lpp)
    | `Subject (np,vp) -> `Subject (map_np transf np, map_vp transf vp)
    | `And ar -> `And (Array.map (map_vp transf) ar)
    | `Or (isusp,ar) -> `Or (isusp, Array.map (map_vp transf) ar)
    | `Maybe (susp,vp) -> `Maybe (susp, map_vp transf vp)
    | `Not (susp,vp) -> `Not (susp, map_vp transf vp)
    | `Ellipsis -> `Ellipsis
    | `Focus (foc,vp) -> `Focus (foc, map_vp transf vp)
and map_pp transf pp =
  match transf#pp pp with
    | `Prep (w,np) -> `Prep (w, map_np transf np)
    | `PrepBin (w1,np1,w2,np2) -> `PrepBin (w1, map_np transf np1, w2, map_np transf np2)


let main_transf =
object (self)
  inherit transf
  method s = function
    | `Return (`Focus (foc, `QuAggreg (susp,_qu,adj,ngg,ng))) -> `Return (`Focus (foc, `QuAggreg (susp, `The, adj, ngg, ng)))
    | `Return (`Focus (foc, `PN (w, `Nil))) -> `ThereIs (`Focus (foc, `PN (w, `Nil)))
    | `Return (`Focus (foc, `PN (w, `That vp))) -> `Truth (`Focus (foc, `PN (w, `Nil)), vp)
    | nl -> nl
  method np = function
    | `Qu (qu, adj, `That (`Thing, `That (`Focus (foc2, `IsNP (`Qu ((`A | `The), `Nil, nl_ng), []))))) ->
      `Qu (qu, adj, `Focus (foc2, nl_ng))
    | `QuAggreg (susp, qu, adj, ngg, `Focus (foc2, `That (`Thing, `That (`IsNP (`Qu ((`A | `The), `Nil, nl_ng), []))))) ->
      `QuAggreg (susp, qu, adj, ngg, `Focus (foc2, nl_ng))
    | `QuOneOf (_, [w]) -> `PN (w, top_rel)
    | `Maybe (susp, `Focus (foc1, `Qu (qu, adj, ng))) -> `Qu (qu, `Optional (susp, adj), `Focus (foc1, ng)) (* TODO: adj out of foc1? *)
    | `Not (susp, `Focus (foc1, `Qu (`A, adj, ng))) -> `Qu (`No susp, adj, `Focus (foc1, ng)) (* TODO: adj out of foc1 *)
    | nl -> nl
  method rel = function
    | `That (`Focus (foc, vp)) -> `Focus (foc, self#rel (`That vp))
    | `That `Ellipsis -> `Ellipsis
    | `That (`And ar) -> `And (Array.map (fun vp -> `That vp) ar)
    | `That (`Or (isusp,ar)) -> `Or (isusp, Array.map (fun vp -> `That vp) ar)
(*    | `That (`Maybe (susp,vp)) -> `Maybe (susp, `That vp) *)
(*    | `That (`Not (susp,vp)) -> `Not (susp, `That vp) *)
    | `That (`HasProp (p,np,lpp)) ->
      ( match np with
	| `Focus (foc2, `Qu (`A, `Nil, `That (`Thing, `That vp))) -> `Whose (`Focus (focus_down foc2, `That (p, `PP lpp)), `Focus (foc2,vp))
	| `Focus (foc2, `Qu (qu, adj, `That (`Thing, rel))) -> `That (`HasProp (p,np,lpp)) (* simplification at VP level *)
	| `Focus (foc2, `QuAggreg (susp, qu, adj, ngg, `Focus (foc3, `That (`Thing, rel2)))) -> `That (`HasProp (p,np,lpp)) (* idem *)
	| _ -> `Whose (`That (p, `PP lpp), `IsNP (np,[])) )
    | `That (`IsPP pp) -> `PP [pp]
    | nl -> nl
  method vp = function
    | `HasProp (p, `Focus (foc2, `Qu (qu, adj, `That (`Thing, rel))), lpp) ->
      `Has (`Focus (foc2, `Qu (qu, adj, `That (p, rel))), lpp)
    | `HasProp (p, `Focus (foc2, `QuAggreg (susp, qu, adj, ngg, `Focus (foc3, `That (`Thing, rel2)))), lpp) ->
      `Has (`Focus (foc2, `QuAggreg (susp, qu, adj, ngg, `Focus (foc3, `That (p, rel2)))), lpp)
    | `HasProp (p, `Focus (foc1, `Maybe (susp, `Focus (foc2, `Qu (qu, adj, `That (`Thing, rel))))), lpp) ->
      `Has (`Focus (foc1, `Qu (qu, `Optional (susp, adj), `Focus (foc2, `That (p, rel)))), lpp) (* TODO: adj out of foc2 *)
    | nl -> nl
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

let rec xml_np_label (`The (k_opt, ng) : np_label) =
  let xml_ng = xml_ng_label ng in
  let nl_rank =
    match k_opt with
      | None -> []
      | Some k ->
	let s_th =
	  if k mod 10 = 1 && not (k mod 100 = 11) then "st"
	  else if k mod 10 = 2 && not (k mod 100 = 12) then "nd"
	  else if k mod 10 = 3 && not (k mod 100 = 13) then "rd"
	  else "th" in
	[Word (`Op (string_of_int k ^ s_th))] in
  Word (`Op "the") :: nl_rank @ xml_ng
and xml_ng_label = function
  | `Word w -> [Word w]
  | `Gen (ng, w) -> Suffix (xml_ng_label ng, "'s") :: Word w :: [] (* TODO: avoid space before 's *)
  | `Of (w,ng) -> Word w :: Kwd "of" :: Kwd "the" :: xml_ng_label ng
  | `Aggreg (w,ng) -> Word w :: xml_ng_label ng

let rec xml_starts_with_vowel = function
  | [] -> false
  | x::_ -> node_starts_with_vowel x
and node_starts_with_vowel = function
  | Kwd s -> string_starts_with_vowel s
  | Word w -> word_starts_with_vowel w
  | Enum (sep, []) -> false
  | Enum (sep, x::_) -> xml_starts_with_vowel x
  | Suffix (x, _) -> xml_starts_with_vowel x
  | Coord (sep, []) -> false
  | Coord (sep, x::_) -> xml_starts_with_vowel x
  | Focus (foc, x) -> xml_starts_with_vowel x
  | Highlight x -> xml_starts_with_vowel x
  | Suspended x -> xml_starts_with_vowel x
  | DeleteCurrentFocus -> false
  | DeleteIncr -> false
and word_starts_with_vowel = function
  | `Thing -> false
  | `Relation -> false
  | `Class (uri,s) -> string_starts_with_vowel s
  | `Prop (uri,s) -> string_starts_with_vowel s
  | `Op s -> string_starts_with_vowel s
  | _ -> false
and string_starts_with_vowel s =
  try
    let c = Char.lowercase s.[0] in
    c = 'a' || c = 'e' || c = 'i' || c = 'o' (* || c = 'u' : 'u' is more often pronounced [y] *)
  with _ -> false

let xml_a_an xml =
  if xml_starts_with_vowel xml
  then Kwd "an" :: xml
  else Kwd "a" :: xml

let xml_suspended susp xml =
  if susp
  then [Suspended xml]
  else xml

let xml_and ar =
  [ Coord ([Kwd "and"], Array.to_list ar) ]
let xml_or isusp ar =
  let susp_or = isusp <> None in
  let susp_elt i = isusp <> None && isusp <> Some i in
  let coord = [Word (`Op "or")] in
  [ Coord ((if susp_or then [Suspended coord] else coord),
	   Array.to_list
	     (Array.mapi
		(fun i xml_i ->
		  if susp_elt i
		  then [Suspended xml_i]
		  else xml_i)
		ar)) ]
let xml_maybe susp xml =
  xml_suspended susp [Word (`Op "optionally")] @ xml
let xml_not susp xml =
  xml_suspended susp [Word (`Op "not")] @ xml
let xml_ellipsis = [Kwd "..."]

let xml_focus (focus,pos) xml =
  let xml = if pos = `At then xml @ [DeleteCurrentFocus] else xml in
  let xml = if pos = `At || pos = `In then [Highlight xml] else xml in
  [Focus (focus, xml)]

let rec xml_s = function
  | `Return np -> Kwd "Give" :: Kwd "me" :: xml_np np
  | `ThereIs np -> Kwd "There" :: Kwd "is" :: xml_np np
  | `Truth (np,vp) -> Kwd "It" :: Kwd "is" :: Kwd "true" :: Kwd "that" :: xml_np np @ xml_vp vp
  | `Focus (foc,s) -> xml_focus foc (xml_s s)
and xml_np = function
  | `Void -> []
  | `PN (w,rel) -> Word w :: xml_rel rel
  | `Ref (np_label,rel) -> xml_np_label np_label @ xml_rel rel
  | `Qu (qu,adj,ng) -> xml_qu qu (xml_adj adj @ xml_ng ng)
  | `QuAggreg (susp, qu,adj,ngg,ng) -> xml_qu qu (xml_suspended susp (xml_adj adj @ xml_ng_aggreg ngg) @ xml_ng ng)
  | `QuOneOf (qu,lw) -> xml_qu qu (Kwd "of" :: Enum (", ", List.map (fun w -> [Word w]) lw) :: [])
  | `And ar -> xml_and (Array.map xml_np ar)
  | `Or (isusp,ar) -> xml_or isusp (Array.map xml_np ar)
  | `Maybe (susp,np) -> xml_maybe susp (xml_np np)
  | `Not (susp,np) -> xml_not susp (xml_np np)
  | `Focus (foc,np) -> xml_focus foc (xml_np np)
and xml_ng = function
  | `That (w,rel) -> Word w :: xml_rel rel
  | `Focus (foc,ng) -> xml_focus foc (xml_ng ng)
and xml_qu qu xml =
  match xml with
    | Word `Thing :: xml_rem ->
      ( match qu with
	| `A -> Kwd "something" :: xml_rem
	| `Any susp -> xml_suspended susp [Word (`Op "anything")] @ xml_rem
	| `The -> Kwd "the" :: xml
	| `All -> Kwd "everything" :: xml_rem
	| `One -> Kwd "one" :: xml
	| `No susp -> xml_suspended susp [Word (`Op "nothing")] @ xml_rem )
    | _ ->
      ( match qu with
	| `A -> xml_a_an xml
	| `Any susp -> xml_suspended susp [Word (`Op "any")] @ xml
	| `The -> Kwd "the" :: xml
	| `All -> Kwd "all" :: xml
	| `One -> Kwd "one" :: xml
	| `No susp -> xml_suspended susp [Word (`Op "no")] @ xml )
and xml_adj = function
  | `Nil -> []
  | `Order w -> [Word w]
  | `Aggreg (susp,adj,w) -> xml_suspended susp (xml_adj adj @ [Word w])
  | `Optional (susp,adj) -> xml_suspended susp [Word (`Op "optional")] @ xml_adj adj
  | `Adj (adj,w) -> xml_adj adj @ [Word w]
and xml_ng_aggreg = function
  | `That (g,rel) -> Word g :: xml_rel rel
  | `ThatOf (g,rel) -> Word g :: xml_rel rel @ [Kwd "of"]
and xml_rel = function
  | `Focus (foc1, `Maybe (susp, `Focus (foc2, `That vp))) -> xml_focus foc1 (Kwd "that" :: xml_vp_mod `Maybe foc1 susp foc2 vp)
  | `Focus (foc1, `Not (susp, `Focus (foc2, `That vp))) -> xml_focus foc1 (Kwd "that" :: xml_vp_mod `Not foc1 susp foc2 vp)
  | `Nil -> []
  | `That vp -> Kwd "that" :: xml_vp vp
  | `Whose (ng,vp) -> Kwd "whose" :: xml_ng ng @ xml_vp vp
  | `Of np -> Kwd "of" :: xml_np np
  | `PP lpp -> xml_pp_list lpp
  | `Ing (w,np) -> Word w :: xml_np np
  | `And ar -> xml_and (Array.map xml_rel ar)
  | `Or (isusp,ar) -> xml_or isusp (Array.map xml_rel ar)
  | `Maybe (susp,rel) -> xml_maybe susp (xml_rel rel)
  | `Not (susp,rel) -> xml_not susp (xml_rel rel)
  | `Ellipsis -> xml_ellipsis
  | `Focus (foc,rel) -> xml_focus foc (xml_rel rel)
and xml_vp = function
  | `Focus (foc1, `Maybe (susp, `Focus (foc2, vp))) -> xml_focus foc1 (xml_vp_mod `Maybe foc1 susp foc2 vp)
  | `Focus (foc1, `Not (susp, `Focus (foc2, vp))) -> xml_focus foc1 (xml_vp_mod `Not foc1 susp foc2 vp) (* negation inversion *)
  | `IsNP (np,lpp) -> Kwd "is" :: xml_np np @ xml_pp_list lpp
  | `IsPP pp -> Kwd "is" :: xml_pp pp
  | `HasProp (p,np,lpp) -> Kwd "has" :: Word p :: xml_np np @ xml_pp_list lpp
  | `Has (np,lpp) -> Kwd "has" :: xml_np np @ xml_pp_list lpp
  | `VT (w,np,lpp) -> Word w :: xml_np np @ xml_pp_list lpp
  | `Subject (np,vp) -> xml_np np @ xml_vp vp
  | `And ar -> xml_and (Array.map xml_vp ar)
  | `Or (isusp,ar) -> xml_or isusp (Array.map xml_vp ar)
  | `Maybe (susp,vp) -> xml_maybe susp (xml_vp vp)
  | `Not (susp,vp) -> xml_not susp (xml_vp vp)
  | `Ellipsis -> xml_ellipsis
  | `Focus (foc,vp) -> xml_focus foc (xml_vp vp)
and xml_vp_mod (op_mod : [`Not | `Maybe]) foc_mod susp_mod foc_vp vp =
  let f_xml_mod = match op_mod with `Maybe -> xml_maybe | `Not -> xml_not in
  let xml_mod = xml_focus (focus_down foc_mod) (f_xml_mod susp_mod []) in
  match op_mod, vp with
    | (`Not | `Maybe), `IsNP (np,lpp) -> xml_focus foc_vp (Kwd "is" :: xml_mod @ xml_np np @ xml_pp_list lpp)
    | (`Not | `Maybe), `IsPP pp -> xml_focus foc_vp (Kwd "is" :: xml_mod @ xml_pp pp)
    | `Not, `HasProp (p,np,lpp) -> xml_focus foc_vp (Kwd "has" :: xml_mod @ Word p :: xml_np np @ xml_pp_list lpp)
    | `Not, `Has (np,lpp) -> xml_focus foc_vp (Kwd "has" :: xml_mod @ xml_np np @ xml_pp_list lpp)
    | _, vp -> xml_mod @ xml_focus foc_vp (xml_vp vp)
and xml_pp_list lpp =
  List.concat (List.map xml_pp lpp)
and xml_pp = function
  | `Prep (prep,np) -> Word prep :: xml_np np
  | `PrepBin (prep1,np1,prep2,np2) -> Word prep1 :: xml_np np1 @ Word prep2 :: xml_np np2


let xml_incr_coordinate focus xml =
  match focus with
    | AtS1 _ -> xml
    | AtP1 (IsThere, _) -> xml
    | _ -> Kwd "and" :: xml

let xml_incr lexicon (focus : focus) = function
  | IncrTerm t ->
    let xml_t = [Word (word_of_term t)] in
    ( match focus with
      | AtS1 (Det (Term t0, _), _) when t0 = t -> xml_t @ [DeleteIncr]
      | AtS1 _ -> xml_t
      | _ ->
	xml_incr_coordinate focus
	  (Kwd "that" :: Kwd "is" :: xml_t) )
  | IncrId id ->
    let xml_id = xml_np_label (lexicon#get_id_label id) in
    ( match focus with
      | AtS1 _ -> xml_id
      | _ ->
	xml_incr_coordinate focus
	  (Kwd "that" :: Kwd "is" :: xml_id) )
  | IncrType c ->
    let xml_c = [Word (word_of_class c)] in
    ( match focus with
      | AtS1 (Det (An (_, _, Class c0), _), _) when c0 = c ->
	xml_a_an xml_c @ [DeleteIncr]
      | AtS1 _ -> xml_a_an xml_c
      | _ ->
	xml_incr_coordinate focus
	  (Kwd "that" :: Kwd "is" :: xml_a_an xml_c) )
  | IncrRel (p,Lisql.Fwd) ->
    xml_incr_coordinate focus
      (Kwd "that" ::
       let word, synt = word_syntagm_of_property p in
       match synt with
	 | Noun -> Kwd "has" :: xml_a_an [Word word]
	 | InvNoun -> Kwd "is" :: Kwd "the" :: Word word :: Kwd "of" :: xml_ellipsis
	 | TransVerb -> Word word :: xml_ellipsis
	 | TransAdj -> Kwd "is" :: Word word :: xml_ellipsis)
  | IncrRel (p,Lisql.Bwd) ->
    xml_incr_coordinate focus
      (Kwd "that" ::
       let word, synt = word_syntagm_of_property p in
       match synt with
	 | Noun -> Kwd "is" :: Kwd "the" :: Word word :: Kwd "of" :: xml_ellipsis
	 | InvNoun -> Kwd "has" :: xml_a_an [Word word]
	 | TransVerb -> xml_ellipsis @ Word word :: []
	 | TransAdj -> xml_ellipsis @ Kwd "is" :: Word word :: [])
  | IncrTriple (S | O as arg) ->
    xml_incr_coordinate focus
      (Kwd "that" :: Kwd "has" :: Kwd "a" :: Word `Relation :: (if arg = S then Kwd "to" :: xml_ellipsis else Kwd "from" :: xml_ellipsis))
  | IncrTriple P ->
    xml_incr_coordinate focus
      (Kwd "that" :: Kwd "is" :: Kwd "a" :: Word `Relation :: Kwd "from" :: xml_ellipsis @ Kwd "to" :: xml_ellipsis)
  | IncrTriplify -> [Kwd "has"; Kwd "a"; Word `Relation; Kwd "from/to"]
  | IncrIs -> xml_incr_coordinate focus (Kwd "that" :: Kwd "is" :: xml_ellipsis)
  | IncrAnd -> Kwd "and" :: xml_ellipsis
  | IncrOr -> Word (`Op "or") :: xml_ellipsis
  | IncrMaybe -> xml_maybe false [Word dummy_word]
  | IncrNot -> xml_not false [Word dummy_word]
  | IncrUnselect -> xml_np (head_of_modif ~suspended:false dummy_word top_rel (Unselect,Unordered))
  | IncrAggreg g -> xml_np (np_of_elt_s1_AnAggreg ~suspended:false Lisql.factory#top_modif g top_rel dummy_ng)
  | IncrOrder order -> xml_np (head_of_modif ~suspended:false dummy_word top_rel (Select,order))


