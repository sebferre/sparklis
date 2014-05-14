
open Jsutils
open Lisql

(* NL generation from focus *)

type word =
  [ `Thing
  | `Class of Rdf.uri
  | `Prop of Rdf.uri
  | `Relation
  | `Op of string
  | `Term of Rdf.term
  | `Literal of string
  | `Id of id
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

(* verbalization of URIs and ids *)

(*
let label_of_uri uri =
  let uri = Js.to_string (Js.decodeURI (Js.string uri)) in
  let s =
    match Regexp.search (Regexp.regexp "[^/#]+$") uri 0 with
      | Some (_,res) ->
	( match Regexp.matched_string res with "" -> uri | name -> name )
      | None -> uri in
  escapeHTML s
*)

let labels_of_uri uri = (* for variable names *)
  match Regexp.search (Regexp.regexp "[A-Za-z0-9_]+$") uri 0 with
    | Some (i,res) -> [Regexp.matched_string res]
    | None -> []

class lexicon =
object (self)
  method labels_uri (uri : Rdf.uri) : string list = labels_of_uri uri

  val mutable prefix_cpt = []
  method private new_label prefix =
    let k =
      try
	let cpt = List.assoc prefix prefix_cpt in
	prefix_cpt <- (prefix,cpt+1)::List.remove_assoc prefix prefix_cpt;
	cpt+1
      with Not_found ->
	prefix_cpt <- (prefix,1)::prefix_cpt;
	1 in
    let l = prefix ^ (if k=1 && prefix<>"" then "" else string_of_int k) in
    l

  val mutable id_label_rev_list : (id * string) list = []

  method set_id_labels (id : id) (labels : string list) : unit =
    let labels = list_to_set labels in (* removing duplicates *)
    let labels = if labels = [] then ["thing"] else labels in (* default label *)
    let labels = List.map self#new_label labels in (* numbering duplicates *)
    id_label_rev_list <- (id, List.hd labels)::id_label_rev_list

  method get_id_label (id : id) : string =
    List.assoc id id_label_rev_list

  method get_label_id (l : string) : id =
    list_rev_assoc l id_label_rev_list

  method id_label_list = List.rev id_label_rev_list

end

let labels_of_arg0 = function P -> ["relation"] | S | O -> []
let labels_of_arg1 = function S -> ["relation"] | P | O -> []
let labels_of_arg2 = function O -> ["relation"] | S | P -> []

let rec labels_elt_p1 lex : elt_p1 -> string list = function
  | Is np -> labels_elt_s1 lex ~labels:[] np
  | Type c -> lex#labels_uri c
  | Has (p,np) -> let _ = labels_elt_s1 lex ~labels:(lex#labels_uri p) np in []
  | IsOf (p,np) -> let _ = labels_elt_s1 lex ~labels:[] np in lex#labels_uri p
  | Triple (arg,np1,np2) ->
    let _ = labels_elt_s1 lex ~labels:(labels_of_arg1 arg) np1 in
    let _ = labels_elt_s1 lex ~labels:(labels_of_arg2 arg) np2 in
    labels_of_arg0 arg
  | Search c -> []
  | Filter c -> []
  | And ar ->
    let ar_labels = Array.map (fun f -> labels_elt_p1 lex f) ar in
    List.concat (Array.to_list ar_labels)
  | Or ar -> []
  | Maybe f -> []
  | Not f -> []
  | IsThere -> []
and labels_elt_s1 lex ~labels : elt_s1 -> string list = function
  | Det (An (id, modif, head), rel_opt) ->
    let l_head = match head with Thing -> [] | Class c -> lex#labels_uri c in
    let l_rel_opt = match rel_opt with None -> [] | Some rel -> labels_elt_p1 lex rel in
    let labels = l_head @ labels @ l_rel_opt in
    lex#set_id_labels id labels;
    labels
  | Det (_,rel_opt) ->
    let l_rel_opt = match rel_opt with None -> [] | Some rel -> labels_elt_p1 lex rel in
    labels @ l_rel_opt
  | NAnd ar -> Array.iter (fun f -> ignore (labels_elt_s1 lex ~labels f)) ar; []
  | NOr ar -> Array.iter (fun f -> ignore (labels_elt_s1 lex ~labels f)) ar; []
  | NMaybe f -> ignore (labels_elt_s1 lex ~labels f); []
  | NNot f -> ignore (labels_elt_s1 lex ~labels f); []
and labels_elt_s lex : elt_s -> unit = function
  | Return np -> ignore (labels_elt_s1 lex ~labels:["result"] np)

let lexicon_of_focus focus : lexicon =
  let lex = new lexicon in
  labels_elt_s lex (elt_s_of_focus focus);
  lex

(* verbalization of focus *)

let np_of_word w = `NoFocus, `PN (w, top_rel)
let np_of_literal l = np_of_word (`Literal l)

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

let vp_of_elt_p1_Is (np : np) = `IsNP (np, [])
let vp_of_elt_p1_Type (c : Rdf.uri) = `IsNP ((`NoFocus, `Qu (`A, `Nil, `Class c, top_rel)), [])
let vp_of_elt_p1_Has (p : Rdf.uri) (np : np) = `HasProp (`Prop p, np, [])
let vp_of_elt_p1_IsOf (p : Rdf.uri) (np : np) = `IsNP ((`NoFocus, `Qu (`The, `Nil, `Prop p, (`NoFocus, `Of np))), [])
let vp_of_elt_p1_Triple (arg : arg) (np1 : np) (np2 : np) =
  match arg with
    | S -> (* has relation npp to npo / has property npp with value npo / has p npo *)
      `HasProp (`Relation, np1, [`Prep (`Op "to", np2)])
    | O -> (* has relation npp from nps / is the value of npp of nps / is the p of nps *)
      `HasProp (`Relation, np2, [`Prep (`Op "from", np1)])
    | P -> (* is a relation from nps to npo / is a property of nps with value npo *)
      `IsNP ((`NoFocus, `Qu (`A, `Nil, `Relation, top_rel)), [`Prep (`Op "from", np1); `Prep (`Op "to", np2)])

let rec vp_of_elt_p1 pos ctx f : vp =
  let nl =
    match f with
      | IsThere -> `IsThere
      | Is np -> vp_of_elt_p1_Is (np_of_elt_s1 (focus_pos_down pos) (IsX ctx) np)
      | Type c -> vp_of_elt_p1_Type c
      | Has (p,np) -> vp_of_elt_p1_Has p (np_of_elt_s1 (focus_pos_down pos) (HasX (p,ctx)) np)
      | IsOf (p,np) -> vp_of_elt_p1_IsOf p (np_of_elt_s1 (focus_pos_down pos) (IsOfX (p,ctx)) np)
      | Triple (arg,np1,np2) ->
	vp_of_elt_p1_Triple arg
	  (np_of_elt_s1 (focus_pos_down pos) (TripleX1 (arg,np2,ctx)) np1)
	  (np_of_elt_s1 (focus_pos_down pos) (TripleX2 (arg,np1,ctx)) np2)
      | Search c -> vp_of_constr c
      | Filter c -> vp_of_constr c
      | And ar -> `And (Array.mapi (fun i elt -> vp_of_elt_p1 (focus_pos_down pos) (AndX (i,ar,ctx)) elt) ar)
      | Or ar -> `Or (None, Array.mapi (fun i elt -> vp_of_elt_p1 (focus_pos_down pos) (OrX (i,ar,ctx)) elt) ar)
      | Maybe elt -> `Maybe (false, vp_of_elt_p1 (focus_pos_down pos) (MaybeX ctx) elt)
      | Not elt -> `Not (false, vp_of_elt_p1 (focus_pos_down pos) (NotX ctx) elt) in
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
and np_of_elt_s1 pos ctx f : np =
  let foc = `Focus (AtS1 (f,ctx),pos) in
  match f with
    | Det (det, None) -> det_of_elt_s2 foc top_rel det
    | Det (det, Some rel) ->
      let foc_rel, nl_rel = vp_of_elt_p1 (focus_pos_down pos) (DetThatX (det,ctx)) rel in
      det_of_elt_s2 foc (foc_rel, `That (`NoFocus, nl_rel)) det
    | NAnd ar -> foc, `And (Array.mapi (fun i elt -> np_of_elt_s1 (focus_pos_down pos) (NAndX (i,ar,ctx)) elt) ar)
    | NOr ar -> foc, `Or (None, Array.mapi (fun i elt -> np_of_elt_s1 (focus_pos_down pos) (NOrX (i,ar,ctx)) elt) ar)
    | NMaybe elt -> foc, `Maybe (false, np_of_elt_s1 (focus_pos_down pos) (NMaybeX ctx) elt)
    | NNot elt -> foc, `Not (false, np_of_elt_s1 (focus_pos_down pos) (NNotX ctx) elt)
and det_of_elt_s2 foc rel : elt_s2 -> np = function
  | Term t -> foc, `PN (`Term t, rel)
  | An (id, modif, head) -> head_of_modif foc (match head with Thing -> `Thing | Class c -> `Class c) rel modif
  | The id -> foc, `Qu (`The, `Nil, `Id id, top_rel)
and s_of_elt_s pos : elt_s -> s = function
  | Return np -> `Focus (AtS (Return np), pos), `Return (np_of_elt_s1 (focus_pos_down pos) ReturnX np)

let rec s_of_ctx_p1 f (foc,nl as foc_nl) ctx : s =
  match ctx with
    | DetThatX (det,ctx2) ->
      let f2 = Det (det, Some f) in
      let nl2 = det_of_elt_s2 (`Focus (AtS1 (f2,ctx2), `Out)) (foc, `That (`NoFocus, nl)) det in
      s_of_ctx_s1 f2 nl2 ctx2
    | AndX (i,ar,ctx2) ->
      let f2 = ar.(i) <- f; And ar in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 =
	`And (Array.mapi
		(fun j elt -> if j=i then foc_nl else vp_of_elt_p1 `Out (AndX (j,ar,ctx2)) elt)
		ar) in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
    | OrX (i,ar,ctx2) ->
      ar.(i) <- f;
      let f2 = Or ar in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Ex) in
      let nl2 =
	`Or (Some i,
	     Array.mapi
	       (fun j elt -> if j=i then foc_nl else vp_of_elt_p1 `Ex (OrX (j,ar,ctx2)) elt)
	       ar) in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
   | MaybeX ctx2 ->
      let f2 = Maybe f in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Ex) in
      let nl2 = `Maybe (true, foc_nl) in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
   | NotX ctx2 ->
      let f2 = Not f in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Ex) in
      let nl2 = `Not (true, foc_nl) in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
and s_of_ctx_s1 f (foc,nl as foc_nl) ctx =
  match ctx with
    | IsX ctx2 ->
      let f2 = Is f in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Is foc_nl in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
    | HasX (p,ctx2) ->
      let f2 = Has (p,f) in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Has p foc_nl in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
    | IsOfX (p,ctx2) ->
      let f2 = IsOf (p,f) in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_IsOf p foc_nl in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
    | TripleX1 (arg,np2,ctx2) ->
      let f2 = Triple (arg,f,np2) in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Triple arg foc_nl (np_of_elt_s1 `Out (TripleX2 (arg,f,ctx2)) np2) in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
    | TripleX2 (arg,np1,ctx2) ->
      let f2 = Triple (arg,np1,f) in
      let foc2 = `Focus (AtP1 (f2,ctx2), `Out) in
      let nl2 = vp_of_elt_p1_Triple arg (np_of_elt_s1 `Out (TripleX1 (arg,f,ctx2)) np1) foc_nl in
      s_of_ctx_p1 f2 (foc2,nl2) ctx2
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
		(fun j elt -> if j=i then foc_nl else np_of_elt_s1 `Out (NAndX (j,ar,ctx2)) elt)
		ar) in
      s_of_ctx_s1 f2 (foc2,nl2) ctx2
    | NOrX (i,ar,ctx2) ->
      ar.(i) <- f;
      let f2 = NOr ar in
      let foc2 = `Focus (AtS1 (f2,ctx2), `Ex) in
      let nl2 =
	`Or (Some i,
	     Array.mapi
	       (fun j elt -> if j=i then foc_nl else np_of_elt_s1 `Ex (NOrX (j,ar,ctx2)) elt)
	       ar) in
      s_of_ctx_s1 f2 (foc2,nl2) ctx2
   | NMaybeX ctx2 ->
      let f2 = NMaybe f in
      let foc2 = `Focus (AtS1 (f2,ctx2), `Ex) in
      let nl2 = `Maybe (true, foc_nl) in
      s_of_ctx_s1 f2 (foc2,nl2) ctx2
   | NNotX ctx2 ->
      let f2 = NNot f in
      let foc2 = `Focus (AtS1 (f2,ctx2), `Ex) in
      let nl2 = `Not (true, foc_nl) in
      s_of_ctx_s1 f2 (foc2,nl2) ctx2

let s_of_focus : focus -> s = function
  | AtP1 (f,ctx) -> s_of_ctx_p1 f (vp_of_elt_p1 `At ctx f) ctx
  | AtS1 (f,ctx) -> s_of_ctx_s1 f (np_of_elt_s1 `At ctx f) ctx
  | AtS f -> s_of_elt_s `Out f
