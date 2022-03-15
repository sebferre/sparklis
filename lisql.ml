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

open Common
  
(* LISQL representations *)

(* LISQL constraints *)

type filter_type = OnlyIRIs | OnlyLiterals | Mixed
let js_filter_type_map : filter_type Jsutils.js_map =
  Jsutils.js_map
    (`Enum [| "OnlyIRIs"; "OnlyLiterals"; "Mixed" |])

type search =
  | WikidataSearch of string list
  | TextQuery of string list
let js_search_map : search Jsutils.js_map =
  Jsutils.js_map
    (`Sum ([| |],
           [| "WikidataSearch", [| "kwds", `List `String |];
              "TextQuery", [| "kwds", `List `String |];
           |]))

type constr =
  | True
  | MatchesAll of string list
  | MatchesAny of string list
  | IsExactly of string
  | StartsWith of string
  | EndsWith of string
  | After of string
  | Before of string
  | FromTo of string * string
  | HigherThan of string
  | LowerThan of string
  | Between of string * string
  | HasLang of string
  | HasDatatype of string
  | ExternalSearch of search * Rdf.term list option (* search service and query, results (None means no constraint, Some lt means one of lt *)

let js_constr_map : constr Jsutils.js_map =
  let open Jsutils in
  js_map
    (`Sum ([| "True" |],
           [| "MatchesAll", [| "kwds", `List `String |];
              "MatchesAny", [| "kwds", `List `String |];
              "IsExactly", [| "kwd", `String |];
              "StartsWith", [| "kwd", `String |];
              "EndsWith", [| "kwd", `String |];
              "After", [| "kwd", `String |];
              "Before", [| "kwd", `String |];
              "FromTo", [| "kwdFrom", `String; "kwdTo", `String |];
              "HigherThan", [| "value", `String |];
              "LowerThan", [| "value", `String |];
              "Between", [| "valueFrom", `String; "valueTo", `String |];
              "HasLang", [| "lang", `String |];
              "HasDatatype", [| "datatype", `String |];
              "ExternalSearch", [| "searchQuery", js_custom_spec js_search_map;
                                   "resultTerms", `Option (`List (js_custom_spec Rdf.js_term_map)) |]
           |]))

let constr_filter_type : constr -> filter_type = function
  | True -> Mixed
  | MatchesAll _
  | MatchesAny _
  | IsExactly _
  | StartsWith _
  | EndsWith _ -> Mixed
  | After _
  | Before _
  | FromTo _
  | HigherThan _
  | LowerThan _
  | Between _
  | HasLang _
  | HasDatatype _ -> OnlyLiterals
  | ExternalSearch _ -> OnlyIRIs
					
let reset_search = function
  | WikidataSearch _ -> WikidataSearch ["..."]
  | TextQuery _ -> TextQuery ["..."]
				
let reset_constr : constr -> constr = function
  | True -> True
  | MatchesAll _ -> MatchesAll ["..."; "..."]
  | MatchesAny _ -> MatchesAny ["..."; "..."]
  | IsExactly _ -> IsExactly "..."
  | StartsWith _ -> StartsWith "..."
  | EndsWith _ -> EndsWith "..."
  | After _ -> After "..."
  | Before _ -> Before "..."
  | FromTo _ -> FromTo ("...","...")
  | HigherThan _ -> HigherThan "..."
  | LowerThan _ -> LowerThan "..."
  | Between _ -> Between ("...","...")
  | HasLang _ -> HasLang "..."
  | HasDatatype _ -> HasDatatype "..."
  | ExternalSearch (s, _) -> ExternalSearch (reset_search s, None)

(* LISQL modifiers *)

type num_conv_type = IntegerConv | DecimalConv | DoubleConv
type num_conv = num_conv_type * bool (* [bool] indicates whether 'str()' must be applied before the numeric converter *)
let js_num_conv_map : num_conv Jsutils.js_map =
  Jsutils.js_map (`Record [| "targetType", `Enum [| "Integer"; "Decimal"; "Double" |];
                             "forgetOriginalDatatype", `Bool |])
(*let _ = Jsutils.js_map_log "num_conv:" js_num_conv_map [(IntegerConv,false); (DoubleConv,true)] (* TEST *) *)

type id = int
        
type arg = S | P | O | Q of Rdf.uri (* qualifier *)
let js_arg_map : arg Jsutils.js_map =
  Jsutils.js_map
    (`Sum ([| "S"; "P"; "O" |],
           [| "Q", [| "uri", `String |] |]))
(* let _ = Jsutils.js_map_log "arg:" js_arg_map [S; Q "http://example.org/q"] (* TEST *) *)
                          
type project = Unselect | Select
                        
type order = Unordered | Highest of num_conv option | Lowest of num_conv option
let js_order_map : order Jsutils.js_map =
  let open Jsutils in
  js_map
    (`Sum ([| "null" |],
           [| "DESC", [| "conv", `Option (js_custom_spec js_num_conv_map) |];
              "ASC", [| "conv", `Option (js_custom_spec js_num_conv_map) |] |]))
                                                              
type modif_s2 = project * order
let js_modif_s2_map : modif_s2 Jsutils.js_map =
  let open Jsutils in
  js_map (`Record [| "select", `Bool; (* Unselect = 0 = false, Select = 1 = true *)
                     "order", js_custom_spec js_order_map |])
              
type orientation = Fwd | Bwd
let js_orientation_map : orientation Jsutils.js_map =
  Jsutils.js_map (`Enum [| "Fwd"; "Bwd" |])
                       
type inverse = bool
type modif_p2 = orientation
              
type pred = (* E = Event, S = Subject, O = Object *)
  | Class of Rdf.uri
  | Prop of Rdf.uri
  | SO of Rdf.uri * Rdf.uri (* properties: E -> S, E -> O *)
  | EO of Rdf.uri * Rdf.uri (* properties: S -> E, E -> O *)
let js_pred_map : pred Jsutils.js_map =
  Jsutils.js_map
    (`Sum ([| |],
           [| "Class", [| "uri", `String |];
              "Prop", [| "uri", `String |];
              "SO", [| "uriS", `String; "uriO", `String |];
              "EO", [| "uriE", `String; "uriO", `String |] |]))
        
type latlong = CustomLatLong of Rdf.uri * Rdf.uri | WikidataLatLong
let js_latlong_map : latlong Jsutils.js_map =
  Jsutils.js_map
    (`Sum ([| "WikidataGeolocation" |],
           [| "LatLong", [| "uriLat", `String; "uriLong", `String |] |]))
(* let _ = Jsutils.js_map_log "latlong:" js_latlong_map [WikidataLatLong; CustomLatLong ("http://lat", "http://long")] (* TEST *) *)
             
type aggreg =
  | NumberOf
  | ListOf (* TODO: add an explicit separator *)
  | Sample
  | Total of num_conv option
  | Average of num_conv option
  | Maximum of num_conv option
  | Minimum of num_conv option
let js_aggreg_map : aggreg Jsutils.js_map =
  Jsutils.(js_map
    (`Sum ([| "COUNT_DISTINCT"; "LIST"; "SAMPLE" |],
           [|  "SUM", [| "conv", `Option (js_custom_spec js_num_conv_map) |];
               "AVG", [| "conv", `Option (js_custom_spec js_num_conv_map) |];
               "MAX", [| "conv", `Option (js_custom_spec js_num_conv_map) |];
               "MIN", [| "conv", `Option (js_custom_spec js_num_conv_map) |] |])))
             
type func =
  | Str
  | Lang | Datatype
  | IRI | STRDT | STRLANG
  | Strlen | Substr2 | Substr3 | Strbefore | Strafter
  | Concat | UCase | LCase | Encode_for_URI | Replace
  | Integer | Decimal | Double | Indicator
  | Add | Sub | Mul | Div | Neg
  | Abs | Round | Ceil | Floor | Random2 (* from some range *)
  | Date | Time
  | Year | Month | Day | Hours | Minutes | Seconds
  | TODAY | NOW
  | And | Or | Not
  | EQ | NEQ | GT | GEQ | LT | LEQ
  | BOUND | IF
  | IsIRI | IsBlank | IsLiteral | IsNumeric
  | StrStarts | StrEnds | Contains | LangMatches | REGEX | REGEX_i (* case insensitive *)
(* missing: timezone, hash functions, BNODE *)
let js_func_map : func Jsutils.js_map =
  Jsutils.js_map
    (`Enum
       [| "Str";
          "Lang"; "Datatype";
          "IRI"; "STRDT"; "STRLANG";
          "Strlen"; "Substr2"; "Substr3"; "Strbefore"; "Strafter";
          "Concat"; "UCase"; "LCase"; "Encode_for_URI"; "Replace";
          "Integer"; "Decimal"; "Double"; "Indicator";
          "Add"; "Sub"; "Mul"; "Div"; "Neg";
          "Abs"; "Round"; "Ceil"; "Floor"; "Random2";
          "Date"; "Time";
          "Year"; "Month"; "Day"; "Hours"; "Minutes"; "Seconds";
          "TODAY"; "NOW";
          "And"; "Or"; "Not";
          "EQ"; "NEQ"; "GT"; "GEQ"; "LT"; "LEQ";
          "BOUND"; "IF";
          "IsIRI"; "IsBlank"; "IsLiteral"; "IsNumeric";
          "StrStarts"; "StrEnds"; "Contains"; "LangMatches"; "REGEX"; "REGEX_i" |])

(* LISQL elts : 'a param is for element annotations (hook) *)
type 'a elt_p1 =
  | Is of 'a * 'a elt_s1
  | Pred of 'a * arg * pred * 'a elt_sn
  | Type of 'a * Rdf.uri
  | Rel of 'a * Rdf.uri * modif_p2 * 'a elt_s1
  | Hier of 'a * id * pred * arg * arg (*Rdf.uri * modif_p2*) * 'a elt_s1
  | Sim of 'a * 'a elt_s1 * pred * arg * arg * int (* rank, positive *)
  | Triple of 'a * arg * 'a elt_s1 * 'a elt_s1 (* abstraction arg + other S1 arguments in order: S, P, O *)
  | LatLong of 'a * latlong * id * id (* specialization of two Rel to get latitude and longitude *)
  | Search of 'a * constr (* `OnlyIRIs *)
  | Filter of 'a * constr * filter_type
  | And of 'a * 'a elt_p1 list
  | Or of 'a * 'a elt_p1 list
  | Maybe of 'a * 'a elt_p1
  | Not of 'a * 'a elt_p1
  | In of 'a * 'a elt_s1 * 'a elt_p1 (* the [elt_s1] should be atomic/Det *)
  | InWhichThereIs of 'a * 'a elt_s1
  | IsThere of 'a
and 'a elt_sn = (* predicate complements *)
  | CNil of 'a
  | CCons of 'a * arg * 'a elt_s1 * 'a elt_sn
  | CAnd of 'a * 'a elt_sn list
  | COr of 'a * 'a elt_sn list
  | CMaybe of 'a * 'a elt_sn
  | CNot of 'a * 'a elt_sn
and 'a elt_s1 =
  | Det of 'a * elt_s2 * 'a elt_p1 option
  | AnAggreg of 'a * id * modif_s2 * aggreg * 'a elt_p1 option * 'a elt_s1 (* aggregation: elt_s1 must be a Det or a AnAggreg *)
  | NAnd of 'a * 'a elt_s1 list
  | NOr of 'a * 'a elt_s1 list
  | NMaybe of 'a * 'a elt_s1
  | NNot of 'a * 'a elt_s1
and elt_s2 =
  | Term of Rdf.term
  | An of id * modif_s2 * elt_head (* existential quantifier *)
  | The of id (* co-reference *)
and elt_head =
  | Thing
  | Class of Rdf.uri
and 'a elt_aggreg =
  (*  | AggregWhere of 'a * id * 'a elt_expr *)
  | ForEachResult of 'a
  | ForEach of 'a * id * modif_s2 * 'a elt_p1 option * id
  | ForTerm of 'a * Rdf.term * id
  | TheAggreg of 'a * id * modif_s2 * aggreg * 'a elt_p1 option * id
and 'a elt_expr =
  | Undef of 'a
  | Const of 'a * Rdf.term
  | Var of 'a * id
  | Apply of 'a * func * (num_conv option * 'a elt_expr) list
  | Choice of 'a * 'a elt_expr list (* non-deterministic choice, enumeration *)
(*and 'a elt_s1_expr =
  | NExpr of 'a * string * id * modif_s2 * 'a elt_expr * 'a elt_p1 option (* string : user label *) *)
and 'a elt_s =
  | Return of 'a * 'a elt_s1
  | SAggreg of 'a * 'a elt_aggreg list
  | SExpr of 'a * string * id * modif_s2 * 'a elt_expr * 'a elt_p1 option (* string : user label *)
  | SFilter of 'a * id * 'a elt_expr (* Boolean expr *)
  | Seq of 'a * 'a elt_s list (* we will avoid unnecessary nestings of Seq, but we keep it for future extensions of elt_s *)

let (js_elt_p1_map : unit elt_p1 Jsutils.js_map),
    (js_elt_sn_map : unit elt_sn Jsutils.js_map),
    (js_elt_s1_map : unit elt_s1 Jsutils.js_map),
    (js_elt_s2_map : elt_s2 Jsutils.js_map),
    (js_elt_aggreg_map : unit elt_aggreg Jsutils.js_map),
    (js_elt_expr_map : unit elt_expr Jsutils.js_map),
    (js_elt_s_map : unit elt_s Jsutils.js_map) =
  let open Jsutils in
  let custom = js_custom_spec in
  let js_annot_map : unit js_map = (* abstract map for ignoring annotations *)
    { spec = `Abstract;
      inject = (fun _ -> Inject.null);
      extract = (fun _ -> ()) } in
  let spec_annot = js_custom_spec js_annot_map in    
  let js_head_map =
    { spec = `Abstract;
      inject = (function Thing -> Inject.null | Class uri -> Inject.string uri);
      extract = (fun js -> match Extract.as_option js with None -> Thing | Some js1 -> Class (Extract.as_string js1)) } in
  let spec_p1 =
    `Sum ([| |],
          [| "Is", [| "annot", spec_annot; "np", `Rec "s1" |];
             "Pred", [| "annot", spec_annot; "arg", custom js_arg_map; "pred", custom js_pred_map; "cp", `Rec "sn" |];
             "Type", [| "annot", spec_annot; "class", `String |];
             "Rel", [| "annot", spec_annot; "property", `String; "orientation", custom js_orientation_map; "np", `Rec "s1" |];
             "Hier", [| "annot", spec_annot; "id", `Int; "pred", custom js_pred_map; "arg1", custom js_arg_map; "arg2", custom js_arg_map; "np", `Rec "s1" |];
             "Sim", [| "annot", spec_annot; "np", `Rec "s1"; "pred", custom js_pred_map; "arg1", custom js_arg_map; "arg2", custom js_arg_map; "rank", `Int |];
             "Triple", [| "annot", spec_annot; "arg", custom js_arg_map; "np1", `Rec "s1"; "np2", `Rec "s2" |];
             "LatLong", [| "annot", spec_annot; "latlong", custom js_latlong_map; "idlat", `Int; "idlong", `Int |];
             "Search", [| "annot", spec_annot; "constr", custom js_constr_map |];
             "Filter", [| "annot", spec_annot; "constr", custom js_constr_map; "filterType", custom js_filter_type_map |];
             "And", [| "annot", spec_annot; "children", `List (`Rec "self") |];
             "Or", [| "annot", spec_annot; "children", `List (`Rec "self") |];
             "Maybe", [| "annot", spec_annot; "child", `Rec "self" |];
             "Not", [| "annot", spec_annot; "child", `Rec "self" |];
             "In", [| "annot", spec_annot; "npg", `Rec "s1"; "child", `Rec "self" |];
             "InWhichThereIs", [| "annot", spec_annot; "np", `Rec "s1" |];
             "IsThere", [| "annot", spec_annot |];
          |]) in
  let spec_sn =
    `Sum ([| |],
          [| "CNil", [| "annot", spec_annot |];
             "CCons", [| "annot", spec_annot; "arg", custom js_arg_map; "np", `Rec "s1"; "cp", `Rec "sn" |];
             "CAnd", [| "annot", spec_annot; "children", `List (`Rec "self") |];
             "COr", [| "annot", spec_annot; "children", `List (`Rec "self") |];
             "CMaybe", [| "annot", spec_annot; "child", `Rec "self" |];
             "CNot", [| "annot", spec_annot; "child", `Rec "self" |];
          |]) in
  let spec_s1 =
    `Sum ([| |],
          [| "Det", [| "annot", spec_annot; "det", `Rec "s2"; "rel", `Option (`Rec "p1") |];
             "AnAggreg", [| "annot", spec_annot; "id", `Int; "modif", custom js_modif_s2_map; "aggreg", custom js_aggreg_map; "rel", `Option (`Rec "p1"); "child", `Rec "self" |];
             "NAnd", [| "annot", spec_annot; "children", `List (`Rec "self") |];
             "NOr", [| "annot", spec_annot; "children", `List (`Rec "self") |];
             "NMaybe", [| "annot", spec_annot; "child", `Rec "self" |];
             "NNot", [| "annot", spec_annot; "child", `Rec "self" |];
          |]) in
  let spec_s2 =
    `Sum ([| |],
          [| "Term", [| "term", custom Rdf.js_term_map |];
             "An", [| "id", `Int; "modif", custom js_modif_s2_map; "class", custom js_head_map |];
             "The", [| "id", `Int |];
          |]) in
  let spec_aggreg =
    `Sum ([| |],
          [| "ForEachResult", [| "annot", spec_annot |];
             "ForEach", [| "annot", spec_annot; "id", `Int; "modif", custom js_modif_s2_map; "rel", `Option (`Rec "p1"); "id2", `Int |];
             "ForTerm", [| "annot", spec_annot; "term", custom Rdf.js_term_map; "id2", `Int |];
             "TheAggreg", [| "annot", spec_annot; "id", `Int; "modif", custom js_modif_s2_map; "aggreg", custom js_aggreg_map; "rel", `Option (`Rec "p1"); "id2", `Int |];
          |]) in
  let spec_expr =
    `Sum ([| |],
          [| "Undef", [| "annot", spec_annot |];
             "Const", [| "annot", spec_annot; "term", custom Rdf.js_term_map |];
             "Var", [| "annot", spec_annot; "id", `Int |];
             "Apply", [| "annot", spec_annot; "func", custom js_func_map; "args", `List (`Record [| "conv", `Option (custom js_num_conv_map); "expr", `Rec "expr" |]) |];
             "Choice", [| "annot", spec_annot; "children", `List (`Rec "self") |];
          |]) in
  let spec_s =
    `Sum ([| |],
          [| "Return", [| "annot", spec_annot; "np", `Rec "s1" |];
             "SAggreg", [| "annot", spec_annot; "items", `List (`Rec "aggreg") |];
             "SExpr", [| "annot", spec_annot; "name", `String; "id", `Int; "modif", custom js_modif_s2_map; "expr", `Rec "expr"; "rel", `Option (`Rec "p1") |];
             "SFilter", [| "annot", spec_annot; "id", `Int; "expr", `Rec "expr" |];
             "Seq", [| "annot", spec_annot; "children", `List (`Rec "self") |];
          |]) in
  let rec_specs =
    [ "p1", spec_p1;
      "sn", spec_sn;
      "s1", spec_s1;
      "s2", spec_s2;
      "aggreg", spec_aggreg;
      "expr", spec_expr;
      "s", spec_s;
    ] in
  js_map ~rec_specs spec_p1,
  js_map ~rec_specs spec_sn,
  js_map ~rec_specs spec_s1,
  js_map ~rec_specs spec_s2,
  js_map ~rec_specs spec_aggreg,
  js_map ~rec_specs spec_expr,
  js_map ~rec_specs spec_s

         
(* list context *)

type 'a ctx_list = 'a list * 'a list

let list_of_ctx (x : 'a) (ll,rr : 'a ctx_list) : 'a list = List.rev ll @ x :: rr

let list_of_list_ctx (lx : 'a list) (ll, rr : 'a ctx_list) : 'a list = List.rev ll @ lx @ rr
								
let ctx_of_list (lr : 'a list) : ('a * 'a ctx_list) list =
  let rec aux ll = function
    | [] -> []
    | x::rr -> (x,(ll,rr)) :: aux (x::ll) rr
  in
  aux [] lr

let ctx_of_ctx_list (x : 'a) (ll,rr : 'a ctx_list) : ('a * 'a ctx_list) ctx_list =
  let rec aux_left rr = function
    | [] -> []
    | x1::ll1 -> (x1, (ll1,rr)) :: aux_left (x1::rr) ll1
  in
  let rec aux_right ll = function
    | [] -> []
    | x1::rr1 -> (x1, (ll,rr1)) :: aux_right (x1::ll) rr1
  in
  aux_left (x::rr) ll, aux_right (x::ll) rr
    
let map_ctx_list (f : 'a -> 'b) (ll,rr : 'a ctx_list) : 'b ctx_list = (List.map f ll, List.map f rr)
    
      
(* LISQL contexts : no annotations in contexts *)
type ctx_p1 =
  | DetThatX of elt_s2 * ctx_s1
  | AnAggregThatX of id * modif_s2 * aggreg * unit elt_s1 * ctx_s1
  | ForEachThatX of id * modif_s2 * id * ctx_aggreg
  | TheAggregThatX of id * modif_s2 * aggreg * id * ctx_aggreg
  | SExprThatX of string * id * modif_s2 * unit elt_expr * ctx_s
  | AndX of unit elt_p1 ctx_list * ctx_p1 (* first list is reverse prefix, second list is suffix *)
  | OrX of unit elt_p1 ctx_list * ctx_p1
  | MaybeX of ctx_p1
  | NotX of ctx_p1
  | InX of unit elt_s1 * ctx_p1
and ctx_sn =
  | PredX of arg * pred * ctx_p1
  | CConsX2 of arg * unit elt_s1 * ctx_sn
  | CAndX of unit elt_sn ctx_list * ctx_sn
  | COrX of unit elt_sn ctx_list * ctx_sn
  | CMaybeX of ctx_sn
  | CNotX of ctx_sn
and ctx_s1 =
  | IsX of ctx_p1
  | CConsX1 of arg * unit elt_sn * ctx_sn
  | RelX of Rdf.uri * modif_p2 * ctx_p1
  | TripleX1 of arg * unit elt_s1 * ctx_p1 (* context on first S1 arg *)
  | TripleX2 of arg * unit elt_s1 * ctx_p1 (* context on second S1 arg *)
  | ReturnX of ctx_s
  | HierX of id * pred * arg * arg * ctx_p1
  | SimX of pred * arg * arg * int * ctx_p1
  | AnAggregX of id * modif_s2 * aggreg * unit elt_p1 option * ctx_s1
  | NAndX of unit elt_s1 ctx_list * ctx_s1
  | NOrX of unit elt_s1 ctx_list * ctx_s1
  | NMaybeX of ctx_s1
  | NNotX of ctx_s1
  | InGraphX of unit elt_p1 * ctx_p1
  | InWhichThereIsX of ctx_p1
and ctx_aggreg =
  | SAggregX of unit elt_aggreg ctx_list * ctx_s
and ctx_expr =
  | ApplyX of func * (num_conv option * unit elt_expr) ctx_list * num_conv option * ctx_expr
  | ChoiceX of unit elt_expr ctx_list * ctx_expr
  | SExprX of string * id * modif_s2 * unit elt_p1 option * ctx_s
  | SFilterX of id * ctx_s
and ctx_s =
  | Root
  | SeqX of unit elt_s ctx_list * ctx_s

(* LISQL focus: no annotations in focus *)
type focus =
  | AtP1 of unit elt_p1 * ctx_p1
  | AtSn of unit elt_sn * ctx_sn
  | AtS1 of unit elt_s1 * ctx_s1
  | AtAggreg of unit elt_aggreg * ctx_aggreg
  | AtExpr of unit elt_expr * ctx_expr
  | AtS of unit elt_s * ctx_s

let factory =
object (self)
  val mutable cpt_id = 0
  method new_id = cpt_id <- cpt_id + 1; cpt_id
  method set n = cpt_id <- n
  method reset = cpt_id <- 0

  method top_p1 = IsThere ()
  method top_modif = (Select, Unordered)
  method top_s2 = let id = self#new_id in An (id, self#top_modif, Thing), id
  method top_s1 = let det, id = self#top_s2 in Det ((), det, None), id
  method top_sn = CNil ()
  method top_expr = Undef ()
  method top_dim = ForEachResult ()
  method top_dim_foreach id2 = let id = self#new_id in ForEach ((), id, self#top_modif, None, id2), id
  method top_s = let np, id = self#top_s1 in Return ((), np), id
  method home_focus = let np, id = self#top_s1 in AtS1 (np, ReturnX Root), [id]
end

  
let is_top_p1 = function IsThere _ -> true | _ -> false
let is_top_p1_opt = function None -> true | Some f -> is_top_p1 f
let is_top_s2 = function An (_, (Select, Unordered), Thing) -> true | _ -> false
let is_top_s1 = function Det (_, det, None) -> is_top_s2 det | _ -> false
let is_top_sn = function CNil _ -> true | _ -> false
let is_top_expr = function Undef _ -> true | _ -> false
let is_top_s = function Return (_, np) -> is_top_s1 np | _ -> false
let is_home_focus = function AtS1 (f, ReturnX Root) -> is_top_s1 f | _ -> false

let is_ForEachResult = function ForEachResult _ -> true | _ -> false
let is_dim = function ForEachResult _ | ForEach _ | ForTerm _ -> true | _ -> false
let is_aggreg = function TheAggreg _ -> true | _ -> false
									    
let is_root_focus = function AtS (_, Root) -> true | _ -> false

let rec is_aggregated_focus = function
  | AtS1 (_, ctx) -> is_aggregated_ctx_s1 ctx
  | _ -> false
and is_aggregated_ctx_s1 = function
  | AnAggregX _ -> true
  | _ -> false

let is_undef_expr_focus = function
  | AtExpr (Undef _, _) -> true
  | _ -> false
    
let rec is_s1_as_p1_focus = function
  | AtS1 (_,ctx) -> is_s1_as_p1_ctx_s1 ctx
  | _ -> false
and is_s1_as_p1_ctx_s1 = function
  | IsX _ -> true
  | CConsX1 _ -> false
  | RelX _ -> false
  | TripleX1 _ -> false
  | TripleX2 _ -> false
  | ReturnX _ -> false
  | HierX _ -> false
  | SimX (_,_,_,_,ctx) -> false
  | AnAggregX _ -> false
  | NAndX (_,ctx) -> is_s1_as_p1_ctx_s1 ctx
  | NOrX (_,ctx) -> is_s1_as_p1_ctx_s1 ctx
  | NMaybeX ctx -> is_s1_as_p1_ctx_s1 ctx
  | NNotX ctx -> is_s1_as_p1_ctx_s1 ctx
  | InGraphX (_,ctx) -> false
  | InWhichThereIsX ctx -> false

let rec is_unconstrained_elt_p1_opt = function
  | None -> true
  | Some rel -> is_unconstrained_elt_p1 rel
and is_unconstrained_elt_p1 = function
  | Is (_,np) -> is_unconstrained_elt_s1_as_p1 np
  | Pred _ -> false
  | Type _ -> false
  | Rel _ -> false
  | Hier _ -> false
  | Sim _ -> false
  | Triple _ -> false
  | LatLong _ -> false
  | Search _ -> false
  | Filter _ -> false
  | And (_,l) -> List.for_all is_unconstrained_elt_p1 l
  | Or (_,l) -> List.for_all is_unconstrained_elt_p1 l
  | Maybe (_,x) -> is_unconstrained_elt_p1 x
  | Not (_,x) -> is_unconstrained_elt_p1 x
  | In (_,npg,x) -> is_unconstrained_elt_p1 x
  | InWhichThereIs _ -> false
  | IsThere _ -> true
and is_unconstrained_elt_s1_as_p1 = function
  | Det (_,det,rel_opt) -> is_unconstrained_elt_s2 det && is_unconstrained_elt_p1_opt rel_opt
  | AnAggreg _ -> false
  | NAnd (_,l) -> List.for_all is_unconstrained_elt_s1_as_p1 l
  | NOr (_,l) -> List.for_all is_unconstrained_elt_s1_as_p1 l
  | NMaybe (_,x) -> is_unconstrained_elt_s1_as_p1 x
  | NNot (_,x) -> is_unconstrained_elt_s1_as_p1 x
and is_unconstrained_elt_s2 = function
  | Term _ -> false
  | An (id,modif,head) -> (match head with Thing -> true | Class _ -> false)
  | The id -> false

let rec is_unconstrained_ctx_s1 = function
  | IsX _ -> false
  | CConsX1 _ -> false
  | RelX _ -> false
  | TripleX1 _ -> false
  | TripleX2 _ -> false
  | ReturnX _ -> true
  | HierX _ -> false
  | SimX _ -> false
  | AnAggregX _ -> false
  | NAndX (ll_rr,ctx) -> is_unconstrained_ctx_s1 ctx
  | NOrX (ll_rr,ctx) -> is_unconstrained_ctx_s1 ctx
  | NMaybeX ctx -> is_unconstrained_ctx_s1 ctx
  | NNotX ctx -> is_unconstrained_ctx_s1 ctx
  | InGraphX (f1,ctx) -> false
  | InWhichThereIsX ctx -> true
and is_unconstrained_ctx_p1 = function
  | DetThatX (det,ctx) ->
    is_unconstrained_elt_s2 det &&
      is_unconstrained_ctx_s1 ctx
  | AnAggregThatX _ -> false
  | ForEachThatX _ -> false
  | TheAggregThatX _ -> false
  | SExprThatX _ -> false
  | AndX ((ll,rr),ctx) ->
    List.for_all is_unconstrained_elt_p1 ll &&
      List.for_all is_unconstrained_elt_p1 rr &&
      is_unconstrained_ctx_p1 ctx
  | OrX ((ll,rr),ctx) -> is_unconstrained_ctx_p1 ctx
  | MaybeX ctx -> is_unconstrained_ctx_p1 ctx
  | NotX ctx -> is_unconstrained_ctx_p1 ctx
  | InX (npg,ctx) -> is_unconstrained_ctx_p1 ctx

let is_unconstrained_det det rel_opt ctx =
  is_unconstrained_elt_s2 det &&
    is_unconstrained_elt_p1_opt rel_opt &&
    is_unconstrained_ctx_s1 ctx
let is_unconstrained_focus_p1 f ctx =
  is_unconstrained_elt_p1 f &&
    is_unconstrained_ctx_p1 ctx

let rec has_left_conjunct_ctx_sn = function
  | CAndX ((ll,rr),ctx) -> ll <> [] || has_left_conjunct_ctx_sn ctx
  | COrX (_,ctx) -> has_left_conjunct_ctx_sn ctx
  | _ -> false
let rec has_left_conjunct_ctx_s1 = function
  | NAndX ((ll,rr),ctx) -> ll <> [] || has_left_conjunct_ctx_s1 ctx
  | NOrX (_,ctx) -> has_left_conjunct_ctx_s1 ctx
  | _ -> false
			    
let rec hierarchy_of_ctx_p1 = function
  | DetThatX (_,ctx) -> hierarchy_of_ctx_s1 ctx
  | AndX (_,ctx) -> hierarchy_of_ctx_p1 ctx
  | OrX (_,ctx) -> hierarchy_of_ctx_p1 ctx
  | MaybeX ctx -> hierarchy_of_ctx_p1 ctx
  | NotX ctx -> hierarchy_of_ctx_p1 ctx
  | _ -> None
and hierarchy_of_ctx_s1 = function
  | IsX _ -> None
  | CConsX1 _ -> None
  | RelX _ -> None
  | TripleX1 _ -> None
  | TripleX2 _ -> None
  | ReturnX _ -> None
  | HierX (id,pred,args,argo,_) -> Some (id,pred,args,argo)
  | SimX (_,_,_,_,ctx) -> None
  | AnAggregX _ -> None
  | NAndX (ll_rr,ctx) -> hierarchy_of_ctx_s1 ctx
  | NOrX (ll_rr,ctx) -> hierarchy_of_ctx_s1 ctx
  | NMaybeX ctx -> hierarchy_of_ctx_s1 ctx
  | NNotX ctx -> hierarchy_of_ctx_s1 ctx
  | InGraphX (f1,ctx) -> None
  | InWhichThereIsX ctx -> None
let hierarchy_of_focus = function
  | AtP1 (f,ctx) -> hierarchy_of_ctx_p1 ctx
  | AtS1 (np,ctx) -> hierarchy_of_ctx_s1 ctx
  | _ -> None
let is_hierarchy_ctx_s1 ctx =
  hierarchy_of_ctx_s1 ctx <> None

let id_of_s2 = function
  | An (id, _, _) -> Some id
  | _ -> None
let id_of_s1 = function
  | Det (_,det,_) -> id_of_s2 det
  | AnAggreg (_,id,_,_,_,_) -> Some id
  | _ -> None
let id_of_sn = function
  | CCons (_,_,np,_) -> id_of_s1 np
  | _ -> None
let id_of_aggreg = function
  | ForEachResult _ -> None
  | ForEach (_,id,_,_,_) -> Some id
  | ForTerm _ -> None
  | TheAggreg (_,id,_,_,_,_) -> Some id
let id_of_s = function
  | SExpr (_,_,id,_,_,_) -> Some id
  | _ -> None
let id_of_focus = function
  | AtP1 (Hier (_,id,_,_,_,_),_) -> Some id
  | AtSn (cp,ctx) -> id_of_sn cp
  | AtS1 (np,ctx) when not (is_s1_as_p1_ctx_s1 ctx) -> id_of_s1 np
  | AtAggreg (aggreg,_) -> id_of_aggreg aggreg
  | AtExpr (_, SExprX (_,id,_,_,_)) -> Some id
  | AtExpr (_, SFilterX (id,_)) -> Some id
  | AtS (s,_) -> id_of_s s
  | _ -> None

let aggregated_id_opt = function
  | AtAggreg (TheAggreg (_,id,_,_,_,id2),_) -> Some id2
  | _ -> None

let inverse_orientation = function
  | Fwd -> Bwd
  | Bwd -> Fwd

let rec last_arg_of_sn : 'a elt_sn -> arg option = function
  | CNil _ -> None
  | CCons (_,arg,np,cp) -> Some arg
  | CAnd (_,lr) -> (try last_arg_of_sn (List.hd (List.rev lr)) with _ -> None)
  | COr (_,lr) -> (try last_arg_of_sn (List.hd (List.rev lr)) with _ -> None)
  | CNot (_,cp) -> last_arg_of_sn cp
  | CMaybe (_,cp) -> last_arg_of_sn cp
	     
(* deprecated
let rec property_range_of_focus = function
  | AtS1 (np,ctx) -> property_range_of_ctx_s1 ctx
  | AtP1 (f,ctx) -> property_range_of_ctx_p1 ctx
  | _ -> None
and property_range_of_ctx_s1 = function
  | RelX (p,ori,ctx) -> Some (p,ori)
  | NAndX (_,ctx)
  | NOrX (_,ctx)
  | NMaybeX ctx
  | NNotX ctx -> property_range_of_ctx_s1 ctx
  | _ -> None
and property_range_of_ctx_p1 = function
  | DetThatX (_,ctx) -> property_range_of_ctx_s1 ctx
  | AndX (_,ctx)
  | OrX (_,ctx)
  | MaybeX ctx
  | NotX ctx -> property_range_of_ctx_p1 ctx
  | _ -> None
 *)
	     
let rec at_sn cp ctx =
  match cp, ctx with
  | CCons (_, arg, NAnd (_,l), cp), _ ->
     at_sn (CAnd ((), List.map (fun np -> CCons ((),arg,np,cp)) l)) ctx
  | CCons (_, arg, NOr (_,l), cp), _ ->
     at_sn (COr ((), List.map (fun np -> CCons ((),arg,np,cp)) l)) ctx
  | CAnd (_,l), CAndX (ll_rr,ctx2) ->
     AtSn (CAnd ((), list_of_list_ctx l ll_rr), ctx2)
  | COr (_,l), COrX (ll_rr,ctx2) ->
     AtSn (COr ((), list_of_list_ctx l ll_rr), ctx2)
  | _ -> AtSn (cp, ctx)
	       
let at_s1 np ctx =
  match np, ctx with
  | _, IsX (DetThatX (det,ctx2)) when is_top_s2 det -> AtS1 (np,ctx2)
  | NAnd (_,l), NAndX (ll_rr,ctx2) ->
     AtS1 (NAnd ((), list_of_list_ctx l ll_rr), ctx2)
  | NOr (_,l), NOrX (ll_rr,ctx2) ->
     AtS1 (NOr ((), list_of_list_ctx l ll_rr), ctx2)
  | _ -> AtS1 (np, ctx)
	       
let at_p1 f ctx =
  match f, ctx with
  | And (_,l), AndX (ll_rr,ctx2) ->
     AtP1 (And ((), list_of_list_ctx l ll_rr), ctx2)
  | Or (_,l), OrX (ll_rr,ctx2) ->
     AtP1 (Or ((), list_of_list_ctx l ll_rr), ctx2)
  | _ -> AtP1 (f, ctx)


(* getting element annotation *)

let rec annot_p1 : 'a elt_p1 -> 'a = function
  | Is (a,np) -> a
  | Pred (a,arg,pred,cp) -> a
  | Type (a,c) -> a
  | Rel (a,p,modif,np) -> a
  | Hier (a,id,pred,args,argo,np) -> a
  | Sim (a,np,pred,arg1,arg2,rank) -> a
  | Triple (a,arg,np1,np2) -> a
  | LatLong (a,ll,id1,id2) -> a
  | Search (a,constr) -> a
  | Filter (a,constr,ft) -> a
  | And (a,lr) -> a
  | Or (a,lr) -> a
  | Maybe (a,f) -> a
  | Not (a,f) -> a
  | In (a,npg,f) -> a
  | InWhichThereIs (a,np) -> a
  | IsThere a -> a
and annot_p1_opt : 'a elt_p1 option -> 'a option = function
  | None -> None
  | Some f -> Some (annot_p1 f)
and annot_sn = function
  | CNil a -> a
  | CCons (a,arg,np,cp) -> a
  | CAnd (a,lr) -> a
  | COr (a,lr) -> a
  | CNot (a,cp) -> a
  | CMaybe (a,cp) -> a
and annot_s1 = function
  | Det (a,det,rel_opt) -> a
  | AnAggreg (a,id,modif,g,rel_opt,np) -> a
  | NAnd (a,lr) -> a
  | NOr (a,lr) -> a
  | NMaybe (a,f) -> a
  | NNot (a,f) -> a
and annot_aggreg = function
  | ForEachResult a -> a
  | ForEach (a,id,modif,rel_opt,id2) -> a
  | ForTerm (a,t,id2) -> a
  | TheAggreg (a,id,modif,g,rel_opt,id2) -> a
and annot_expr = function
  | Undef a -> a
  | Const (a,t) -> a
  | Var (a,id) -> a
  | Apply (a,func,lr) -> a
  | Choice (a,le) -> a
and annot_s = function
  | Return (a,np) -> a
  | SAggreg (a,aggregs) -> a
  | SExpr (a,name,id,modif,expr,rel_opt) -> a
  | SFilter (a,id,expr) -> a
  | Seq (a,lr) -> a


(* conversion between focus and sentence+path *)

type step = DOWN | RIGHT
type path = step list
let js_path_map : path Jsutils.js_map =
  let open Jsutils in
  js_map (`List (`Enum [| "DOWN"; "RIGHT" |]))

let path_of_list_ctx (ll,rr) path =
  List.fold_left
    (fun path _ -> RIGHT::path)
    path ll
		 
let rec elt_s_path_of_ctx_p1 path (f : unit elt_p1) = function
  | DetThatX (det,ctx) -> elt_s_path_of_ctx_s1 (DOWN::path) (Det ((), det, Some f)) ctx
  | AnAggregThatX (id,modif,g,np,ctx) -> elt_s_path_of_ctx_s1 (DOWN::path) (AnAggreg ((), id, modif, g, Some f, np)) ctx
  | ForEachThatX (id,modif,id2,ctx) -> elt_s_path_of_ctx_aggreg (DOWN::path) (ForEach ((), id, modif, Some f, id2)) ctx
  | TheAggregThatX (id,modif,g,id2,ctx) -> elt_s_path_of_ctx_aggreg (DOWN::path) (TheAggreg ((), id, modif, g, Some f, id2)) ctx
  | SExprThatX (name,id,modif,expr,ctx) -> elt_s_path_of_ctx_s (DOWN::RIGHT::path) (SExpr ((), name, id, modif, expr, Some f)) ctx
  | AndX (ll_rr,ctx) -> elt_s_path_of_ctx_p1 (DOWN::path_of_list_ctx ll_rr path) (And ((), list_of_ctx f ll_rr)) ctx
  | OrX (ll_rr,ctx) -> elt_s_path_of_ctx_p1 (DOWN::path_of_list_ctx ll_rr path) (Or ((), list_of_ctx f ll_rr)) ctx
  | MaybeX ctx -> elt_s_path_of_ctx_p1 (DOWN::path) (Maybe ((),f)) ctx
  | NotX ctx -> elt_s_path_of_ctx_p1 (DOWN::path) (Not ((),f)) ctx
  | InX (npg,ctx) -> elt_s_path_of_ctx_p1 (DOWN::RIGHT::path) (In ((),npg,f)) ctx
and elt_s_path_of_ctx_sn path (f : unit elt_sn) = function
  | PredX (arg,pred,ctx) -> elt_s_path_of_ctx_p1 (DOWN::path) (Pred ((),arg,pred,f)) ctx
  | CConsX2 (arg,np,ctx) -> elt_s_path_of_ctx_sn (DOWN::RIGHT::path) (CCons ((),arg,np,f)) ctx
  | CAndX (ll_rr,ctx) -> elt_s_path_of_ctx_sn (DOWN::path_of_list_ctx ll_rr path) (CAnd ((),list_of_ctx f ll_rr)) ctx
  | COrX (ll_rr,ctx) -> elt_s_path_of_ctx_sn (DOWN::path_of_list_ctx ll_rr path) (COr ((),list_of_ctx f ll_rr)) ctx
  | CMaybeX ctx -> elt_s_path_of_ctx_sn (DOWN::path) (CMaybe ((),f)) ctx
  | CNotX ctx -> elt_s_path_of_ctx_sn (DOWN::path) (CNot ((),f)) ctx
and elt_s_path_of_ctx_s1 path (f : unit elt_s1) = function
  | IsX ctx -> elt_s_path_of_ctx_p1 (DOWN::path) (Is ((),f)) ctx
  | CConsX1 (arg,cp,ctx) -> elt_s_path_of_ctx_sn (DOWN::path) (CCons ((),arg,f,cp)) ctx
  | RelX (p,modif,ctx) -> elt_s_path_of_ctx_p1 (DOWN::path) (Rel ((),p,modif,f)) ctx
  | TripleX1 (arg,np,ctx) -> elt_s_path_of_ctx_p1 (DOWN::path) (Triple ((),arg,f,np)) ctx
  | TripleX2 (arg,np,ctx) -> elt_s_path_of_ctx_p1 (DOWN::RIGHT::path) (Triple ((),arg,np,f)) ctx
  | ReturnX ctx -> elt_s_path_of_ctx_s (DOWN::path) (Return ((),f)) ctx
  | HierX (id,pred,args,argo,ctx) -> elt_s_path_of_ctx_p1 (DOWN::path) (Hier ((),id,pred,args,argo,f)) ctx
  | SimX (pred,args,argo,rank,ctx) -> elt_s_path_of_ctx_p1 (DOWN::path) (Sim ((),f,pred,args,argo,rank)) ctx
  | AnAggregX (id,modif,g,rel_opt,ctx) -> elt_s_path_of_ctx_s1 (DOWN::RIGHT::path) (AnAggreg ((),id, modif, g, rel_opt, f)) ctx
  | NAndX (ll_rr,ctx) -> elt_s_path_of_ctx_s1 (DOWN::path_of_list_ctx ll_rr path) (NAnd ((),list_of_ctx f ll_rr)) ctx
  | NOrX (ll_rr,ctx) -> elt_s_path_of_ctx_s1 (DOWN::path_of_list_ctx ll_rr path) (NOr ((),list_of_ctx f ll_rr)) ctx
  | NMaybeX ctx -> elt_s_path_of_ctx_s1 (DOWN::path) (NMaybe ((),f)) ctx
  | NNotX ctx -> elt_s_path_of_ctx_s1 (DOWN::path) (NNot ((),f)) ctx
  | InGraphX (f1,ctx) -> elt_s_path_of_ctx_p1 (DOWN::path) (In ((),f,f1)) ctx
  | InWhichThereIsX ctx -> elt_s_path_of_ctx_p1 (DOWN::path) (InWhichThereIs ((),f)) ctx
and elt_s_path_of_ctx_aggreg path (f : unit elt_aggreg) = function
  | SAggregX (ll_rr,ctx) -> elt_s_path_of_ctx_s (DOWN::path_of_list_ctx ll_rr path) (SAggreg ((), list_of_ctx f ll_rr)) ctx
and elt_s_path_of_ctx_expr path (f : unit elt_expr) = function
  | SExprX (name,id,modif,rel_opt,ctx) -> elt_s_path_of_ctx_s (DOWN::path) (SExpr ((), name, id, modif, f, rel_opt)) ctx
  | SFilterX (id,ctx) -> elt_s_path_of_ctx_s (DOWN::path) (SFilter ((), id, f)) ctx
  | ApplyX (func,ll_rr,conv_opt,ctx) -> elt_s_path_of_ctx_expr (DOWN::path_of_list_ctx ll_rr path) (Apply ((), func, list_of_ctx (conv_opt,f) ll_rr)) ctx
  | ChoiceX (ll_rr,ctx) -> elt_s_path_of_ctx_expr (DOWN::path_of_list_ctx ll_rr path) (Choice ((), list_of_ctx f ll_rr)) ctx
and elt_s_path_of_ctx_s path (f : unit elt_s) = function
  | Root -> (f, path)
  | SeqX (ll_rr,ctx) -> elt_s_path_of_ctx_s (DOWN::path_of_list_ctx ll_rr path) (Seq ((), list_of_ctx f ll_rr)) ctx

let elt_s_path_of_focus : focus -> unit elt_s * path = function
  | AtP1 (f,ctx) -> elt_s_path_of_ctx_p1 [] f ctx
  | AtSn (f,ctx) -> elt_s_path_of_ctx_sn [] f ctx
  | AtS1 (f,ctx) -> elt_s_path_of_ctx_s1 [] f ctx
  | AtAggreg (f,ctx) -> elt_s_path_of_ctx_aggreg [] f ctx
  | AtExpr (f,ctx) -> elt_s_path_of_ctx_expr [] f ctx
  | AtS (f,ctx) -> elt_s_path_of_ctx_s [] f ctx

let elt_s_of_focus foc = fst (elt_s_path_of_focus foc)


let list_focus_of_path_list path lr =
  let rec aux path (ll,rr) x =
    match path, rr with
    | RIGHT::_, [] -> assert false
    | RIGHT::path1, y::rr1 -> aux path1 (x::ll,rr1) y
    | _ -> path, (ll,rr), x
  in
  match lr with
  | [] -> assert false
  | x::rr -> aux path ([],rr) x
			     
let rec focus_of_path_p1 (ctx : ctx_p1) : path * unit elt_p1 -> focus = function
  | [], f -> AtP1 (f,ctx)
  | DOWN::path, Is (_,np) -> focus_of_path_s1 (IsX ctx) (path,np)
  | DOWN::path, Pred (_,arg,pred,cp) -> focus_of_path_sn (PredX (arg,pred,ctx)) (path,cp)
  | DOWN::path, Rel (_,p,m,np) -> focus_of_path_s1 (RelX (p,m,ctx)) (path,np)
  | DOWN::path, Hier (_, id,pred,args,argo,np) -> focus_of_path_s1 (HierX (id,pred,args,argo,ctx)) (path,np)
  | DOWN::path, Sim (_,np,pred,args,argo,rank) -> focus_of_path_s1 (SimX (pred,args,argo,rank,ctx)) (path,np)
  | DOWN::RIGHT::path, Triple (_,arg,np1,np2) -> focus_of_path_s1 (TripleX2 (arg,np1,ctx)) (path,np2)
  | DOWN::path, Triple (_,arg,np1,np2) -> focus_of_path_s1 (TripleX1 (arg,np2,ctx)) (path,np1)
  | DOWN::path, And (_,lr) ->
     let path, ll_rr, x = list_focus_of_path_list path lr in
     focus_of_path_p1 (AndX (ll_rr, ctx)) (path,x)
  | DOWN::path, Or (_,lr) ->
     let path, ll_rr, x = list_focus_of_path_list path lr in
     focus_of_path_p1 (OrX (ll_rr, ctx)) (path,x)
  | DOWN::path, Maybe (_,x) -> focus_of_path_p1 (MaybeX ctx) (path,x)
  | DOWN::path, Not (_,x) -> focus_of_path_p1 (NotX ctx) (path,x)
  | DOWN::RIGHT::path, In (_,npg,x) -> focus_of_path_p1 (InX (npg,ctx)) (path,x)
  | DOWN::path, In (_,npg,x) -> focus_of_path_s1 (InGraphX (x,ctx)) (path,npg)
  | DOWN::path, InWhichThereIs (_,np) -> focus_of_path_s1 (InWhichThereIsX ctx) (path,np)
  | _ -> assert false
and focus_of_path_sn (ctx : ctx_sn) : path * unit elt_sn -> focus = function
  | [], cp -> AtSn (cp,ctx)
  | DOWN::RIGHT::path, CCons (_,arg,np,cp) -> focus_of_path_sn (CConsX2 (arg,np,ctx)) (path,cp)
  | DOWN::path, CCons (_,arg,np,cp) -> focus_of_path_s1 (CConsX1 (arg,cp,ctx)) (path,np)
  | DOWN::path, CAnd (_,lr) ->
     let path, ll_rr, x = list_focus_of_path_list path lr in
     focus_of_path_sn (CAndX (ll_rr, ctx)) (path,x)
  | DOWN::path, COr (_,lr) ->
     let path, ll_rr, x = list_focus_of_path_list path lr in
     focus_of_path_sn (COrX (ll_rr, ctx)) (path,x)
  | DOWN::path, CMaybe (_,x) -> focus_of_path_sn (CMaybeX ctx) (path,x)
  | DOWN::path, CNot (_,x) -> focus_of_path_sn (CNotX ctx) (path,x)
  | _ -> assert false
and focus_of_path_s1 (ctx : ctx_s1) : path * unit elt_s1 -> focus = function
  | [], np -> AtS1 (np,ctx)
  | DOWN::path, Det (_, det, Some rel) -> focus_of_path_p1 (DetThatX (det, ctx)) (path,rel)
  | DOWN::RIGHT::path, AnAggreg (_, id, modif, g, rel_opt, np) -> focus_of_path_s1 (AnAggregX (id,modif,g,rel_opt,ctx)) (path,np)
  | DOWN::path, AnAggreg (_, id, modif, g, Some rel, np) -> focus_of_path_p1 (AnAggregThatX (id, modif, g, np, ctx)) (path,rel)
  | DOWN::path, NAnd (_,lr) ->
     let path, ll_rr, x = list_focus_of_path_list path lr in
     focus_of_path_s1 (NAndX (ll_rr, ctx)) (path,x)
  | DOWN::path, NOr (_,lr) ->
     let path, ll_rr, x = list_focus_of_path_list path lr in
     focus_of_path_s1 (NOrX (ll_rr, ctx)) (path,x)
  | DOWN::path, NMaybe (_,x) -> focus_of_path_s1 (NMaybeX ctx) (path,x)
  | DOWN::path, NNot (_,x) -> focus_of_path_s1 (NNotX ctx) (path,x)
  | _ -> assert false
and focus_of_path_aggreg (ctx : ctx_aggreg) : path * unit elt_aggreg -> focus = function
  | [], aggreg -> AtAggreg (aggreg,ctx)
  | DOWN::path, ForEach (_,id,modif,Some rel,id2) -> focus_of_path_p1 (ForEachThatX (id,modif,id2,ctx)) (path,rel)
  | DOWN::path, TheAggreg (_,id,modif,g,Some rel,id2) -> focus_of_path_p1 (TheAggregThatX (id,modif,g,id2,ctx)) (path,rel)
  | _ -> assert false
and focus_of_path_expr (ctx : ctx_expr) : path * unit elt_expr -> focus = function
  | [], expr -> AtExpr (expr,ctx)
  | DOWN::path, Apply (_,func,args) ->
     let path, ll_rr, (conv_opt,expr) = list_focus_of_path_list path args in
     focus_of_path_expr (ApplyX (func, ll_rr, conv_opt, ctx)) (path,expr)
  | DOWN::path, Choice (_,lr) ->
     let path, ll_rr, expr = list_focus_of_path_list path lr in
     focus_of_path_expr (ChoiceX (ll_rr,ctx)) (path,expr)
  | _ -> assert false
and focus_of_path_s (ctx : ctx_s) : path * unit elt_s -> focus = function
  | [], s -> AtS (s,ctx)
  | DOWN::path, Return (_,np) -> focus_of_path_s1 (ReturnX ctx) (path,np)
  | DOWN::path, SAggreg (_,aggregs) ->
     let path, ll_rr, aggreg = list_focus_of_path_list path aggregs in
     focus_of_path_aggreg (SAggregX (ll_rr,ctx)) (path,aggreg)
  | DOWN::RIGHT::path, SExpr (_,name,id,modif,expr,Some rel) -> focus_of_path_p1 (SExprThatX (name,id,modif,expr,ctx)) (path,rel)
  | DOWN::path, SExpr (_,name,id,modif,expr,rel_opt) -> focus_of_path_expr (SExprX (name,id,modif,rel_opt,ctx)) (path,expr)
  | DOWN::path, SFilter (_,id,expr) -> focus_of_path_expr (SFilterX (id,ctx)) (path,expr)
  | DOWN::path, Seq (_,lr) ->
     let path, ll_rr, x = list_focus_of_path_list path lr in
     focus_of_path_s (SeqX (ll_rr,ctx)) (path,x)
  | _ -> assert false

let focus_of_elt_s_path : unit elt_s * path -> focus =
  fun (s,path) -> focus_of_path_s Root (path,s)

				  
(* focus moves *)

let move_seq move1 move2 = fun focus -> match move1 focus with None -> None | Some focus2 -> move2 focus2
let move_alt move1 move2 = fun focus -> match move1 focus with None -> move2 focus | Some focus2 -> Some focus2
    
let down_p1 (ctx : ctx_p1) : unit elt_p1 -> focus option = function
  | Is (_,np) -> Some (AtS1 (np, IsX ctx))
  | Pred (_,arg,pred,cp) -> Some (AtSn (cp, PredX (arg,pred,ctx)))
  | Type _ -> None
  | Rel (_,p,m,np) -> Some (AtS1 (np, RelX (p,m,ctx)))
  | Hier (_, id,pred,args,argo,np) -> Some (AtS1 (np, HierX (id,pred,args,argo,ctx)))
  | Sim (_,np,pred,args,argo,rank) -> Some (AtS1 (np, SimX (pred,args,argo,rank,ctx)))
  | Triple (_,arg,np1,np2) -> Some (AtS1 (np1, TripleX1 (arg,np2,ctx)))
  | LatLong _ -> None
  | Search _ -> None
  | Filter _ -> None
  | And (_,[]) -> None
  | And (_,x::rr) -> Some (AtP1 (x, AndX (([],rr),ctx)))
  | Or (_,[]) -> None
  | Or (_,x::rr) -> Some (AtP1 (x, OrX (([],rr),ctx)))
  | Maybe (_,elt) -> Some (AtP1 (elt, MaybeX ctx))
  | Not (_,elt) -> Some (AtP1 (elt, NotX ctx))
  | In (_,npg,elt) -> Some (AtP1 (elt, InX (npg,ctx)))
  | InWhichThereIs (_,np) -> Some (AtS1 (np, InWhichThereIsX ctx))
  | IsThere _ -> None
let down_p1_opt (ctx : ctx_p1) : unit elt_p1 option -> focus option = function
  | Some (And (_,x::rr)) -> Some (AtP1 (x, AndX (([],rr), ctx)))
  | Some rel -> Some (AtP1 (rel, ctx))
  | None -> None
let down_sn (ctx : ctx_sn) : unit elt_sn -> focus option = function
  | CNil _ -> None
  | CCons (_,arg,np,cp) -> Some (AtS1 (np, CConsX1 (arg,cp,ctx)))
  | CAnd (_,[]) -> None
  | CAnd (_,x::rr) -> Some (AtSn (x, CAndX (([],rr),ctx)))
  | COr (_,[]) -> None
  | COr (_,x::rr) -> Some (AtSn (x, COrX (([],rr),ctx)))
  | CMaybe (_,elt) -> Some (AtSn (elt, CMaybeX ctx))
  | CNot (_,elt) -> Some (AtSn (elt, CNotX ctx))
let down_s1 (ctx : ctx_s1) : unit elt_s1 -> focus option = function
  | Det (_, det, rel_opt) -> down_p1_opt (DetThatX (det, ctx)) rel_opt
  | AnAggreg (_, id, modif, g, Some rel, np) -> down_p1_opt (AnAggregThatX (id,modif,g,np,ctx)) (Some rel)
  | AnAggreg (_, id, modif, g, None, np) -> Some (AtS1 (np, AnAggregX (id, modif, g, None, ctx)))
  | NAnd (_,[]) -> None
  | NAnd (_,x::rr) -> Some (AtS1 (x, NAndX (([],rr),ctx)))
  | NOr (_,[]) -> None
  | NOr (_,x::rr) -> Some (AtS1 (x, NOrX (([],rr),ctx)))
  | NMaybe (_,elt) -> Some (AtS1 (elt, NMaybeX ctx))
  | NNot (_,elt) -> Some (AtS1 (elt, NNotX ctx))
let down_aggreg (ctx : ctx_aggreg) : unit elt_aggreg -> focus option = function
  | ForEachResult _ -> None
  | ForEach (_,id,modif,rel_opt,id2) -> down_p1_opt (ForEachThatX (id,modif,id2,ctx)) rel_opt
  | ForTerm (_,t,id2) -> None
  | TheAggreg (_,id,modif,g,rel_opt,id2) -> down_p1_opt (TheAggregThatX (id,modif,g,id2,ctx)) rel_opt
let down_expr (ctx : ctx_expr) : unit elt_expr -> focus option = function
  | Undef _ -> None
  | Const _ -> None
  | Var _ -> None
  | Apply (_,func,[]) -> None
  | Apply (_,func,(conv_opt,expr)::args) -> Some (AtExpr (expr, ApplyX (func, ([],args), conv_opt, ctx)))
  | Choice (_,[]) -> None (* should not happen *)
  | Choice (_,x::rr) -> Some (AtExpr (x, ChoiceX (([],rr),ctx)))
let down_s (ctx : ctx_s) : unit elt_s -> focus option = function
  | Return (_,np) -> Some (AtS1 (np,ReturnX ctx))
  | SAggreg (_,[]) -> None
  | SAggreg (_,aggreg::aggregs) -> Some (AtAggreg (aggreg, SAggregX (([],aggregs), ctx)))
  | SExpr (_,name,id,modif,expr,rel_opt) -> Some (AtExpr (expr, SExprX (name,id,modif,rel_opt,ctx)))
  | SFilter (_,id,expr) -> Some (AtExpr (expr, SFilterX (id,ctx)))
  | Seq (_,[]) -> None
  | Seq (_,x::rr) -> Some (AtS (x, SeqX (([],rr),ctx)))
let down_focus = function
  | AtP1 (f,ctx) -> down_p1 ctx f
  | AtSn (f,ctx) -> down_sn ctx f
  | AtS1 (f,ctx) -> down_s1 ctx f
  | AtAggreg (f,ctx) -> down_aggreg ctx f
  | AtExpr (f,ctx) -> down_expr ctx f
  | AtS (f,ctx) -> down_s ctx f

let rec up_p1 f = function
  | DetThatX (det,ctx) -> Some (AtS1 (Det ((), det, Some f), ctx))
  | AnAggregThatX (id, modif, g, np, ctx) -> Some (AtS1 (AnAggreg ((), id, modif, g, Some f, np), ctx))
  | ForEachThatX (id,modif,id2,ctx) -> Some (AtAggreg (ForEach ((), id, modif, Some f, id2), ctx))
  | TheAggregThatX (id,modif,g,id2,ctx) -> Some (AtAggreg (TheAggreg ((), id,modif,g,Some f,id2), ctx))
  | SExprThatX (name,id,modif,expr,ctx) -> Some (AtS (SExpr ((), name, id, modif, expr, Some f), ctx))
  | AndX (ll_rr,ctx) -> up_p1 (And ((), list_of_ctx f ll_rr)) ctx (* Some (AtP1 (And ar, ctx)) *)
  | OrX (ll_rr,ctx) -> Some (AtP1 (Or ((), list_of_ctx f ll_rr), ctx))
  | MaybeX ctx -> Some (AtP1 (Maybe ((), f), ctx))
  | NotX ctx -> Some (AtP1 (Not ((), f), ctx))
  | InX (npg,ctx) -> Some (AtP1 (In ((), npg, f), ctx))
let rec up_sn f = function
  | PredX (arg,pred,ctx) -> Some (AtP1 (Pred ((),arg,pred,f), ctx))
  | CConsX2 (arg,np,ctx) -> Some (AtSn (CCons ((),arg,np,f), ctx))
  | CAndX (ll_rr,ctx) -> up_sn (CAnd ((), list_of_ctx f ll_rr)) ctx
  | COrX (ll_rr,ctx) -> Some (AtSn (COr ((), list_of_ctx f ll_rr), ctx))
  | CMaybeX ctx -> Some (AtSn (CMaybe ((),f), ctx))
  | CNotX ctx -> Some (AtSn (CNot ((),f), ctx))
let rec up_s1 f = function
  | IsX ctx -> Some (AtP1 (Is ((), f), ctx))
  | CConsX1 (arg,cp,ctx) -> Some (AtSn (CCons ((),arg,f,cp), ctx))
  | RelX (p,m,ctx) -> Some (AtP1 (Rel ((),p,m,f), ctx))
  | TripleX1 (arg,np,ctx) -> Some (AtP1 (Triple ((),arg,f,np), ctx))
  | TripleX2 (arg,np,ctx) -> Some (AtP1 (Triple ((),arg,np,f), ctx))
  | ReturnX ctx -> Some (AtS (Return ((),f), ctx))
  | HierX (id,pred,args,argo,ctx) -> Some (AtP1 (Hier ((),id,pred,args,argo,f),ctx))
  | SimX (pred,args,argo,rank,ctx) -> Some (AtP1 (Sim ((),f,pred,args,argo,rank),ctx))
  | AnAggregX (id, modif, g, rel_opt, ctx) -> Some (AtS1 (AnAggreg ((), id, modif, g, rel_opt, f), ctx))
  | NAndX (ll_rr,ctx) -> up_s1 (NAnd ((), list_of_ctx f ll_rr)) ctx
  | NOrX (ll_rr,ctx) -> Some (AtS1 (NOr ((), list_of_ctx f ll_rr), ctx))
  | NMaybeX ctx -> Some (AtS1 (NMaybe ((),f), ctx))
  | NNotX ctx -> Some (AtS1 (NNot ((),f), ctx))
  | InGraphX (f1,ctx) -> Some (AtP1 (In ((),f,f1), ctx))
  | InWhichThereIsX ctx -> Some (AtP1 (InWhichThereIs ((),f), ctx))
let up_aggreg f = function
  | SAggregX (ll_rr,ctx) -> Some (AtS (SAggreg ((), list_of_ctx f ll_rr), ctx))
let up_expr f = function
  | SExprX (name,id,modif,rel_opt,ctx) -> Some (AtS (SExpr ((), name, id, modif, f, rel_opt), ctx))
  | SFilterX (id,ctx) -> Some (AtS (SFilter ((), id, f), ctx))
  | ApplyX (func,ll_rr,conv_opt,ctx) -> Some (AtExpr (Apply ((), func, list_of_ctx (conv_opt,f) ll_rr), ctx))
  | ChoiceX (ll_rr,ctx) -> Some (AtExpr (Choice ((), list_of_ctx f ll_rr), ctx))
let up_s f = function
  | Root -> None
  | SeqX (ll_rr,ctx) -> Some (AtS (Seq ((), list_of_ctx f ll_rr), ctx))
let up_focus = function
  | AtP1 (f,ctx) -> up_p1 f ctx
  | AtSn (f,ctx) -> up_sn f ctx
  | AtS1 (f,ctx) -> up_s1 f ctx
  | AtAggreg (f,ctx) -> up_aggreg f ctx
  | AtExpr (f,ctx) -> up_expr f ctx
  | AtS (f,ctx) -> up_s f ctx

let right_p1 (f : unit elt_p1) : ctx_p1 -> focus option = function
  | DetThatX (det,ctx) -> None
  | AnAggregThatX (id, modif, g, np, ctx) -> Some (AtS1 (np, AnAggregX (id, modif, g, Some f, ctx)))
  | ForEachThatX (id,modif,id2,ctx) -> None
  | TheAggregThatX (id,modif,g,id2,ctx) -> None
  | SExprThatX (name,id,modif,expr,ctx) -> None
  | AndX ((ll,[]),ctx) -> None
  | AndX ((ll,x::rr),ctx) -> Some (AtP1 (x, AndX ((f::ll,rr),ctx)))
  | OrX ((ll,[]),ctx) -> None
  | OrX ((ll,x::rr),ctx) -> Some (AtP1 (x, OrX ((f::ll,rr),ctx)))
  | MaybeX ctx -> None
  | NotX ctx -> None
  | InX (npg,ctx) -> None
let right_sn (f : unit elt_sn) : ctx_sn -> focus option = function
  | PredX _ -> None
  | CConsX2 _ -> None
  | CAndX ((ll,[]),ctx) -> None
  | CAndX ((ll,x::rr),ctx) -> Some (AtSn (x, CAndX ((f::ll,rr),ctx)))
  | COrX ((ll,[]),ctx) -> None
  | COrX ((ll,x::rr),ctx) -> Some (AtSn (x, COrX ((f::ll,rr),ctx)))
  | CMaybeX ctx -> None
  | CNotX ctx -> None
let right_s1 (f : unit elt_s1) : ctx_s1 -> focus option = function
  | IsX _ -> None
  | CConsX1 (arg,cp,ctx) -> Some (AtSn (cp, CConsX2 (arg,f,ctx)))
  | RelX _ -> None
  | TripleX1 (arg,np,ctx) -> Some (AtS1 (np, TripleX2 (arg,f,ctx)))
  | TripleX2 _ -> None
  | ReturnX _ -> None
  | HierX _ -> None
  | SimX _ -> None
  | AnAggregX _ -> None
  | NAndX ((ll,[]),ctx) -> None
  | NAndX ((ll,x::rr),ctx) -> Some (AtS1 (x, NAndX ((f::ll,rr),ctx)))
  | NOrX ((ll,[]),ctx) -> None
  | NOrX ((ll,x::rr),ctx) -> Some (AtS1 (x, NOrX ((f::ll,rr),ctx)))
  | NMaybeX ctx -> None
  | NNotX ctx -> None
  | InGraphX (f1,ctx) -> Some (AtP1 (f1, InX (f, ctx)))
  | InWhichThereIsX ctx -> None
let right_aggreg (f : unit elt_aggreg) : ctx_aggreg -> focus option = function
  | SAggregX ((ll,[]), ctx) -> None
  | SAggregX ((ll,x::rr), ctx) -> Some (AtAggreg (x, SAggregX ((f::ll,rr), ctx)))
let right_expr (f : unit elt_expr) : ctx_expr -> focus option = function
  | SExprX (name,id,modif,None,ctx) -> None
  | SExprX (name,id,modif,Some rel,ctx) -> Some (AtP1 (rel, SExprThatX (name,id,modif,f,ctx)))
  | SFilterX (id,ctx) -> None
  | ApplyX (func,(ll,[]),conv_opt,ctx) -> None
  | ApplyX (func,(ll,(conv_opt_1,f_1)::rr),conv_opt,ctx) -> Some (AtExpr (f_1, ApplyX (func, ((conv_opt,f)::ll,rr), conv_opt_1, ctx)))
  | ChoiceX ((ll,[]),ctx) -> None
  | ChoiceX ((ll,x::rr),ctx) -> Some (AtExpr (x, ChoiceX ((f::ll,rr),ctx)))
let right_s (f : unit elt_s) : ctx_s -> focus option = function
  | Root -> None
  | SeqX ((ll,[]),ctx) -> None
  | SeqX ((ll,x::rr),ctx) -> Some (AtS (x, SeqX ((f::ll,rr),ctx)))
let right_focus = function
  | AtP1 (f,ctx) -> right_p1 f ctx
  | AtSn (f,ctx) -> right_sn f ctx
  | AtS1 (f,ctx) -> right_s1 f ctx
  | AtAggreg (f,ctx) -> right_aggreg f ctx
  | AtExpr (f,ctx) -> right_expr f ctx
  | AtS (f,ctx) -> right_s f ctx

let left_p1 (f : unit elt_p1) : ctx_p1 -> focus option = function
  | DetThatX (det,ctx) -> None
  | AnAggregThatX _ -> None
  | ForEachThatX _ -> None
  | TheAggregThatX _ -> None
  | SExprThatX (name,id,modif,expr,ctx) -> Some (AtExpr (expr, SExprX (name,id, modif, Some f, ctx)))
  | AndX (([],rr),ctx) -> None
  | AndX ((x::ll,rr),ctx) -> Some (AtP1 (x, AndX ((ll,f::rr),ctx)))
  | OrX (([],rr),ctx) -> None
  | OrX ((x::ll,rr),ctx) -> Some (AtP1 (x, OrX ((ll,f::rr),ctx)))
  | MaybeX ctx -> None
  | NotX ctx -> None
  | InX (npg,ctx) -> Some (AtS1 (npg, InGraphX (f,ctx)))
let left_sn (f : unit elt_sn) : ctx_sn -> focus option = function
  | PredX _ -> None
  | CConsX2 (arg,np,ctx) -> Some (AtS1 (np, CConsX1 (arg,f,ctx)))
  | CAndX (([],rr),ctx) -> None
  | CAndX ((x::ll,rr),ctx) -> Some (AtSn (x, CAndX ((ll,f::rr),ctx)))
  | COrX (([],rr),ctx) -> None
  | COrX ((x::ll,rr),ctx) -> Some (AtSn (x, COrX ((ll,f::rr),ctx)))
  | CMaybeX ctx -> None
  | CNotX ctx -> None
let left_s1 (f : unit elt_s1) : ctx_s1 -> focus option = function
  | IsX _ -> None
  | CConsX1 _ -> None
  | RelX _ -> None
  | TripleX1 _ -> None
  | TripleX2 (arg,np,ctx) -> Some (AtS1 (np, TripleX1 (arg,f,ctx)))
  | ReturnX _ -> None
  | HierX _ -> None
  | SimX _ -> None
  | AnAggregX (id, modif, g, None, ctx) -> None
  | AnAggregX (id, modif, g, Some rel, ctx) -> Some (AtP1 (rel, AnAggregThatX (id, modif, g, f, ctx)))
  | NAndX (([],rr),ctx) -> None
  | NAndX ((x::ll,rr),ctx) -> Some (AtS1 (x, NAndX ((ll,f::rr),ctx)))
  | NOrX (([],rr),ctx) -> None
  | NOrX ((x::ll,rr),ctx) -> Some (AtS1 (x, NOrX ((ll,f::rr),ctx)))
  | NMaybeX ctx -> None
  | NNotX ctx -> None
  | InGraphX (f1,ctx) -> None
  | InWhichThereIsX ctx -> None
let left_aggreg (f : unit elt_aggreg) : ctx_aggreg -> focus option = function
  | SAggregX (([],rr),ctx) -> None
  | SAggregX ((x::ll,rr),ctx) -> Some (AtAggreg (x, SAggregX ((ll,f::rr),ctx)))
let left_expr (f : unit elt_expr) : ctx_expr -> focus option = function
  | SExprX (name,id,modif,rel_opt,ctx) -> None
  | SFilterX (id,ctx) -> None
  | ApplyX (func, ([],rr), conv_opt, ctx) -> None
  | ApplyX (func, ((conv_opt_1,f_1)::ll,rr), conv_opt, ctx) -> Some (AtExpr (f_1, ApplyX (func, (ll,(conv_opt,f)::rr), conv_opt_1, ctx)))
  | ChoiceX (([],rr), ctx) -> None
  | ChoiceX ((x::ll,rr), ctx) -> Some (AtExpr (x, ChoiceX ((ll,f::rr), ctx)))
let left_s (f : unit elt_s) : ctx_s -> focus option = function
  | Root -> None
  | SeqX (([],rr),ctx) -> None
  | SeqX ((x::ll,rr),ctx) -> Some (AtS (x, SeqX ((ll,f::rr),ctx)))
let left_focus = function
  | AtP1 (f,ctx) -> left_p1 f ctx
  | AtSn (f,ctx) -> left_sn f ctx
  | AtS1 (f,ctx) -> left_s1 f ctx
  | AtAggreg (f,ctx) -> left_aggreg f ctx
  | AtExpr (f,ctx) -> left_expr f ctx
  | AtS (f,ctx) -> left_s f ctx

(* move to next undef expr if any, or to the context of the whole expr otherwise *)
let rec next_undef_focus focus =
  match focus with
  | AtExpr (expr, ctx) ->
    ( match expr with
    | Undef _ -> Some focus
    | Const _ -> move_seq up_focus next_undef_focus focus
    | Var _ -> move_seq up_focus next_undef_focus focus
    | Apply (_,func,args) ->
      ( try
	  let (conv_opt, x), ll_rr =
	    List.find (* if some argument is Undef *)
	      (function ((_, Undef _), ll_rr) -> true | _ -> false)
	      (ctx_of_list args) in
	  Some (AtExpr (x, ApplyX (func,ll_rr,conv_opt,ctx))) (* set focus on it *)
	with _ -> move_seq up_focus next_undef_focus focus )
    | Choice (_,le) ->
      ( try
	  let x, ll_rr =
	    List.find (* if some expression is Undef *)
	      (function (Undef _, ll_rr) -> true | _ -> false)
	      (ctx_of_list le) in
	  Some (AtExpr (x, ChoiceX (ll_rr,ctx))) (* set focus on it *)
	with _ -> move_seq up_focus next_undef_focus focus ) )
  | AtS (SExpr _,_) -> down_focus focus
  | AtS (SFilter _,_) -> down_focus focus
  | _ -> Some focus


(* going to root expr *)    
let rec root_expr_of_ctx_expr (f : unit elt_expr) : ctx_expr -> unit elt_s * ctx_s = function
  | SExprX (name,id,modif,rel_opt,ctx2) -> SExpr ((),name,id,modif,f,rel_opt), ctx2
  | SFilterX (id,ctx2) -> SFilter ((),id,f), ctx2
  | ApplyX (func,ll_rr,conv_opt,ctx) -> root_expr_of_ctx_expr (Apply ((), func, list_of_ctx (conv_opt,f) ll_rr)) ctx
  | ChoiceX (ll_rr,ctx) -> root_expr_of_ctx_expr (Choice ((), list_of_ctx f ll_rr)) ctx


let rec focus_up_at_root_s1 = function
  | AtS1 (f, CConsX1 (arg2,cp, PredX (arg1,pred,ctx))) -> Some (AtP1 (Pred ((),arg1,pred,CCons ((),arg2,f,cp)), ctx))
  | AtS1 (f, RelX (p, m, ctx)) -> Some (AtP1 (Rel ((),p,m,f), ctx))
  | AtS1 (f, HierX (id,pred,arg1,arg2, DetThatX (det, ctx))) ->
     focus_up_at_root_s1 (AtS1 (Det ((),det, Some (Hier ((),id,pred,arg1,arg2,f))), ctx))
  | AtS1 (f, TripleX1 (arg,np,ctx)) -> Some (AtP1 (Triple ((),arg,f,np), ctx))
  | AtS1 (f, TripleX2 (arg,np,ctx)) -> Some (AtP1 (Triple ((),arg,np,f), ctx))
  | AtS1 (f, InGraphX (f1,ctx)) -> Some (AtP1 (f1, InX (f,ctx)))
  | _ -> None

(* copy *)

type id_map = (id * id) list (* map from old ids to new ids *)
	   
let copy_list (copy : 'a -> 'a * id_map) (lf : 'a list) : 'a list * id_map =
  List.fold_right
    (fun f (lf',map) ->
     let f', m = copy f in
     f'::lf', m @ map)
    lf ([],[])

let rec copy_p1 (f : unit elt_p1) : unit elt_p1 * id_map =
  match f with
  | Is (a,np) ->
     let np', map = copy_s1 np in
     Is (a, np'), map
  | Pred (a,arg,pred,cp) ->
     let cp', map = copy_sn cp in
     Pred (a, arg, pred, cp'), map
  | Type (a,uri) -> Type (a,uri), []
  | Rel (a,uri,modif,np) ->
     let np', map = copy_s1 np in
     Rel (a,uri,modif,np'), map
  | Hier (a,id,pred,args,argo,np) ->
     let id' = factory#new_id in
     let np', map = copy_s1 np in
     Hier (a, id', pred, args, argo, np'), (id,id')::map
  | Sim (a,np,pred,args,argo,rank) ->
     let np', map1 = copy_s1 np in
     Sim (a,np',pred,args,argo,rank), map1
  | Triple (a,arg,np1,np2) ->
     let np1', map1 = copy_s1 np1 in
     let np2', map2 = copy_s1 np2 in
     Triple (a,arg, np1', np2'), map1 @ map2
  | LatLong (a,ll,id1,id2) ->
     let id1' = factory#new_id in
     let id2' = factory#new_id in
     LatLong (a, ll, id1', id2'), (id1,id1')::(id2,id2')::[]
  | Search _ -> f, []
  | Filter _ -> f, []
  | And (a,lr) ->
     let lr', map = copy_list copy_p1 lr in
     And (a, lr'), map
  | Or (a,lr) ->
     let lr', map = copy_list copy_p1 lr in
     Or (a, lr'), map
  | Maybe (a,f1) ->
     let f1', map = copy_p1 f1 in
     Maybe (a, f1'), map
  | Not (a,f1) ->
     let f1', map = copy_p1 f1 in
     Not (a, f1'), map
  | In (a,npg,f1) ->
     let npg', map1 = copy_s1 npg in
     let f1', map2 = copy_p1 f1 in
     In (a, npg', f1'), map1 @ map2
  | InWhichThereIs (a,np) ->
     let np', map = copy_s1 np in
     InWhichThereIs (a, np'), map
  | IsThere _ -> f, []
and copy_p1_opt = function
  | None -> None, []
  | Some f ->
     let f', map = copy_p1 f in
     Some f', map
and copy_sn (cp : unit elt_sn) : unit elt_sn * id_map =
  match cp with
  | CNil a -> CNil a, []
  | CCons (a,arg,np,cp) ->
     let np', map1 = copy_s1 np in
     let cp', map2 = copy_sn cp in
     CCons (a, arg, np', cp'), map1 @ map2
  | CAnd (a,lr) ->
     let lr', map = copy_list copy_sn lr in
     CAnd (a, lr'), map
  | COr (a,lr) ->
     let lr', map = copy_list copy_sn lr in
     COr (a, lr'), map
  | CMaybe (a,cp1) ->
     let cp1', map = copy_sn cp1 in
     CMaybe (a, cp1'), map
  | CNot (a,cp1) ->
     let cp1', map = copy_sn cp1 in
     CNot (a, cp1'), map
and copy_s1 (np : unit elt_s1) : unit elt_s1 * id_map =
  match np with
  | Det (a,det,rel_opt) ->
     let det', map1 = copy_s2 det in
     let rel_opt', map2 = copy_p1_opt rel_opt in
     Det (a, det', rel_opt'), map1 @ map2
  | AnAggreg (a,id,modif,g,rel_opt,np) ->
     let id' = factory#new_id in
     let rel_opt', map1 = copy_p1_opt rel_opt in
     let np', map2 = copy_s1 np in
     AnAggreg (a, id', modif,g, rel_opt', np'), (id,id')::map1@map2
  | NAnd (a,lr) ->
     let lr', map = copy_list copy_s1 lr in
     NAnd (a, lr'), map
  | NOr (a,lr) ->
     let lr', map = copy_list copy_s1 lr in
     NOr (a, lr'), map
  | NMaybe (a,np1) ->
     let np1', map = copy_s1 np1 in
     NMaybe (a, np1'), map
  | NNot (a,np1) ->
     let np1', map = copy_s1 np1 in
     NNot (a, np1'), map
and copy_s2 (det : elt_s2) : elt_s2 * id_map =
  match det with
  | Term _ -> det, []
  | An (id,modif,head) ->
     let id' = factory#new_id in
     An (id', modif, head), (id,id')::[]
  | The _ -> det, []
and copy_aggreg (aggreg : unit elt_aggreg) : unit elt_aggreg * id_map =
  match aggreg with
  | ForEachResult _ -> aggreg, []
  | ForEach (a,id,modif,rel_opt,id2) ->
     let id' = factory#new_id in
     let rel_opt', map = copy_p1_opt rel_opt in
     ForEach (a, id', modif, rel_opt', id2), (id,id')::map
  | ForTerm _ -> aggreg, []
  | TheAggreg (a,id,modif,g,rel_opt,id2) ->
     let id' = factory#new_id in
     let modif' = factory#top_modif in
     TheAggreg (a, id', modif', Sample, None, id2), (id,id')::[]
and copy_expr (expr : unit elt_expr) : unit elt_expr * id_map =
  expr, []
and copy_s (s : unit elt_s) : unit elt_s * id_map =
  match s with
  | Return (a,np) ->
     let np', map = copy_s1 np in
     Return (a, np'), map
  | SAggreg (a,aggregs) ->
     let aggregs', map = copy_list copy_aggreg aggregs in
     SAggreg (a, aggregs'), map
  | SExpr (a,name,id,modif,expr,rel_opt) ->
     let id' = factory#new_id in
     let modif' = factory#top_modif in
     let expr', map1 = copy_expr expr in
     let rel_opt', map2 = copy_p1_opt rel_opt in
     SExpr (a,"", id', modif', expr', rel_opt'), (id,id')::map1@map2
  | SFilter (a,id,expr) ->
     let id' = factory#new_id in
     let expr', map = copy_expr expr in
     SFilter (a, id', expr'), map
  | Seq (a, lr) ->
     let lr', map = copy_list copy_s lr in
     Seq (a, lr'), map


(* deltas *)
		     
type delta_ids = id list
type delta =
  | DeltaNil
  | DeltaIds of delta_ids
  | DeltaDuplicate of id_map
  | DeltaSelection of delta * delta list

let js_delta_map : delta Jsutils.js_map =
  Jsutils.js_map
    (`Sum  ([| "nil" |],
            [| "ids", [| "ids", `List `Int |];
               "duplicate", [| "map", `List (`Tuple [| `Int; `Int |]) |];
               "selection", [| "whole", `Rec "self"; "parts", `List (`Rec "self") |] |]))

  
let delta_ids ids = if ids=[] then DeltaNil else DeltaIds ids
							  
let focus_move (f : focus -> focus option) : focus -> (focus * delta) option =
  fun foc ->
  match f foc with
  | None -> None
  | Some foc2 -> Some (foc2, DeltaNil)
                    
let focus_start ?(delta = DeltaNil) (foc : focus) : focus * delta = foc, delta
									   
let focus_opt_start ?(delta = DeltaNil) (foc_opt : focus option) : (focus * delta) option =
  match foc_opt with
  | None -> None
  | Some foc -> Some (foc, delta)
			    
let rec focus_moves (steps : (focus -> focus option) list) (foc, delta : focus * delta) : focus * delta = (* makes as many steps as possible *)
  match steps with
    | [] -> foc, delta
    | step::others ->
      ( match step foc with
	| None -> foc, delta
	| Some foc' -> focus_moves others (foc',delta) )

let rec focus_opt_moves (steps : (focus -> focus option) list) (foc_delta_opt : (focus * delta) option) : (focus * delta) option = (* makes as many steps as possible *)
  match foc_delta_opt with
  | None -> None
  | Some foc_delta -> Some (focus_moves steps foc_delta)

let home_focus () : focus * delta =
  let foc, ids = factory#home_focus in
  (foc, delta_ids ids)

(* increments *)

type input_type =  IRIInput | StringInput | FloatInput | IntegerInput | DateInput | TimeInput | DateTimeInput | DurationInput (* a sub-type of Sparql.datatype *)
let js_input_type_map : input_type Jsutils.js_map =
  Jsutils.js_map
    (`Enum [| "IRI"; "String"; "Float"; "Integer"; "Date"; "Time"; "DateTime"; "Duration" |])

type selection_op = AndSel | OrSel | NAndSel | NOrSel | AggregSel
let js_selection_op_map : selection_op Jsutils.js_map =
  Jsutils.js_map
    (`Enum [| "And"; "Or"; "NAnd"; "NOr"; "Aggreg" |])
  
type increment =
  | IncrSelection of selection_op * increment list
  | IncrInput of string * input_type
  | IncrTerm of Rdf.term
  | IncrId of id * num_conv option
  | IncrAnything
  | IncrThatIs
  | IncrSomethingThatIs
  | IncrPred of arg * pred
  | IncrArg of Rdf.uri
  | IncrTriple of arg
  | IncrType of Rdf.uri
  | IncrRel of Rdf.uri * modif_p2
  | IncrLatLong of latlong
  | IncrTriplify
  | IncrHierarchy of bool (* trans_rel *)
  (* trans_rel: to indicate that relation in context can be made transitive *)
  | IncrSim of pred * arg * arg (* predicate, source/target roles *)
  | IncrSimRankIncr
  | IncrSimRankDecr
  | IncrAnd
  | IncrDuplicate
  | IncrOr
  | IncrChoice
  | IncrMaybe
  | IncrNot
  | IncrIn
  | IncrInWhichThereIs
  | IncrUnselect
  | IncrOrder of order
  | IncrForeach
  | IncrAggreg of aggreg
  | IncrForeachResult
  | IncrForeachId of id
  | IncrAggregId of aggreg * id
  | IncrFuncArg of bool (* is_pred *) * func * int (* arity *) * int (* arg position, starting at 1 *) * num_conv option (* function result *) * num_conv option (* argument *)
  | IncrName of string
              
let js_increment_map : increment Jsutils.js_map =
  let open Jsutils in
  js_map
    (`Sum
       ([| "IncrAnything";
           "IncrThatIs";
           "IncrSomethingThatIs";
           "IncrTriplify";
           "IncrSimRankIncr";
           "IncrSimRankDecr";
           "IncrAnd";
           "IncrDuplicate";
           "IncrOr";
           "IncrChoice";
           "IncrMaybe";
           "IncrNot";
           "IncrIn";
           "IncrInWhichThereIs";
           "IncrUnselect";
           "IncrForeach";
           "IncrForeachResult"
        |],
        [| "IncrSelection", [| "op", js_custom_spec js_selection_op_map;
                               "items", `List (`Rec "self") |];
           "IncrInput", [| "value", `String;
                           "inputType", js_custom_spec js_input_type_map |];
           "IncrTerm", [| "term", js_custom_spec Rdf.js_term_map |];
           "IncrId", [| "id", `Int;
                        "conv", `Option (js_custom_spec js_num_conv_map) |];
           "IncrPred", [| "arg", js_custom_spec js_arg_map;
                          "pred", js_custom_spec js_pred_map |];
           "IncrArg", [| "uri", `String |];
           "IncrTriple", [| "arg", js_custom_spec js_arg_map |];
           "IncrType", [| "uri", `String |];
           "IncrRel", [| "uri", `String;
                         "orientation", js_custom_spec js_orientation_map |];
           "IncrLatLong", [| "latlong", js_custom_spec js_latlong_map |];
           "IncrHierarchy", [| "transitiveRelInCtx", `Bool |];
           (* trans_rel: to indicate that relation in context can be made transitive *)
           "IncrSim", [| "pred", js_custom_spec js_pred_map;
                           "argS", js_custom_spec js_arg_map;
                           "argO", js_custom_spec js_arg_map |];
           "IncrOrder", [| "order", js_custom_spec js_order_map |];
           "IncrAggreg", [| "aggreg", js_custom_spec js_aggreg_map |];
           "IncrForeachId", [| "id", `Int |];
           "IncrAggregId", [| "aggreg", js_custom_spec js_aggreg_map;
                              "id", `Int |];
           "IncrFuncArg", [| "boolResult", `Bool;
                             "func", js_custom_spec js_func_map;
                             "arity", `Int;
                             "argPos", `Int;
                             "resultConv", `Option (js_custom_spec js_num_conv_map);
                             "argConv", `Option (js_custom_spec js_num_conv_map) |];
           "IncrName", [| "name", `String |]
          |]))
(* let _ = Jsutils.js_map_log "increment:" js_increment_map
          [ IncrRel ("http://dbpedia.org/director", Fwd);
            IncrOr;
            IncrTerm (Rdf.PlainLiteral ("hello","en")) ] (* TEST *) *)

let datatype_of_input_type = function
  | IRIInput -> invalid_arg "datatype_of_input_type: URI has no datatype"
  | StringInput -> Rdf.xsd_string
  | FloatInput -> Rdf.xsd_double
  | IntegerInput -> Rdf.xsd_integer
  | DateInput -> Rdf.xsd_date
  | TimeInput -> Rdf.xsd_time
  | DateTimeInput -> Rdf.xsd_dateTime
  | DurationInput -> Rdf.xsd_duration
let term_of_input s = function
  | IRIInput -> Rdf.URI s
  | typ -> Rdf.TypedLiteral (s, datatype_of_input_type typ)

let rec term_of_increment : increment -> Rdf.term option = function
  | IncrInput (s,dt) -> Some (term_of_input s dt)
  | IncrTerm t -> Some t
  | IncrPred (arg,pred) -> term_of_pred pred
  | IncrArg q -> Some (Rdf.URI q)
  | IncrType c -> Some (Rdf.URI c)
  | IncrRel (p,m) -> Some (Rdf.URI p)
  | _ -> None
and term_of_pred : pred -> Rdf.term option = function
  | Class c -> Some (Rdf.URI c)
  | Prop p -> Some (Rdf.URI p)
  | SO (ps,po) -> Some (Rdf.URI po)
  | EO (pe,po) -> Some (Rdf.URI pe)

let uri_of_increment (incr : increment) : Rdf.uri option =
  match term_of_increment incr with
  | Some (Rdf.URI uri) -> Some uri
  | _ -> None
	      
let latlong_of_increment (incr : increment) : latlong option =
  match incr with
  | IncrPred (S, EO (pe,po)) when pe = Rdf.p_P625 -> Some WikidataLatLong
  | IncrRel (uri,Fwd) ->
     if uri = Rdf.p_P625
     then Some WikidataLatLong
     else
       (try Some (CustomLatLong (uri, List.assoc uri Rdf.lat_long_properties))
	with Not_found -> None)
  | _ -> None

					 

let hierarchy_p1_opt_of_uri (uri : Rdf.uri) : (unit elt_p1 * delta_ids) option =
  let lhp = Ontology.config_hierarchy_inheritance#value#info uri in
  match lhp with
  | [] -> None
  | hp::_ -> (* TODO: what about other properties ? *)
     let idh = factory#new_id in
     let np, id = factory#top_s1 in
     Some (Hier ((), idh, Prop hp, S, O, np), [idh; id])

let hierarchy_s1_of_uri (uri : Rdf.uri) : unit elt_s1 * delta_ids =
  let det, id = factory#top_s2 in
  let fh_opt, ids =
    match hierarchy_p1_opt_of_uri uri with
    | None -> None, []
    | Some (fh, ids) -> Some fh, ids in
  Det ((), det, fh_opt), id::ids
	  
let elt_p1_of_arg_pred (arg : arg) (pred : pred) : unit elt_p1 * delta_ids =
  match pred with
  | Class _ ->
     ( match arg with
       | S -> Pred ((), arg, pred, CNil ()), []
       | _ -> let np, id = factory#top_s1 in
	      Pred ((), arg, pred, CCons ((), S, np, CNil ())), [id] )
  | Prop p
  | SO (_,p)
  | EO (_,p) ->
     ( match arg with
       | S -> let np, ids = hierarchy_s1_of_uri p in
	      Pred ((), S, pred, CCons ((), O, np, CNil ())), ids
       | O -> let np, id = factory#top_s1 in
	      Pred ((), O, pred, CCons ((), S, np, CNil ())), [id]
       | _ ->
	  let np1, id1 = factory#top_s1 in
	  let np2, id2 = factory#top_s1 in
	  Pred ((), arg, pred,
		CCons ((), S, np1,
		       CCons ((), O, np2, CNil ()))),
	  [id1; id2] )
	  
let elt_p1_of_rel (p : Rdf.uri) (m : modif_p2) : unit elt_p1 * delta_ids =
  let np, ids =
    match m with
    | Fwd -> hierarchy_s1_of_uri p
    | Bwd -> let np, id = factory#top_s1 in np, [id]
  in
  Rel ((), p, m, np), ids
  
let elt_p1_of_increment : increment -> (unit elt_p1 * delta_ids) option = function
  | IncrPred (arg,pred) -> Some (elt_p1_of_arg_pred arg pred)
  | IncrType c -> Some (Type ((), c), [])
  | IncrRel (p,m) -> Some (elt_p1_of_rel p m)
  | IncrLatLong ll -> let id1, id2 = factory#new_id, factory#new_id in
		      Some (LatLong ((), ll, id1, id2), [id1; id2])
  | _ -> None
	   
let elt_s2_of_increment : increment -> (elt_s2 * delta_ids) option = function
  | IncrTerm t -> Some (Term t, [])
  | IncrId (id,_) -> Some (The id, [])
  | _ -> None

let elt_s1_of_increment (incr : increment) : (unit elt_s1 * delta_ids) option =
  match elt_s2_of_increment incr with
  | Some (det, ids) -> Some (Det ((), det, None), ids)
  | None -> None
	   
let apply_conv_ctx_expr conv_opt = function
  | ApplyX (func,ll_rr,_,ctx2) -> ApplyX (func,ll_rr,conv_opt,ctx2)
  | ctx -> ctx
    
let append_and_p1 ctx (elt_p1 : unit elt_p1) = function
  | IsThere _ -> Some (at_p1 elt_p1 ctx)
  | And (_,lr) -> Some (at_p1 elt_p1 (AndX ((List.rev lr, []), ctx)))
  | f ->
     let f_ctx =
       match ctx with
       | AndX ((ll,rr), ctx2) -> AndX ((f::ll,rr), ctx2)
       | _ -> AndX (([f], []), ctx) in
     Some (at_p1 elt_p1 f_ctx)
let append_or_p1 ctx (elt_p1 : unit elt_p1) = function
  | IsThere _ -> Some (at_p1 elt_p1 ctx)
  | Or (_,lr) -> Some (at_p1 elt_p1 (OrX ((List.rev lr, []), ctx)))
  | f ->
     let f_ctx =
       match ctx with
       | OrX ((ll,rr), ctx2) -> OrX ((f::ll,rr), ctx2)
       | _ -> OrX (([f], []), ctx) in
     Some (at_p1 elt_p1 f_ctx)

let append_and_sn ctx (elt_sn : unit elt_sn) = function
  | CAnd (_,lr) -> Some (at_sn elt_sn (CAndX ((List.rev lr, []), ctx)))
  | cp ->
     if is_top_sn cp
     then None (* no change *)
     else
       let cp_ctx =
	 match ctx with
	 | CAndX ((ll,rr), ctx2) -> CAndX ((cp::ll,rr), ctx2)
	 | _ -> CAndX (([cp], []), ctx) in
       Some (at_sn elt_sn cp_ctx)
let append_or_sn ctx (elt_sn : unit elt_sn) = function
  | COr (_,lr) -> Some (at_sn elt_sn (COrX ((List.rev lr, []), ctx)))
  | cp ->
     if is_top_sn cp
     then None (* no change *)
     else
       let cp_ctx =
	 match ctx with
	 | COrX ((ll,rr), ctx2) -> COrX ((cp::ll,rr), ctx2)
	 | _ -> COrX (([cp], []), ctx) in
       Some (at_sn elt_sn cp_ctx)

let append_and_s1 ctx (elt_s1 : unit elt_s1) = function
  | NAnd (_,lr) -> Some (at_s1 elt_s1 (NAndX ((List.rev lr, []), ctx)))
  | np ->
     if is_top_s1 np
     then None
     else
       let np_ctx =
	 match ctx with
	 | NAndX ((ll,rr), ctx2) -> NAndX ((np::ll,rr), ctx2)
	 | _ -> NAndX (([np], []), ctx) in
       Some (at_s1 elt_s1 np_ctx)
let append_or_s1 ctx (elt_s1 : unit elt_s1) = function
  | NOr (_,lr) -> Some (at_s1 elt_s1 (NOrX ((List.rev lr, []), ctx)))
  | np ->
     if is_top_s1 np
     then None
     else
       let np_ctx =
	 match ctx with
	 | NOrX ((ll,rr), ctx2) -> NOrX ((np::ll,rr), ctx2)
	 | _ -> NOrX (([np], []), ctx) in
       Some (at_s1 elt_s1 np_ctx)

	     
let append_choice ctx (elt_expr : unit elt_expr) = function
  | Choice (_,lr) -> Some (AtExpr (elt_expr, ChoiceX ((List.rev lr, []), ctx)))
  | e -> Some (AtExpr (elt_expr, ChoiceX (([e], []), ctx)))

let append_seq_s ctx (elt_s : unit elt_s) = function
  | Seq (_,lr) -> Some (AtS (elt_s, SeqX ((List.rev lr, []), ctx)))
  | s -> Some (AtS (elt_s, SeqX (([s], []), ctx)))

let insert_elt_p1_in_rel_opt ctx ~elt_ids elt : unit elt_p1 option -> (focus * delta) option = function
  | None -> Some (AtP1 (elt, ctx), delta_ids elt_ids)
  | Some rel -> focus_opt_start ~delta:(delta_ids elt_ids) (append_and_p1 ctx elt rel)

let rec insert_elt_p1 ?(elt_ids = []) (elt : unit elt_p1) : focus -> (focus * delta) option = function
  | AtP1 (f, ctx) -> focus_opt_start ~delta:(delta_ids elt_ids) (append_and_p1 ctx elt f)
  | AtSn (CCons (_,arg,np,cp), ctx) -> insert_elt_p1 elt ~elt_ids (AtS1 (np, CConsX1 (arg,cp,ctx)))
  | AtSn _ -> None
  | AtS1 (Det (_, det, rel_opt), ctx) -> insert_elt_p1_in_rel_opt ~elt_ids (DetThatX (det,ctx)) elt rel_opt
  | AtS1 (AnAggreg (_, id, modif, g, rel_opt, np), ctx) -> insert_elt_p1_in_rel_opt ~elt_ids (AnAggregThatX (id,modif,g,np,ctx)) elt rel_opt
  | AtS1 _ -> None (* no insertion of increments on complex NPs *)
  | AtAggreg (ForEach (_,id,modif,rel_opt,id2), ctx) -> insert_elt_p1_in_rel_opt ~elt_ids (ForEachThatX (id,modif,id2,ctx)) elt rel_opt
  (*  | AtAggreg (_, SAggregX ([],_,_)) -> None (* HAVING clauses are not allowed without GROUP BY dimensions, unique value anyway *) *)
  | AtAggreg (TheAggreg (_,id,modif,g,rel_opt,id2), ctx) -> insert_elt_p1_in_rel_opt ~elt_ids (TheAggregThatX (id,modif,g,id2,ctx)) elt rel_opt
  | AtAggreg _ -> None
  | AtExpr (expr, SExprX (name,id,modif,rel_opt,ctx)) -> insert_elt_p1_in_rel_opt ~elt_ids (SExprThatX (name,id,modif,expr,ctx)) elt rel_opt
  | AtExpr _ -> None (* no insertion inside expressions *)
  | AtS _ -> None

let rec insert_elt_s1 elt focus : (focus * delta) option =
  let focus2_opt =
    match focus with
    | AtSn (CCons (_,arg,_np,cp), ctx) -> Some (at_sn (CCons ((),arg,elt,CNil ())) ctx, DeltaNil)
    (*       insert_elt_s1 elt (AtS1 (np, CConsX1 (arg,cp,ctx))) *)
    | AtSn _ -> None
    | AtS1 (_,ctx) when is_hierarchy_ctx_s1 ctx -> Some (at_s1 elt ctx, DeltaNil)
    | AtS1 ((Det _ as _np), ctx) -> Some (at_s1 elt ctx, DeltaNil)
       (*if is_top_s1 np
       then Some (at_s1 elt ctx, DeltaNil)
       else insert_elt_p1 (Is ((), elt)) focus *)
    | AtS1 (AnAggreg (_,id,modif,g,_,np), ctx) ->
       Some (AtS1 (AnAggreg ((), id, modif, g, Some (Is ((), elt)), np), ctx), DeltaNil)
    | AtS1 (_,ctx) -> None (* no insertion of NPs on complex NPs *)
    | AtP1 _
    | AtAggreg _ -> insert_elt_p1 (Is ((), elt)) focus
    | _ -> None in
  focus_opt_moves [focus_up_at_root_s1] focus2_opt

let rec insert_elt_s2 det : focus -> (focus * delta) option = function
  | AtSn (CCons (_,arg,np,cp), ctx) -> insert_elt_s2 det (AtS1 (np, CConsX1 (arg,cp,ctx)))
  | AtSn _ -> None
  | AtS1 (Det (_, det0, rel_opt), ctx) ->
     let focus_delta2 =
       if det0 = det (* erasing existing det *)
       then let det, id = factory#top_s2 in (* TODO: handle removed ids *)
	    AtS1 (Det ((), det, rel_opt), ctx), delta_ids [id]
       else AtS1 (Det ((), det, rel_opt), ctx), DeltaNil in
     Some (focus_moves [focus_up_at_root_s1] focus_delta2)
  | focus -> insert_elt_s1 (Det ((), det, None)) focus


let insert_input s typ focus : (focus * delta) option =
  match focus with
  | AtExpr (_,ctx) -> focus_opt_start (next_undef_focus (AtExpr (Const ((), term_of_input s typ), ctx)))
  | _ -> None

let insert_term t focus : (focus * delta) option =
  match t with
    | Rdf.Bnode _ -> None (* blank nodes cannot be injected in queries *)
    | _ ->
      match focus with
      | AtExpr (_,ctx) ->
	 focus_opt_start (next_undef_focus (AtExpr (Const ((),t), ctx)))
      | AtAggreg (ForEach (_,id,modif,rel_opt,id2), ctx) -> (* TODO: handle removed ids *)
	 Some (AtAggreg (ForTerm ((),t,id2), ctx), DeltaNil)
      | _ -> insert_elt_s2 (Term t) focus
let insert_id id conv_opt = function
  | AtExpr (_,ctx) ->
     focus_opt_start (next_undef_focus (AtExpr (Var ((),id), apply_conv_ctx_expr conv_opt ctx)))
  | focus -> insert_elt_s2 (The id) focus

let rec insert_anything focus : (focus * delta) option =
  match focus with
  | AtSn (CCons (_,arg,np,cp), ctx) -> insert_anything (AtS1 (np, CConsX1 (arg,cp,ctx)))
  | AtSn _ -> None
  | _ ->
     let focus_delta2_opt =
       match focus with
       | AtS1 (Det (_, det, rel_opt), ctx) ->
	  let det, delta =
	    if is_top_s2 det
	    then det, DeltaNil
	    else let det, id = factory#top_s2 in
		 det, delta_ids [id] in
	  Some (AtS1 (Det ((), det, rel_opt), ctx), delta)
       | AtS1 _ -> None (* no insertion of terms on complex NPs *)
       | _ -> None in
     focus_opt_moves [focus_up_at_root_s1] focus_delta2_opt
			   
let rec insert_type c = function
  | AtSn (CCons (_,arg,np,cp), ctx) -> insert_type c (AtS1 (np, CConsX1 (arg,cp,ctx)))
  | AtSn _ -> None
  | AtS1 (Det (_,det,rel_opt), ctx) ->
    ( match det with
      | Term _ ->
	 let id = factory#new_id in
	 Some (AtS1 (Det ((), An (id, factory#top_modif, Class c), rel_opt), ctx), delta_ids [id])
      | An (id, modif, Thing) ->
	 let moves, rel_opt, delta =
	   match rel_opt with
	   | Some _ -> [], rel_opt, DeltaNil
	   | None ->
	      ( match hierarchy_p1_opt_of_uri c with
		| Some (fh, ids) -> [down_focus; down_focus], Some fh, delta_ids ids
		| None -> [], None, DeltaNil ) in
	 focus_opt_moves
	   moves
	   (Some (AtS1 (Det ((), An (id, modif, Class c), rel_opt), ctx), delta))
      | An (id, modif, Class c2) when c2 = c ->
	Some (AtS1 (Det ((), An (id, modif, Thing), rel_opt), ctx), DeltaNil)
      | _ ->
	let rel = match rel_opt with None -> IsThere () | Some rel -> rel in
	insert_elt_p1 (Type ((),c)) (AtP1 (rel, DetThatX (det, ctx))) )
  | focus -> insert_elt_p1 (Type ((),c)) focus

let insert_pred arg pred focus =
  let elt, elt_ids = elt_p1_of_arg_pred arg pred in
  let foc_opt = insert_elt_p1 ~elt_ids elt focus in
  focus_opt_moves [down_focus; down_focus; down_focus] foc_opt

let insert_arg (q : Rdf.uri) focus =
  let arg = Q q in
  let np_arg, ids = hierarchy_s1_of_uri q in
  let foc_opt =
    let delta = delta_ids ids in
    match focus with
    | AtP1 (Pred (_,arg0,pred,cp), ctx) ->
       Some (AtS1 (np_arg, CConsX1 (arg, cp, PredX (arg0, pred, ctx))), delta)
    | AtSn (cp,ctx) ->
       Some (AtS1 (np_arg, CConsX1 (arg, cp, ctx)), delta)
    | AtS1 (np, CConsX1 (arg0, cp, ctx)) ->
       Some (AtS1 (np_arg, CConsX1 (arg, cp, CConsX2 (arg0, np, ctx))), delta)
    | _ -> None in
  focus_opt_moves [down_focus; down_focus] foc_opt 
		  
let insert_rel p m focus =
  let elt, elt_ids = elt_p1_of_rel p m in
  let foc_opt = insert_elt_p1 ~elt_ids elt focus in
  focus_opt_moves [down_focus; down_focus; down_focus] foc_opt

let insert_latlong ll focus =
  let id_lat = factory#new_id in
  let id_long = factory#new_id in
  insert_elt_p1 ~elt_ids:[id_lat; id_long] (LatLong ((), ll, id_lat, id_long)) focus
		
let insert_triple arg focus =
  let foc_opt =
    let np1, id1 = factory#top_s1 in
    let np2, id2 = factory#top_s1 in
    insert_elt_p1 ~elt_ids:[id1; id2] (Triple ((), arg, np1, np2)) focus in
  let steps = if arg = S then [down_focus; right_focus] else [down_focus] in
  focus_opt_moves steps foc_opt

let insert_triplify = function
  | AtP1 (Rel (_, p, Fwd, np), ctx) -> Some (AtS1 (Det ((), Term (Rdf.URI p), None), TripleX1 (S, np, ctx)), DeltaNil)
  | AtP1 (Rel (_, p, Bwd, np), ctx) -> Some (AtS1 (Det ((), Term (Rdf.URI p), None), TripleX2 (O, np, ctx)), DeltaNil)
  | AtP1 (Triple (_, S, Det ((), Term (Rdf.URI p), _), np), ctx) -> Some (AtP1 (Rel ((), p, Fwd, np), ctx), DeltaNil)
  | AtP1 (Triple (_, O, np, Det ((), Term (Rdf.URI p), _)), ctx) -> Some (AtP1 (Rel ((), p, Bwd, np), ctx), DeltaNil)
  | _ -> None

let rec toggle_hierarchy trans_rel focus =
  let toggle_hierarchy_on np pred args argo ctx =
    match pred, args, argo with
    | _, S, O
    | _, O, S ->
       if trans_rel && not (is_unconstrained_ctx_p1 ctx)
       then let id = factory#new_id in
	    Some (AtS1 (np, HierX (id,pred,args,argo,ctx)), delta_ids [id])
       else None
    | _ -> None in
  let toggle_hierarchy_off np pred args argo ctx =
    match pred, args, argo with
    | Prop p, S, O -> Some (AtS1 (np, RelX (p, Fwd, ctx)), DeltaNil)
    | Prop p, O, S -> Some (AtS1 (np, RelX (p, Bwd, ctx)), DeltaNil)
    | _ -> Some (AtS1 (np, CConsX1 (argo, CNil (), PredX (args, pred, ctx))), DeltaNil) in
  match focus with
  | AtP1 (Hier (_,id,pred,args,argo,np), ctx) -> (* TODO: removed ids *)
     toggle_hierarchy_off np pred args argo ctx
  | AtS1 (np, HierX (id,pred,args,argo,ctx)) -> (* TODO: removed ids *)
     toggle_hierarchy_off np pred args argo ctx
  | AtS1 (np, RelX (p, ori, ctx)) ->
     let args, argo = match ori with Fwd -> S, O | Bwd -> O, S in
     toggle_hierarchy_on np (Prop p) args argo ctx
  | AtS1 (np, CConsX1 (argo, CNil _, PredX (args, pred, ctx))) ->
     toggle_hierarchy_on np pred args argo ctx
  | AtSn (CCons ((), argo, np, CNil _), PredX (args, pred, ctx)) ->
     toggle_hierarchy_on np pred args argo ctx
  | _ -> None

let insert_sim pred args argo = function
(*  | AtP1 (Sim (_,np,pred0,args0,argo0,rank),ctx) when pred0=pred && args0=args && argo0=argo ->
     Some (AtP1 (Sim ((),np,pred0,args0,argo0,rank+1),ctx), DeltaNil) *)
  | AtS1 (np,SimX (pred0,args0,argo0,rank,ctx)) when pred0=pred && args0=args && argo0=argo ->
     Some (AtS1 (np, SimX (pred0,args0,argo0,rank+1,ctx)), DeltaNil)
  | AtS1 (Det (_,det, Some (Sim (_,np,pred0,args0,argo0,rank))),ctx) when pred0=pred && args0=args && argo0=argo ->
     Some (AtS1 (Det ((),det, Some (Sim ((),np,pred0,args0,argo0,rank+1))),ctx), DeltaNil)
  | AtS1 (np,ctx) ->
     let det, id = factory#top_s2 in
     Some (AtS1 (Det ((), det, Some (Sim ((),np,pred,args,argo,1))),ctx), DeltaIds [id])
  | _ -> None

let change_sim_rank (f : int -> int option) = function
  | AtP1 (Sim (_,np,pred,args,argo,rank),ctx) ->
     ( match f rank with
       | None -> Some (at_s1 np (IsX ctx), DeltaNil)
       | Some rank -> Some (AtP1 (Sim ((),np,pred,args,argo,rank),ctx), DeltaNil) )
  | AtS1 (np,SimX (pred,args,argo,rank,ctx)) ->
     ( match f rank with
       | None -> Some (at_s1 np (IsX ctx), DeltaNil)
       | Some rank -> Some (AtP1 (Sim ((),np,pred,args,argo, rank),ctx), DeltaNil) )
  | AtS1 (Det (_,det, Some (Sim (_,np,pred,args,argo,rank))),ctx) ->
     ( match f rank with
       | None -> Some (at_s1 np ctx, DeltaNil)
       | Some rank -> Some (AtS1 (Det ((),det, Some (Sim ((),np,pred,args,argo,rank))), ctx), DeltaNil) )
  | _ -> None
let incr_sim_rank = change_sim_rank (fun rank -> Some (rank+1))
let decr_sim_rank = change_sim_rank (fun rank -> if rank=1 then None else Some (rank-1))
	  
let insert_constr constr ft focus =
  match focus with
  | AtS1 (f, ReturnX _) when is_top_s1 f ->
     ( match constr with
       | MatchesAll _ | MatchesAny _ | IsExactly _ | StartsWith _ | EndsWith _ | ExternalSearch _ ->
	   insert_elt_p1 (Search ((),constr)) focus
       | _ -> None )
  | _ -> insert_elt_p1 (Filter ((),constr,ft)) focus

let rec insert_that_is = function
  (*  | AtS1 (f, IsX ctx) when is_top_s1 f -> None *)
  | AtSn (CCons (_,arg,np,cp), ctx) -> insert_that_is (AtS1 (np, CConsX1 (arg,cp,ctx)))
  | AtS1 (Det (_, An (id,modif,Class _), None), _) as focus ->
     (*  | focus -> *)
     let np, id = factory#top_s1 in (* TODO: avoid id in s1_as_p1 *)
     let foc_opt = insert_elt_p1 ~elt_ids:[id] (Is ((),np)) focus in
     focus_opt_moves [down_focus] foc_opt
  | _ -> None

(* introduces a NP id when there is none *)
let rec insert_something_that_is = function
  | AtSn (CCons (_,arg,np,cp), ctx) -> insert_something_that_is (AtS1 (np, CConsX1 (arg,cp,ctx)))
  | AtS1 (Det (_, An (id,modif,Thing), Some (Is (_, np))), ctx) ->
     Some (AtS1 (np,ctx), DeltaNil) (* TODO: removed ids *)
  | AtS1 ((NOr _ | NNot _ as np), ctx) ->
     let det, id = factory#top_s2 in
     Some (AtS1 (Det ((), det, Some (Is ((), np))), ctx), delta_ids [id])
  | _ -> None

let rec insert_and = function
  | AtP1 _ -> None (* P1 conjunction is implicit *)
  | AtSn (f,ctx) ->
     let cp, ids =
       match last_arg_of_sn f with
       | None -> factory#top_sn, []
       | Some arg -> let np, id = factory#top_s1 in
		     CCons ((), arg, np, CNil ()), [id] in
     focus_opt_start ~delta:(delta_ids ids)
		     (append_and_sn ctx cp f)
  | AtS1 (f, ReturnX ctx) ->
     let np, id = factory#top_s1 in
     Some (AtS1 (np, ReturnX (SeqX (([Return ((),f)],[]), ctx))), delta_ids [id])
  | AtS1 (f, CConsX1 (arg,cp,ctx)) ->
     insert_and (AtSn (CCons ((), arg, f, cp), ctx))
  | AtS1 (f, ctx) when not (is_s1_as_p1_ctx_s1 ctx && is_top_s1 f) ->
     let np, id = factory#top_s1 in
     focus_opt_start ~delta:(delta_ids [id])
		     (append_and_s1 ctx np f)
  | _ -> None

let rec insert_duplicate = function
  | AtP1 _ -> None (* P1 conjunction is implicit *)
  | AtSn (f, ctx) ->
     let f', map = copy_sn f in
     focus_opt_start ~delta:(DeltaDuplicate map)
		     (append_and_sn ctx f' f)
  | AtS1 (f, ReturnX ctx) -> None (* to avoid Cartesian products *)
  | AtS1 (_, InGraphX _) -> None (* to avoid duplication of focus, and complex focus graphs *)
  | AtS1 (f, CConsX1 (arg,cp,ctx)) ->
     insert_duplicate (AtSn (CCons ((), arg, f, cp), ctx))
  | AtS1 (f, ctx) when not (is_s1_as_p1_ctx_s1 ctx && is_top_s1 f) ->
     let f', map = copy_s1 f in
     focus_opt_start ~delta:(DeltaDuplicate map)
		     (append_and_s1 ctx f' f)
  | AtAggreg ((TheAggreg _ as aggreg), SAggregX ((ll,rr),ctx)) ->
     let aggreg', map = copy_aggreg aggreg in
     Some (AtAggreg (aggreg', SAggregX ((aggreg::ll,rr), ctx)), DeltaDuplicate map)
  | AtS ((SAggreg _ | SExpr _ | SFilter _ as f), SeqX ((ll,rr),ctx)) ->
     let f', map = copy_s f in
     Some (AtS (f', SeqX ((f::ll,rr),ctx)), DeltaDuplicate map)
  | _ -> None

let rec insert_or = function
  | AtP1 (f, ctx) when not (is_top_p1 f) ->
     focus_opt_start (append_or_p1 ctx (IsThere ()) f)
  | AtSn (f, ctx) when not (is_top_sn f) ->
     let cp, ids =
       match last_arg_of_sn f with
       | None -> factory#top_sn, []
       | Some arg -> let np, id = factory#top_s1 in
		     CCons ((), arg, np, CNil ()), [id] in
     focus_opt_start ~delta:(delta_ids ids)
		     (append_or_sn ctx cp f)
  | AtS1 (_, InGraphX _) -> None
  | AtS1 (f, CConsX1 (arg,cp,ctx)) ->
     insert_or (AtSn (CCons ((), arg, f, cp), ctx))
  | AtS1 (f, ctx) when not (is_top_s1 f) ->
     let np, id = factory#top_s1 in
     focus_opt_start ~delta:(delta_ids [id])
		     (append_or_s1 ctx np f)
  | _ -> None

let insert_choice = function
  | AtExpr (f, ChoiceX ((ll,rr),ctx2)) when not (is_top_expr f) ->
     Some (AtExpr (factory#top_expr, ChoiceX ((f::ll,rr),ctx2)), DeltaNil)
  | AtExpr (f, ctx) when not (is_top_expr f) ->
     focus_opt_start (append_choice ctx factory#top_expr f)
  | _ -> None
(*
let insert_choice = function
  | AtExpr (f, ChoiceX ((ll,rr),ctx2)) when not (is_top_expr f) -> Some (AtExpr (factory#top_expr, ChoiceX ((f::ll,rr),ctx2)))
  | AtExpr (Choice (_,lr), ctx) -> Some (AtExpr (factory#top_expr, ChoiceX ((List.rev lr,[]),ctx)))
  | AtExpr (f, (SExprX _ as ctx)) -> Some (AtExpr (factory#top_expr, ChoiceX (([f],[]), ctx)))
  | AtExpr (f,ctx) ->
    let id = factory#new_id in
    let s, ctx2 = root_expr_of_ctx_expr (Var ((),id)) ctx in
    let ll, rr, ctx3 = match ctx2 with Root -> [], [], Root | SeqX ((ll,rr),ctx3) -> ll, rr, ctx3 in
    Some (AtExpr (factory#top_expr,
		  ChoiceX (([f],[]),
			   SExprX ("", id, factory#top_modif, None,
				   SeqX ((ll,s::rr), ctx3)))))
  | _ -> None
*)

let rec insert_maybe = function
  | AtP1 (Maybe (_,f), ctx) -> Some (AtP1 (f,ctx), DeltaNil)
  | AtP1 (_, MaybeX ctx) -> None
  | AtP1 (Not _, ctx) -> None
  | AtP1 (_, NotX ctx) -> None				     
  | AtP1 (f, ctx) when not (is_top_p1 f) -> Some (AtP1 (Maybe ((),f), ctx), DeltaNil)
  (*if is_top_p1 f then Some (AtP1 (f, MaybeX ctx)) else Some (AtP1 (Maybe f, ctx))*)
  | AtSn (CMaybe (_,f), ctx) -> Some (AtSn (f,ctx), DeltaNil)
  | AtSn (_, CMaybeX ctx) -> None
  | AtSn (CNot _, ctx) -> None
  | AtSn (_, CNotX ctx) -> None				     
  | AtSn (f, ctx) when not (is_top_sn f) ->
     let ctx =
       if has_left_conjunct_ctx_sn ctx
       then ctx
       else CAndX (([CNil ()],[]), ctx) in
     Some (AtSn (CMaybe ((),f), ctx), DeltaNil)
  | AtS1 (_, InGraphX _) -> None
  | AtS1 (NMaybe (_,f), ctx) -> Some (AtS1 (f,ctx), DeltaNil)
  | AtS1 (_, NMaybeX ctx) -> None
  | AtS1 (NNot _, ctx) -> None
  | AtS1 (_, NNotX ctx) -> None
  | AtS1 (_, ReturnX _) -> None
  | AtS1 (np, CConsX1 (arg,cp,ctx)) ->
     insert_maybe (AtSn (CCons ((),arg,np,cp),ctx))
  | AtS1 (f, ctx) when not (is_aggregated_ctx_s1 ctx || is_s1_as_p1_ctx_s1 ctx && is_top_s1 f) ->
     Some (AtS1 (NMaybe ((),f), ctx), DeltaNil)
  (*if is_top_s1 f then Some (AtS1 (f, NMaybeX ctx)) else Some (AtS1 (NMaybe f, ctx))*)
  | _ -> None

let rec insert_not = function
  | AtP1 (Not (_,f), ctx) -> Some (AtP1 (f,ctx), DeltaNil)
  | AtP1 (_, NotX ctx) -> None
  | AtP1 (Maybe _, ctx) -> None
  | AtP1 (_, MaybeX ctx) -> None
  | AtP1 (f, ctx) ->
     if is_top_p1 f
     then Some (AtP1 (f, NotX ctx), DeltaNil)
     else Some (AtP1 (Not ((),f), ctx), DeltaNil)
  | AtSn (CNot (_,f), ctx) -> Some (AtSn (f,ctx), DeltaNil)
  | AtSn (_, CNotX ctx) -> None
  | AtSn (CMaybe _, ctx) -> None
  | AtSn (_, CMaybeX ctx) -> None
  | AtSn (f, ctx) ->
     let ctx =
       if has_left_conjunct_ctx_sn ctx
       then ctx
       else CAndX (([CNil ()],[]), ctx) in
     let foc_delta = (AtSn (CNot ((),f), ctx), DeltaNil) in
     if is_top_sn f
     then Some (focus_moves [down_focus] foc_delta)
     else Some foc_delta
  | AtS1 (_, InGraphX _) -> None
  | AtS1 (NNot (_,f), ctx) -> Some (AtS1 (f,ctx), DeltaNil)
  | AtS1 (_, NNotX ctx) -> None
  | AtS1 (NMaybe _, ctx) -> None
  | AtS1 (_, NMaybeX ctx) -> None
  | AtS1 (_, ReturnX ctx) -> None
  | AtS1 (np, CConsX1 (arg,cp,ctx)) ->
     insert_not (AtSn (CCons ((),arg,np,cp),ctx))
  | AtS1 (f, ctx) when not (is_aggregated_ctx_s1 ctx || is_s1_as_p1_ctx_s1 ctx && is_top_s1 f) ->
     let foc_delta = (AtS1 (NNot ((),f), ctx), DeltaNil) in
     if is_top_s1 f
     then Some (focus_moves [down_focus] foc_delta)
     else Some foc_delta
  | _ -> None

let rec insert_in = function
  | AtP1 (f,ctx) ->
     let np, id = factory#top_s1 in
     Some (AtS1 (np, InGraphX (f,ctx)), delta_ids [id])
  | AtS1 (_, InGraphX _) -> None
  | AtS1 (Det (_,det,None), ctx) ->
     let np, id = factory#top_s1 in
     Some (AtS1 (np, InGraphX (IsThere (), DetThatX (det, ctx))), delta_ids [id])
  | AtS1 (Det (_,det,Some rel), ctx) ->
     let np, id = factory#top_s1 in
     Some (AtS1 (np, InGraphX (rel, DetThatX (det, ctx))), delta_ids [id])
  | _ -> None

let insert_in_which_there_is focus =
  let np, id = factory#top_s1 in
  let foc_opt = insert_elt_p1 ~elt_ids:[id] (InWhichThereIs ((), np)) focus in
  focus_opt_moves [down_focus] foc_opt

    
let insert_seq = function
  | AtS (f, SeqX ((ll,rr),ctx2)) ->
     let s, id = factory#top_s in
     Some (AtS (s, SeqX ((f::ll,rr),ctx2)), delta_ids [id])
  | AtS (f, ctx) ->
     let s, id = factory#top_s in
     focus_opt_start ~delta:(delta_ids [id])
		     (append_seq_s ctx s f)
  | _ -> None

let out_of_unselect modif foc =
  match fst modif with
  | Unselect -> up_focus foc (* to enforce hidden column *)
  | Select -> Some foc

let rec insert_modif_transf f = function
  | AtSn (CCons (_,arg,np,cp), ctx) -> insert_modif_transf f (AtS1 (np, CConsX1 (arg,cp,ctx)))
  | AtS1 (Det (_, An (id, modif, head), rel_opt), ctx) when not (is_s1_as_p1_ctx_s1 ctx) ->
    let modif2 = f modif in
    let foc2 = AtS1 (Det ((), An (id, modif2, head), rel_opt), ctx) in
    focus_opt_start (out_of_unselect modif2 foc2)
  | AtS1 (AnAggreg (_, id, modif, g, rel_opt, np), ctx) ->
    let modif2 = f modif in
    let foc2 = AtS1 (AnAggreg ((), id, modif2, g, rel_opt, np), ctx) in
    focus_opt_start (out_of_unselect modif2 foc2)
  | AtAggreg (ForEach (_,id,modif,rel_opt,id2), ctx) ->
    let modif2 = f modif in
    if fst modif2 = Unselect
    then None (* hidding dimensions is not allowed *)
    else Some (AtAggreg (ForEach ((),id,modif2,rel_opt,id2), ctx), DeltaNil)
  | AtAggreg (TheAggreg (_,id,modif,g,rel_opt,id2), ctx) ->
    let modif2 = f modif in
    let foc2 = AtAggreg (TheAggreg ((),id,modif2,g,rel_opt,id2), ctx) in
    focus_opt_start (out_of_unselect modif2 foc2)
  | AtExpr (expr, SExprX (name,id,modif,rel_opt,ctx)) ->
    let modif2 = f modif in
    if fst modif2 = Unselect
    then None (* hidding expressions is not allowed *)
    else Some (AtExpr (expr, SExprX (name,id,modif2,rel_opt,ctx)), DeltaNil)
  | AtS (SExpr (_,name,id,modif,expr,rel_opt),ctx) ->
    let modif2 = f modif in
    if fst modif2 = Unselect
    then None  (* hidding expressions is not allowed *)
    else Some (AtS (SExpr ((), name, id, modif2, expr, rel_opt), ctx), DeltaNil)
  | _ -> None

let insert_foreach = function
  | focus ->
    ( match id_of_focus focus with
    | None -> None
    | Some id2 ->
       let s = elt_s_of_focus focus in
       let id = factory#new_id in
       let aggregs = [ForEach ((), id, factory#top_modif, None, id2)] in
       focus_opt_moves
	 [down_focus]
	 (focus_opt_start
	    ~delta:(delta_ids [id])
	    (append_seq_s Root
			  (SAggreg ((), aggregs))
			  s)) )
    
let insert_aggreg g focus =
  match id_of_focus focus with
  | None -> None
  | Some id2 ->
     let s = elt_s_of_focus focus in
     let id = factory#new_id in
     let aggregs = [TheAggreg ((), id, factory#top_modif, g, None, id2)] in
     focus_opt_moves
       [down_focus]
       (focus_opt_start
	  ~delta:(delta_ids [id])
	  (append_seq_s Root (SAggreg ((), aggregs)) s))
  
let insert_foreach_result = function
  | AtS (SAggreg (_, aggregs), ctx) ->
     if List.exists is_ForEachResult aggregs
     then Some (AtS (SAggreg ((), List.filter (not1 is_ForEachResult) aggregs), ctx), DeltaNil)
     else Some (AtS (SAggreg ((), ForEachResult () :: List.filter (not1 is_dim) aggregs), ctx), DeltaNil)
  | AtAggreg (ForEachResult _, SAggregX ((ll,rr), ctx)) -> Some (AtS (SAggreg ((), List.rev ll @ rr), ctx), DeltaNil)
  | AtAggreg (aggreg, SAggregX ((ll,rr), ctx)) ->
     if List.exists is_ForEachResult ll || List.exists is_ForEachResult rr
     then Some (AtAggreg (aggreg, SAggregX ((List.filter (not1 is_ForEachResult) ll, List.filter (not1 is_ForEachResult) rr), ctx)), DeltaNil)
     else (* remove all dims, and replace by ForEachResult *)
       if is_dim aggreg
       then Some (AtS (SAggreg ((), ForEachResult () :: List.filter (not1 is_dim) (List.rev ll @ rr)), ctx), DeltaNil)
       else Some (AtAggreg (aggreg, SAggregX ((List.filter (not1 is_dim) ll @ [ForEachResult ()], List.filter (not1 is_dim) rr), ctx)), DeltaNil)
  | _ -> None
(*    
  | AtS (SAggreg (_, [ForEachResult _], aggregs), ctx) -> Some (AtS (SAggreg ((), [], aggregs), ctx))
  | AtS (SAggreg (_,_dims,aggregs), ctx) -> Some (AtS (SAggreg ((), [ForEachResult ()], aggregs), ctx))
  | AtDim (ForEachResult _, SAggregForX (_, aggregs, ctx)) -> Some (AtS (SAggreg ((), [], aggregs), ctx))
  | AtDim (_dim, SAggregForX (_, aggregs, ctx)) -> Some (AtS (SAggreg ((), [ForEachResult ()], aggregs), ctx))
  | AtAggreg (aggreg, SAggregX ([ForEachResult _], ll_rr, ctx)) -> Some (AtAggreg (aggreg, SAggregX ([], ll_rr, ctx)))
  | AtAggreg (aggreg, SAggregX (_dims, ll_rr, ctx)) -> Some (AtAggreg (aggreg, SAggregX ([ForEachResult ()], ll_rr, ctx)))
  | _ -> None
 *)
		 
let insert_foreach_id id2 focus =
  let new_dim, id = factory#top_dim_foreach id2 in
  match focus with
  | AtS (SAggreg (_,aggregs), ctx) ->
     let aggregs = List.filter (not1 is_ForEachResult) aggregs in
     let ll_rr = List.rev aggregs, [] in
     Some (AtAggreg (new_dim, SAggregX (ll_rr, ctx)), delta_ids [id])
  | AtAggreg (aggreg, SAggregX ((ll,rr), ctx)) ->
     let ll, rr = List.filter (not1 is_ForEachResult) ll, List.filter (not1 is_ForEachResult) rr in
     let ll_rr = if is_ForEachResult aggreg then ll, rr else aggreg::ll, rr in
     Some (AtAggreg (new_dim, SAggregX (ll_rr, ctx)), delta_ids [id])
  | _ -> None

let insert_aggreg_id g id2 focus =
  match focus with
  | AtS (SAggreg (_,aggregs), ctx) ->
     let id = factory#new_id in
     let new_aggreg = TheAggreg ((), id, factory#top_modif, g, None, id2) in
     Some (AtAggreg (new_aggreg, SAggregX ((List.rev aggregs, []), ctx)), delta_ids [id])
  | AtAggreg (TheAggreg (_,id0,modif0,g0,rel0_opt,id20), ctx) when id20=id2 ->
     (* assuming type-compatibility of g over g0's values *)
     let can_be_replaced, with_same_id =
       match g0, g with
       | Sample, _ -> true, false
       | NumberOf, Sample -> true, false
       | ListOf, (Sample | NumberOf) -> true, false
       | (Total _ | Average _), (Sample | ListOf) -> true, false
       | (Total _ | Average _), (NumberOf | Total _ | Average _ | Maximum _ | Minimum _) -> true, true
       | (Maximum _ | Minimum _), (Sample | ListOf) -> true, false
       | (Maximum _ | Minimum _), (NumberOf | Maximum _ | Minimum _) -> true, true
       | _ -> false, false in
     if can_be_replaced && g <> g0
     then
       let id, modif, delta =
	 if with_same_id
	 then id0, modif0, DeltaNil
	 else let id = factory#new_id in
	      id, factory#top_modif, delta_ids [id] in
       Some (AtAggreg (TheAggreg ((),id,modif,g,None,id2), ctx), delta)
     else None
  | AtAggreg (aggreg, SAggregX ((ll,rr), ctx)) ->
     let id = factory#new_id in
     let new_aggreg = TheAggreg ((), id, factory#top_modif, g, None, id2) in
     Some (AtAggreg (new_aggreg, SAggregX ((aggreg::ll,rr), ctx)), delta_ids [id])
  | _ -> None

let insert_func_arg is_pred func arity pos res_conv_opt arg_conv_opt =
  let ll_rr =
    List.map (fun _ -> None, factory#top_expr) (Common.from_downto (pos-1) 1),
    List.map (fun _ -> None, factory#top_expr) (Common.from_to (pos+1) arity) in
  function
  | AtExpr (expr,ctx) ->
    let ctx =
      match ctx with
      | SExprX (name,id,modif,rel_opt,ctx2) ->
	if is_pred
	then SFilterX (id, ctx2)
	else ctx
      | SFilterX (id,ctx2) ->
	if is_pred
	then ctx
	else SExprX ("", id, factory#top_modif, None, ctx2)
      | _ -> apply_conv_ctx_expr res_conv_opt ctx in
    let args =
      if arity = 0
      then []
      else list_of_ctx (arg_conv_opt,expr) ll_rr in
    focus_opt_start (next_undef_focus (AtExpr (Apply ((), func, args), ctx)))
  | focus ->
    ( match id_of_focus focus with
    | None -> None
    | Some id ->
      let s = elt_s_of_focus focus in
      let args = if arity = 0 then [] else list_of_ctx (arg_conv_opt, Var ((),id)) ll_rr in
      let s2 =
	let expr = Apply ((), func, args) in
	if is_pred
	then SFilter ((), factory#new_id, expr)
	else SExpr ((), "", factory#new_id, factory#top_modif, expr, None) in
      let focus2_opt = append_seq_s Root s2 s in
      focus_opt_moves [move_seq down_focus next_undef_focus]
		      (focus_opt_start focus2_opt) )

let insert_name new_name = function
  | AtS (SExpr (_,name,id,modif,expr,rel_opt), ctx) ->
     Some (AtS (SExpr ((), new_name, id, modif, expr, rel_opt), ctx), DeltaNil)
  | AtExpr (expr, SExprX (name,id,modif,rel_opt,ctx)) ->
     Some (AtExpr (expr, SExprX (new_name, id, modif, rel_opt, ctx)), DeltaNil)
  | AtExpr (_, SFilterX _) -> None
  | AtExpr (f,ctx) ->
    let id = factory#new_id in
    let s, ctx2 = root_expr_of_ctx_expr (Var ((),id)) ctx in
    let ll, rr, ctx3 = match ctx2 with Root -> [], [], Root | SeqX ((ll,rr),ctx3) -> ll, rr, ctx3 in
    Some (AtS (SExpr ((), new_name, id, factory#top_modif, f, None),
	       SeqX ((ll,s::rr), ctx3)), delta_ids [id])
  | _ -> None


let insert_selection_gen
      ~(elt_of_increment : increment -> ('elt * delta_ids) option)
      ~(coord : 'elt list -> 'elt)
      ~(insert_elt : 'elt -> focus -> (focus * delta) option)
      (l_incr : increment list) (focus : focus) : (focus * delta) option =
  let l_f_incr, ldelta =
    List.fold_right
      (fun incr (lf,ldelta) ->
       match elt_of_increment incr with
       | None -> lf, DeltaNil::ldelta
       | Some (f,ids) -> f::lf, (delta_ids ids)::ldelta)
      l_incr ([],[]) in
  let f_incr_opt =
    match l_f_incr with
    | [] -> None
    | [f_incr] -> Some f_incr
    | _ -> Some (coord l_f_incr) in
  match f_incr_opt with
  | None -> None
  | Some f_incr ->
     ( match insert_elt f_incr focus with
       | None -> None
       | Some (foc,delta) -> Some (foc, DeltaSelection (delta, ldelta)) )

let insert_selection_p1 =
  insert_selection_gen
    ~elt_of_increment:elt_p1_of_increment
    ~insert_elt:insert_elt_p1
let insert_selection_and =
  insert_selection_p1 ~coord:(fun l -> And ((), l))
let insert_selection_or =
  insert_selection_p1 ~coord:(fun l -> Or ((), l))
			     
let insert_selection_s1 =
  insert_selection_gen
    ~elt_of_increment:elt_s1_of_increment
    ~insert_elt:insert_elt_s1
let insert_selection_nand =
  insert_selection_s1 ~coord:(fun l -> NAnd ((), l))
let insert_selection_nor =
  insert_selection_s1 ~coord:(fun l -> NOr ((), l))

let insert_selection_aggreg l_incr focus =
  match focus with
  | AtAggreg _
  | AtS (SAggreg _, _) ->
     let foc2, ldelta =
       List.fold_right
	 (fun incr (foc2,ldelta) ->
	  match incr with
	  | IncrForeachId id ->
	     ( match insert_foreach_id id foc2 with
	       | None -> foc2, DeltaNil::ldelta
	       | Some (foc2,delta) -> foc2, delta::ldelta )
	  | IncrAggregId (g,id) ->
	     ( match insert_aggreg_id g id foc2 with
	       | None -> foc2, DeltaNil::ldelta
	       | Some (foc2,delta) -> foc2, delta::ldelta )
	  | _ -> foc2, DeltaNil::ldelta)
	 l_incr (focus,[]) in
     Some (foc2, DeltaSelection (DeltaNil, ldelta))
(*
     List.fold_left
       (fun focus2_opt incr ->
	match incr with
	| IncrForeachId id ->
	   focus_opt_moves [insert_foreach_id id] focus2_opt
	| IncrAggregId (g,id) ->
	   focus_opt_moves [insert_aggreg_id g id] focus2_opt
	| _ -> focus2_opt)
       (Some focus) l_incr
 *)
  | _ -> None
	     
let insert_increment (incr : increment) (focus : focus) : (focus * delta) option =
  match incr with
    | IncrSelection (selop, l_incr) ->
       ( match selop with
	 | AndSel -> insert_selection_and l_incr focus
	 | OrSel -> insert_selection_or l_incr focus
	 | NAndSel -> insert_selection_nand l_incr focus
	 | NOrSel -> insert_selection_nor l_incr focus
	 | AggregSel -> insert_selection_aggreg l_incr focus )
    | IncrInput (s,dt) -> insert_input s dt focus
    | IncrTerm t -> insert_term t focus
    | IncrId (id,conv_opt) -> insert_id id conv_opt focus
    | IncrPred (arg,pred) -> insert_pred arg pred focus
    | IncrArg q -> insert_arg q focus
    | IncrType c -> insert_type c focus
    | IncrRel (p,m) -> insert_rel p m focus
    | IncrLatLong ll -> insert_latlong ll focus
    | IncrTriple arg -> insert_triple arg focus
    | IncrTriplify -> insert_triplify focus
    | IncrHierarchy trans_rel -> toggle_hierarchy trans_rel focus
    | IncrSim (pred,args,argo) -> insert_sim pred args argo focus
    | IncrSimRankIncr -> incr_sim_rank focus
    | IncrSimRankDecr -> decr_sim_rank focus
    | IncrAnything -> insert_anything focus
    | IncrThatIs -> insert_that_is focus
    | IncrSomethingThatIs -> insert_something_that_is focus
    | IncrAnd -> insert_and focus
    | IncrDuplicate -> insert_duplicate focus
    | IncrOr -> insert_or focus
    | IncrChoice -> insert_choice focus
    | IncrMaybe -> insert_maybe focus
    | IncrNot -> insert_not focus
    | IncrIn -> insert_in focus
    | IncrInWhichThereIs -> insert_in_which_there_is focus
    | IncrUnselect ->
      insert_modif_transf
	(function
	  | (Unselect,order) -> Select, order
	  | (_,order) ->  Unselect, order)
	focus
    | IncrOrder order ->
      insert_modif_transf
	(function (proj, order0) ->
	  if order0 = order
	  then proj, Unordered
	  else proj, order)
	focus
    | IncrForeach -> insert_foreach focus
    | IncrAggreg g -> insert_aggreg g focus
    | IncrForeachResult -> insert_foreach_result focus
    | IncrForeachId id -> insert_foreach_id id focus
    | IncrAggregId (g,id) -> insert_aggreg_id g id focus
    | IncrFuncArg (is_pred,func,arity,pos,res_conv_opt,arg_conv_opt) -> insert_func_arg is_pred func arity pos res_conv_opt arg_conv_opt focus
    | IncrName name -> insert_name name focus
	
       
let delete_list = function
  | [], [] -> `Empty
  | [x], [] -> `Single x
  | [], [x] -> `Single x
  | x::ll1, rr -> `List (x,ll1,rr)
  | [], x::rr1 -> `List (x,[],rr1)

let rec delete_elt_sn_is_top cp =
  let cp', ids = delete_elt_sn cp in
  (if cp = cp' then None else Some cp'), ids
and delete_elt_sn : unit elt_sn -> unit elt_sn * delta_ids = function
  | CNil () -> CNil (), []
  | CCons ((), Q _, _, cp) -> delete_elt_sn cp
  | CCons ((), arg, np, cp) ->
     let np, ids1 = delete_elt_s1 np in
     let cp, ids2 = delete_elt_sn cp in
     CCons ((), arg, np, cp), ids1@ids2
  | CAnd ((), []) -> assert false
  | CAnd ((), cp::_) -> delete_elt_sn cp
  | COr ((), []) -> assert false
  | COr ((), cp::_) -> delete_elt_sn cp
  | CMaybe ((),cp) -> delete_elt_sn cp
  | CNot ((),cp) -> delete_elt_sn cp
(*
  | CAnd ((), l) ->
     ( match delete_elt_sn_list l with
       | [], ids -> CNil (), ids
       | [cp], ids -> cp, ids
       | l, ids -> CAnd ((),l), ids )
  | COr ((), l) ->
     ( match delete_elt_sn_list l with
       | [], ids -> CNil (), ids
       | [cp], ids -> cp, ids
       | l, ids -> COr ((),l), ids )
  | CMaybe ((), cp) ->
     ( match delete_elt_sn cp with
       | CNil (), ids -> CNil (), ids
       | cp, ids -> CMaybe ((), cp), ids )
  | CNot ((), cp) ->
     ( match delete_elt_sn cp with
       | CNil (), ids -> CNil (), ids
       | cp, ids -> CNot ((), cp), ids )
and delete_elt_sn_list = function
  | [] -> [], []
  | cp::l ->
     let cp', ids1 = delete_elt_sn cp in
     let l', ids2 = delete_elt_sn_list l in
     ( match cp' with
     | CNil () -> l', ids1@ids2
     | cp' -> cp'::l', ids1@ids2 )
 *)
and delete_elt_s1 : unit elt_s1 -> unit elt_s1 * delta_ids = function
  | Det ((), An (id,_,_), _) ->
     Det ((), An (id, factory#top_modif, Thing), None), []
  | _ ->
     let np, id = factory#top_s1 in
     np, [id]
and delete_elt_s : unit elt_s -> unit elt_s * delta_ids = function
  | Return ((), np) ->
     let np, ids = delete_elt_s1 np in
     Return ((), np), ids
  | _ ->
     let s, id = factory#top_s in
     s, [id]
		   
let rec delete_ctx_p1 : ctx_p1 -> focus option * delta_ids = function
  | DetThatX (det,ctx) ->
     Some (AtS1 (Det ((),det,None), ctx)), []
  | AnAggregThatX (id,modif,g,np,ctx) ->
     Some (AtS1 (AnAggreg ((), id, modif, g, None, np), ctx)), []
  | ForEachThatX (id,modif,id2,ctx) ->
     Some (AtAggreg (ForEach ((), id,modif,None,id2), ctx)), []
  | TheAggregThatX (id,modif,g,id2,ctx) ->
     Some (AtAggreg (TheAggreg ((), id,modif,g,None,id2), ctx)), []
  | SExprThatX (name,id,modif,expr,ctx) ->
     Some (AtS (SExpr ((), name, id, modif, expr, None), ctx)), []
  | AndX (ll_rr,ctx) ->
    ( match delete_list ll_rr with
      | `Empty -> delete_ctx_p1 ctx
      | `Single elt -> Some (AtP1 (elt, ctx)), []
      | `List (elt,ll2,rr2) -> Some (AtP1 (elt, AndX ((ll2,rr2),ctx))), [] )
  | OrX (ll_rr,ctx) ->
    ( match delete_list ll_rr with
      | `Empty -> delete_ctx_p1 ctx
      | `Single elt -> Some (AtP1 (elt, ctx)), []
      | `List (elt,ll2,rr2) -> Some (AtP1 (elt, OrX ((ll2, rr2), ctx))), [] )
  | MaybeX ctx -> delete_ctx_p1 ctx
  | NotX ctx -> delete_ctx_p1 ctx
  | InX (npg,ctx) -> delete_ctx_p1 ctx
and delete_ctx_sn (f_opt,ids) ctx =
  match ctx with
  | PredX (arg,pred,ctx2) ->
     ( match f_opt with
       | None -> delete_ctx_p1 ctx2
       | Some f -> Some (at_sn f ctx), ids )
  | CConsX2 (arg,np,ctx2) ->
     ( match f_opt with
       | None ->
	  let f2_opt, ids2 =
	    delete_elt_sn_is_top (CCons ((),arg,np, CNil ())) in	    
	  delete_ctx_sn (f2_opt,ids@ids2) ctx2
       | Some f -> Some (at_sn f ctx), ids )
  | CAndX (ll_rr,ctx2) ->
     ( match delete_list ll_rr with
       | `Empty -> delete_ctx_sn (None,ids) ctx2
       | `Single elt -> Some (AtSn (elt, ctx2)), ids
       | `List (elt,ll2,rr2) -> Some (AtSn (elt, CAndX ((ll2,rr2),ctx2))), ids )
  | COrX (ll_rr,ctx2) ->
     ( match delete_list ll_rr with
       | `Empty -> delete_ctx_sn (None,ids) ctx2
       | `Single elt -> Some (AtSn (elt, ctx2)), ids
       | `List (elt,ll2,rr2) -> Some (AtSn (elt, COrX ((ll2,rr2),ctx2))), ids )
  | CMaybeX ctx2 -> delete_ctx_sn (f_opt,ids) ctx2
  | CNotX ctx2 -> delete_ctx_sn (f_opt,ids) ctx2
and delete_ctx_s1 f_opt ctx =
  match ctx with
    | IsX ctx2 -> delete_ctx_p1 ctx2
    | RelX (_,_,ctx2)
    | TripleX1 (_,_,ctx2)
    | TripleX2 (_,_,ctx2) ->
      ( match f_opt with
	| None -> delete_ctx_p1 ctx2
	| Some f ->
	   let np, ids = delete_elt_s1 f in
	   Some (AtS1 (np, ctx)), ids )
    | ReturnX ctx2 ->
      ( match f_opt with
	| None -> delete_ctx_s None ctx2
	| Some f ->
	   let np, ids = delete_elt_s1 f in
	   Some (AtS1 (np, ctx)), ids )
    | HierX (id,pred,args,argo,ctx2) ->
       ( match f_opt with
	 | None ->
	    let foc_opt, ids = delete_ctx_p1 ctx2 in
	    foc_opt, id::ids
	 | Some f ->
	    let np, ids = delete_elt_s1 f in
	    Some (AtS1 (np, ctx)), id::ids )
    | SimX (pred,args,argo,rank,ctx2) ->
       ( match f_opt with
	 | None ->
	    let foc_opt, ids = delete_ctx_p1 ctx2 in
	    foc_opt, ids
	 | Some f ->
	    let np, ids = delete_elt_s1 f in
	    Some (AtS1 (np, ctx)), ids )
    | AnAggregX (id,modif,g,rel_opt,ctx2) -> delete_ctx_s1 f_opt ctx2
    | CConsX1 (arg,cp,ctx2) ->
       ( match arg, f_opt with
	 | Q _, None -> Some (at_sn cp ctx2), []
	 | (S|P|O), None -> (* those args cannot be removed *)
	    delete_ctx_sn
	      (let np, id = factory#top_s1 in
	       let f2_opt, ids = delete_elt_sn_is_top (CCons ((),arg,np,cp)) in
	       f2_opt, id::ids)
	      ctx2
	 | _, Some f ->
	    let np, ids = delete_elt_s1 f in
	    Some (AtS1 (np, ctx)), ids )
    | NAndX (ll_rr,ctx2) ->
      ( match delete_list ll_rr with
	| `Empty -> delete_ctx_s1 None ctx2
	| `Single elt -> Some (AtS1 (elt, ctx2)), []
	| `List (elt,ll2,rr2) -> Some (AtS1 (elt, NAndX ((ll2,rr2),ctx2))), [] )
    | NOrX (ll_rr,ctx2) ->
      ( match delete_list ll_rr with
	| `Empty -> delete_ctx_s1 None ctx2
	| `Single elt -> Some (AtS1 (elt, ctx2)), []
	| `List (elt,ll2,rr2) -> Some (AtS1 (elt, NOrX ((ll2,rr2),ctx2))), [] )
    | NMaybeX ctx2 -> delete_ctx_s1 f_opt ctx2
    | NNotX ctx2 -> delete_ctx_s1 f_opt ctx2
    | InGraphX (_,ctx2) ->
      ( match f_opt with
      | None -> delete_ctx_p1 ctx2
      | Some f -> let np, ids = delete_elt_s1 f in
		  Some (AtS1 (np, ctx)), ids )
    | InWhichThereIsX ctx2 ->
      ( match f_opt with
      | None -> delete_ctx_p1 ctx2
      | Some f -> let np, ids = delete_elt_s1 f in
		  Some (AtS1 (np, ctx)), ids )
and delete_ctx_aggreg ctx =
  match ctx with
  | SAggregX (ll_rr,ctx) ->
    ( match delete_list ll_rr with
    | `Empty -> delete_ctx_s None ctx
    | `Single elt -> Some (AtAggreg (elt, SAggregX (([],[]),ctx))), []
    | `List (elt,ll2,rr2) -> Some (AtAggreg (elt, SAggregX ((ll2,rr2), ctx))), [] )
and delete_ctx_expr f_opt ctx =
  match ctx with
  | SExprX (name,id,modif,rel_opt,ctx2) -> delete_ctx_s None ctx2
  | SFilterX (id,ctx2) -> delete_ctx_s None ctx2
  | ApplyX (func,ll_rr,conv_opt,ctx2) ->
    ( match f_opt with
    | None -> delete_ctx_expr (Some (Apply ((), func, list_of_ctx (None, factory#top_expr) ll_rr))) ctx2
    | Some _ -> Some (AtExpr (factory#top_expr, apply_conv_ctx_expr None ctx)), [] ) (* forgetting conversion *)
  | ChoiceX (ll_rr,ctx2) ->
    ( match delete_list ll_rr with
    | `Empty -> delete_ctx_expr None ctx2
    | `Single elt -> Some (AtExpr (elt, ctx2)), []
    | `List (elt,ll2,rr2) -> Some (AtExpr (elt, ChoiceX ((ll2,rr2),ctx2))), [] )
and delete_ctx_s f_opt ctx =
  match ctx with
  | Root ->
     ( match f_opt with
       | None -> None, []
       | Some f -> (* TODO: ugly to switch between (foc * delta) option and foc option * delta_ids *)
	  let s, ids = delete_elt_s f in
	  let foc_opt = focus_opt_moves [down_focus]
					(Some (AtS (s, Root), DeltaIds ids)) in
	  match foc_opt with
	  | None -> None, []
	  | Some (foc, DeltaIds ids) -> Some foc, ids
	  | _ -> assert false )
  | SeqX (ll_rr,ctx2) ->
    ( match delete_list ll_rr with
    | `Empty -> delete_ctx_s None ctx2
    | `Single elt -> Some (AtS (elt,ctx2)), []
    | `List (elt,ll2,rr2) -> Some (AtS (elt, SeqX ((ll2,rr2),ctx2))), [] )

let delete_focus focus =
  let new_focus_opt, ids =
    match focus with
    | AtP1 (Sim (_,np,pred,args,argo,rank),ctx) ->
       if rank <= 1
       then Some (at_s1 np (IsX ctx)), []
       else Some (AtP1 (Sim ((),np,pred,args,argo,rank-1),ctx)), []
    | AtP1 (_, ctx) -> delete_ctx_p1 ctx
    | AtSn (f, ctx) -> delete_ctx_sn (delete_elt_sn_is_top f) ctx
    | AtS1 (f, ctx) -> delete_ctx_s1 (if is_top_s1 f then None else Some f) ctx
    | AtAggreg (ForTerm (_,t,id2), ctx) ->
       let dim, id = factory#top_dim_foreach id2 in
       Some (AtAggreg (dim, ctx)), [id]
    | AtAggreg (f, ctx) -> delete_ctx_aggreg ctx
    | AtExpr (f, ctx) -> delete_ctx_expr (if is_top_expr f then None else Some f) ctx
    | AtS (f, ctx) -> delete_ctx_s (if is_top_s f then None else Some f) ctx in
  let new_focus_ids_opt =
    match new_focus_opt with
    | None -> None
    | Some foc -> Some (foc, delta_ids ids) in
  match new_focus_ids_opt with
  | Some (AtSn (CNil (), _), _) ->
     focus_opt_moves [up_focus] new_focus_ids_opt
  | _ -> new_focus_ids_opt
  

(* goto to query *)

let focus_of_query_path (s : unit elt_s) (path : path) = focus_of_elt_s_path (s,path)
