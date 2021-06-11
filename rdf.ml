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

type uri = string

let uri_has_ext uri exts =
  List.exists
    (fun ext -> Filename.check_suffix uri ext)
    exts
let uri_is_image uri = uri_has_ext uri ["jpg"; "JPG"; "jpeg"; "JPEG"; "png"; "PNG"; "gif"; "GIF"; "bmp"; "BMP"; "svg"; "SVG"]
let uri_is_video uri = uri_has_ext uri ["mp4"; "MP4"; "mov"; "MOV"]
let uri_is_audio uri = uri_has_ext uri ["mp3"; "MP3"]

let xsd_string = "http://www.w3.org/2001/XMLSchema#string"
let xsd_integer = "http://www.w3.org/2001/XMLSchema#integer"
let xsd_decimal = "http://www.w3.org/2001/XMLSchema#decimal"
let xsd_double = "http://www.w3.org/2001/XMLSchema#double"
let xsd_date = "http://www.w3.org/2001/XMLSchema#date"
let xsd_dateTime = "http://www.w3.org/2001/XMLSchema#dateTime"
let xsd_time = "http://www.w3.org/2001/XMLSchema#time"
let xsd_duration = "http://www.w3.org/2001/XMLSchema#duration"
let xsd_boolean = "http://www.w3.org/2001/XMLSchema#boolean"

let rdf_type = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let rdf_Property = "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property"
let rdf_first = "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let rdf_item = "http://www.w3.org/1999/02/22-rdf-syntax-ns#item" (* virtual RDF property to be expanded by rdf:rest*/rdf:first in SPARQL queries *)
		 
let rdfs_Class = "http://www.w3.org/2000/01/rdf-schema#Class"
let rdfs_subClassOf = "http://www.w3.org/2000/01/rdf-schema#subClassOf"
let rdfs_subPropertyOf = "http://www.w3.org/2000/01/rdf-schema#subPropertyOf"
let rdfs_domain = "http://www.w3.org/2000/01/rdf-schema#domain"
let rdfs_range = "http://www.w3.org/2000/01/rdf-schema#range"
let rdfs_inheritsThrough = "http://www.w3.org/2000/01/rdf-schema#inheritsThrough" (* TODO: move to other namespace *)
let rdfs_label = "http://www.w3.org/2000/01/rdf-schema#label"

let owl_Thing = "http://www.w3.org/2002/07/owl#Thing"
let owl_Class = "http://www.w3.org/2002/07/owl#Class"
let owl_ObjectProperty = "http://www.w3.org/2002/07/owl#ObjectProperty"
let owl_DatatypeProperty = "http://www.w3.org/2002/07/owl#DatatypeProperty"

let owl_transitiveOf = "http://www.irisa.fr/LIS/ferre/vocab/owl#transitiveOf" 
                         
let nary_subjectObject = "http://www.irisa.fr/LIS/ferre/vocab/nary#subjectObject"
let nary_eventObject = "http://www.irisa.fr/LIS/ferre/vocab/nary#eventObject"

let schema_position = "https://schema.org/position"
let schema_logo = "https://schema.org/logo"

let wikibase_Property = "http://wikiba.se/ontology#Property"
let wikibase_directClaim = "http://wikiba.se/ontology#directClaim"
let wikibase_claim = "http://wikiba.se/ontology#claim"
let wikibase_statementProperty = "http://wikiba.se/ontology#statementProperty"
let wikidata_entity (q : string) = "http://www.wikidata.org/entity/" ^ q
let wikidata_Q (n : int) = "http://www.wikidata.org/entity/Q" ^ string_of_int n
let wikidata_P (n : int) = "http://www.wikidata.org/prop/P" ^ string_of_int n
let p_P625 = wikidata_P 625 (* Wikidata: geographical coordinates *)

let lat_long_properties =
  [ "http://www.w3.org/2003/01/geo/wgs84_pos#lat", "http://www.w3.org/2003/01/geo/wgs84_pos#long";
    "http://www.semwebtech.org/mondial/10/meta#latitude", "http://www.semwebtech.org/mondial/10/meta#longitude";
    "http://www.w3.org/2006/vcard/ns#latitude", "http://www.w3.org/2006/vcard/ns#longitude";
    "http://schema.org/latitude", "http://schema.org/longitude";
    "https://schema.org/latitude", "https://schema.org/longitude" ]
  
(* ------------------------- *)

let config_wikidata_mode =
  new Config.boolean_input
      ~key:"wikidata_mode"
      ~input_selector:"#input-wikidata-mode"
      ~default:false
      ()
    
type var = string

type term =
  | URI of uri
  | Number of float * string * string (* value, string, datatype *)
  | TypedLiteral of string * uri
  | PlainLiteral of string * string
  | Bnode of string
  | Var of var

let js_term_map : term Jsutils.js_map =
  Jsutils.js_map
    (`Sum ([| |],
           [| "uri", [| "uri", `String|];
              "number", [| "number", `Float; "str", `String; "datatype", `String|];
              "typedLiteral", [| "str", `String; "datatype", `String|];
              "plainLiteral", [| "str", `String; "lang", `String|];
              "bnode", [| "id", `String|];
              "var", [| "name", `String|] |]))
(*let _ = Jsutils.js_map_log "RDF term:" js_term_map [URI "http://example.org/"; Number (3.14, "3.14", "xsd:float")] (* TEST *)*)
  
let term_is_var = function
  | Var _ -> true
  | _ -> false

let term_can_be_subject = function
  | URI _ | Bnode _ | Var _ -> true
  | _ -> false
	     
let string_of_term = function
  | URI uri -> uri
  | Number (f,s,dt) -> s
  | TypedLiteral (s,dt) -> s
  | PlainLiteral (s,lang) -> s
  | Bnode id -> id
  | Var v -> v

let float_of_term = function
  | Number (f,_,_) -> f
  | _ -> invalid_arg "float_of_term"
