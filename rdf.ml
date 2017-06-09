(*
  Copyright 2013-2017 Sébastien Ferré, IRISA, Université de Rennes 1

  This file is part of Sparklis.

  Sparklis is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Sparklis is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with Sparklis.  If not, see <http://www.gnu.org/licenses/>.
*)

type uri = string

let uri_has_ext uri exts =
  List.exists
    (fun ext -> Filename.check_suffix uri ext)
    exts
let uri_is_image uri = uri_has_ext uri ["jpg"; "JPG"; "jpeg"; "JPEG"; "png"; "PNG"; "gif"; "GIF"; "bmp"; "BMP"]

let xsd_string = "http://www.w3.org/2001/XMLSchema#string"
let xsd_integer = "http://www.w3.org/2001/XMLSchema#integer"
let xsd_decimal = "http://www.w3.org/2001/XMLSchema#decimal"
let xsd_double = "http://www.w3.org/2001/XMLSchema#double"
let xsd_date = "http://www.w3.org/2001/XMLSchema#date"
let xsd_dateTime = "http://www.w3.org/2001/XMLSchema#dateTime"
let xsd_time = "http://www.w3.org/2001/XMLSchema#time"
let xsd_boolean = "http://www.w3.org/2001/XMLSchema#boolean"

let rdfs_subClassOf = "http://www.w3.org/2000/01/rdf-schema#subClassOf"
let rdfs_subPropertyOf = "http://www.w3.org/2000/01/rdf-schema#subPropertyOf"
  
let owl_Thing = "http://www.w3.org/2002/07/owl#Thing"

let lat_long_properties =
  [ "http://www.w3.org/2003/01/geo/wgs84_pos#lat", "http://www.w3.org/2003/01/geo/wgs84_pos#long";
    "http://www.semwebtech.org/mondial/10/meta#latitude", "http://www.semwebtech.org/mondial/10/meta#longitude";
    "http://www.w3.org/2006/vcard/ns#latitude", "http://www.w3.org/2006/vcard/ns#longitude";
    "http://schema.org/latitude", "http://schema.org/longitude" ]
  
(* ------------------------- *)

type var = string

type term =
  | URI of uri
  | Number of float * string * string (* value, string, datatype *)
  | TypedLiteral of string * uri
  | PlainLiteral of string * string
  | Bnode of string
  | Var of var

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
