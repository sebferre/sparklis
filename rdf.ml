(*
  Copyright 2013-2017 Sébastien Ferré, IRISA, Université de Rennes 1

  This file is part of Sparklis.
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
let rdfs_domain = "http://www.w3.org/2000/01/rdf-schema#domain"
let rdfs_range = "http://www.w3.org/2000/01/rdf-schema#range"
let rdfs_inheritsThrough = "http://www.w3.org/2000/01/rdf-schema#inheritsThrough"

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
