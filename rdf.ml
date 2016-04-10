
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
