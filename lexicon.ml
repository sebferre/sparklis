

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

let name_of_uri_concept =
  fun uri ->
    let name = name_of_uri uri in
    try Common.uncamel name
    with _ -> name

type property_syntagm = [ `Noun | `InvNoun | `TransVerb | `TransAdj ]

let prepositions = ["by"; "for"; "with"; "on"; "from"; "to"; "off"; "in"; "about"; "after"; "at"; "down"; "up"; "into"; "over"; "until"; "upon"; "within"; "without"]

let syntagm_of_property_name (name : string) : property_syntagm * string =
  if Common.has_suffix name " of" then `InvNoun, String.sub name 0 (String.length name - 3)
  else if Common.has_prefix name "has " then `Noun, String.sub name 4 (String.length name - 4)
  else if Common.has_suffix name "ed" || List.exists (fun prep -> Common.has_suffix name ("s " ^ prep)) prepositions then `TransVerb, name
  else if List.exists (fun prep -> Common.has_suffix name (" " ^ prep)) prepositions then `TransAdj, name
  else `Noun, name

let syntagm_name_of_uri_property =
  fun uri ->
    let name = name_of_uri_concept uri in
    syntagm_of_property_name name
