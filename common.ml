
(* common utilities *)

let list_rev_assoc y l = fst (List.find (fun (x1,y1) -> y1=y) l)

(* retaining first occurences and removing duplicates *)
let list_to_set l =
  let rec aux acc = function
    | [] -> List.rev acc
    | x::l -> if List.mem x acc then aux acc l else aux (x::acc) l
  in
  aux [] l

let unobfuscate_string s = (* symmetric, to be used for obfuscation *)
  String.map
    (fun oc ->
      let ocode = Char.code oc in
      let code = if ocode > 127 then ocode else 127 - ocode in
      Char.chr code)
    s
