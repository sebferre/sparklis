
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

let has_prefix (s1 : string) (s2 : string) : bool =
  let n1 = String.length s1 in
  let n2 = String.length s2 in
  let i = ref 0 in
  let res = ref true in
  while !res && !i < n2 && !i < n1 do
    res := s1.[!i] = s2.[!i];
    incr i
  done;
  !res && !i <= n1
