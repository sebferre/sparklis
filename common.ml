
(* common utilities *)

let list_rev_assoc y l = fst (List.find (fun (x1,y1) -> y1=y) l)

let unsome = function
  | Some x -> x
  | None -> invalid_arg "unsome"

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

let has_suffix (s1 : string) (s2 : string) : bool =
  let n1 = String.length s1 in
  let n2 = String.length s2 in
  let i1 = ref (n1-1) in
  let i2 = ref (n2-1) in
  let res = ref true in
  while !res && !i1 >= 0 && !i2 >= 0 do
    res := s1.[!i1] = s2.[!i2];
    decr i1;
    decr i2
  done;
  !res && !i2 < 0

let uncamel s =
  let n = String.length s in
  let lower = Array.init n (fun i -> 'a' <= s.[i] && s.[i] <= 'z') in
  let upper = Array.init n (fun i -> 'A' <= s.[i] && s.[i] <= 'Z') in
  let s2 = String.create (2*n) in
  s2.[0] <- if upper.(0) && 1 <= n-1 && not lower.(1) then s.[0] else Char.lowercase s.[0];
  let j = ref 1 in
  for i = 1 to n-1 do
    if lower.(i-1) && upper.(i) then begin
      s2.[!j] <- ' ';
      incr j;
      s2.[!j] <- if i+1 <= n-1 && not lower.(i+1) then s.[i] else Char.lowercase s.[i];
      incr j end
    else if upper.(i-1) && upper.(i) && i+1 <= n-1 && lower.(i+1) then begin
      s2.[!j] <- ' ';
      incr j;
      s2.[!j] <- Char.lowercase s.[i];
      incr j end
    else begin
      s2.[!j] <- s.[i];
      incr j
    end
  done;
  String.sub s2 0 !j
