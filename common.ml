
(* common utilities *)

let rec from_to a b =
  if a <= b
  then a :: from_to (a+1) b
  else []

let rec from_downto a b =
  if a >= b
  then a :: from_downto (a-1) b
  else []
    
let list_rev_assoc y l = fst (List.find (fun (x1,y1) -> y1=y) l)

let unsome = function
  | Some x -> x
  | None -> invalid_arg "unsome"

let take_rest n l =
  let rec aux = function
    | 0, t, r -> t, r
    | _, t, [] -> t, []
    | n, t, x::r -> aux (n-1, x::t, r)
  in
  let rev_t, r = aux (n,[],l) in
  List.rev rev_t, r

let rec bin_list n l =
  if l = []
  then []
  else
    let t, r = take_rest n l in
    t :: bin_list n r

(* retaining first occurences and removing duplicates *)
let list_to_set l =
  let rec aux acc = function
    | [] -> List.rev acc
    | x::l -> if List.mem x acc then aux acc l else aux (x::acc) l
  in
  aux [] l

let equal_lists_as_sets l1 l2 =
  List.sort Pervasives.compare l1 = List.sort Pervasives.compare l2
    
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
  !res && !i = n2

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

let uncamel (s : string) : string =
  let n = String.length s in
  let lower = Array.init n (fun i -> 'a' <= s.[i] && s.[i] <= 'z') in
  let upper = Array.init n (fun i -> 'A' <= s.[i] && s.[i] <= 'Z') in
  let s2 = Bytes.create (2*n) in
  Bytes.set s2 0 (if upper.(0) && 1 <= n-1 && not lower.(1) then s.[0] else Char.lowercase s.[0]);
  let j = ref 1 in
  for i = 1 to n-1 do
    if lower.(i-1) && upper.(i) then begin
      Bytes.set s2 !j ' ';
      incr j;
      Bytes.set s2 !j (if i+1 <= n-1 && not lower.(i+1) then s.[i] else Char.lowercase s.[i]);
      incr j end
    else if upper.(i-1) && upper.(i) && i+1 <= n-1 && lower.(i+1) then begin
      Bytes.set s2 !j ' ';
      incr j;
      Bytes.set s2 !j (Char.lowercase s.[i]);
      incr j end
    else begin
      Bytes.set s2 !j s.[i];
      incr j
    end
  done;
  Bytes.sub s2 0 !j

    
