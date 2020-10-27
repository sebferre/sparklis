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

(* common utilities *)

let not1 (p : 'a -> bool) : 'a -> bool = fun x -> not (p x)

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

let rec map_last (f : bool -> 'a -> 'b) (l : 'a list) : 'b list =
  match l with
  | [] -> []
  | [x] -> [f true x]
  | x::r -> f false x :: map_last f r
		    
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
  List.sort Stdlib.compare l1 = List.sort Stdlib.compare l2
    
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
  Bytes.set s2 0 (if upper.(0) && 1 <= n-1 && not lower.(1) then s.[0] else Char.lowercase_ascii s.[0]);
  let j = ref 1 in
  for i = 1 to n-1 do
    if lower.(i-1) && upper.(i) then begin
      Bytes.set s2 !j ' ';
      incr j;
      Bytes.set s2 !j (if i+1 <= n-1 && not lower.(i+1) then s.[i] else Char.lowercase_ascii s.[i]);
      incr j end
    else if upper.(i-1) && upper.(i) && i+1 <= n-1 && lower.(i+1) then begin
      Bytes.set s2 !j ' ';
      incr j;
      Bytes.set s2 !j (Char.lowercase_ascii s.[i]);
      incr j end
    else begin
      Bytes.set s2 !j s.[i];
      incr j
    end
  done;
  Bytes.sub_string s2 0 !j

let mapfilter (f : 'a -> 'b option) (l : 'a list) : 'b list =
  List.fold_right
    (fun x res ->
     match f x with
     | None -> res
     | Some y -> y::res)
    l []

let mapforall (f : 'a -> 'b option) (l : 'a list) : 'b list option =
  let ok, res =
    List.fold_right
      (fun x (ok, res) ->
       match f x with
       | None -> (false, res)
       | Some y -> (ok, y::res))
      l (true,[]) in
  if ok then Some res else None
    
let list_fold_prod (f : 'a -> 'b list -> 'a) (acc : 'a) (list_col_x : 'b list list) : 'a =
  let rec aux acc rev_row_x = function
    | [] -> f acc (List.rev rev_row_x)
    | col_x::lcx ->
      List.fold_left
	(fun acc x -> aux acc (x::rev_row_x) lcx)
	acc col_x
  in
  aux acc [] list_col_x

let rec split_list_at l n =
  if n = 0
  then [], l
  else
    match l with
    | [] -> [], []
    | x::r ->
       let l1, l2 = split_list_at r (n-1) in
       x :: l1, l2

