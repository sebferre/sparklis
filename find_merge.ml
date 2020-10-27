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

(* copied and slightly adapted from prog/ocaml/lib/ *)

(* exposes an interface similar to hashtables plus the possibility to merge keys *)
class ['a,'b] hashtbl ~(init_val : 'b) ~(merge_val : 'b -> 'b -> 'b) =
object (self)
  (* data structures for the Find-Merge algorithm *)
  val parent : ('a,'a) Hashtbl.t = Hashtbl.create 13 (* no parent for roots *)
  val rank_value : ('a, int * 'b) Hashtbl.t = Hashtbl.create 13 (* from roots to (rank, value) *)

  method private find_root (x : 'a) : 'a =
    let rec get_root x =
      try
	let parent_x = Hashtbl.find parent x in
	let root = get_root parent_x in
	if root <> parent_x then Hashtbl.replace parent x root;
	root
      with Not_found -> (* no parent *)
      (*      Hashtbl.add rank_value x (0,init_val);*)
	x (* x is its own root *)
    in
    let root = get_root x in
    if root = x && not (Hashtbl.mem rank_value root) then (* new root (implies root=x) *)
      Hashtbl.add rank_value root (0,init_val);
    root

  method private merge_roots (root1 : 'a) (root2 : 'a) : 'a =
    if root1 = root2
    then root1
    else begin
      let r1, v1 = try Hashtbl.find rank_value root1 with Not_found -> 0, init_val in
      let r2, v2 = try Hashtbl.find rank_value root2 with Not_found -> 0, init_val in
      let new_root, new_rank, old_root =
	if r1 < r2 then root2, r2, root1
	else if r1 > r2 then root1, r1, root2
	else root1, r1+1, root2 in
      let new_val = merge_val v1 v2 in
      Hashtbl.add parent old_root new_root;
      Hashtbl.remove rank_value old_root;
      Hashtbl.replace rank_value new_root (new_rank, new_val);
      new_root
    end

  method find (x : 'a) : 'b =
    let root = self#find_root x in
    let rank, v = try Hashtbl.find rank_value root with _ -> 0, init_val in
    v

  method replace (x : 'a) (v : 'b) : unit =
    let root = self#find_root x in
    try
      let r, _ = Hashtbl.find rank_value root in
      Hashtbl.replace rank_value x (r,v)
    with Not_found ->
      Hashtbl.add rank_value x (0,v)
    
  method merge (lx : 'a list) : 'a =
    match lx with
    | [] -> invalid_arg "Find_merge.hashtbl#merge: empty list"
    | x::lx1 ->
      List.fold_left
	(fun root x1 ->
	  let root1 = self#find_root x1 in
	  self#merge_roots root root1)
	(self#find_root x) lx1

  method merged (x1 : 'a) (x2 : 'a) : bool =
    try self#find_root x1 = self#find_root x2
    with _ -> false

  method cardinal : int =
    Hashtbl.length rank_value
      
  method fold : 'c. ('a -> 'b -> 'c -> 'c) -> 'c -> 'c =
    (* the ['a] is a represant key for the value ['b] *)
    fun f init ->
      Hashtbl.fold
	(fun x (r,v) -> f x v)
	rank_value init

  method iter (f : 'a -> 'b -> unit) : unit =
    Hashtbl.iter
      (fun x (r,v) -> f x v)
      rank_value
end


(* exposes an interface similar to sets plus the possibility to merge keys *)
module Set (X : Map.OrderedType) =
struct
  module M = Map.Make(X)
  type t = { elements : X.t list;
	     parent : X.t M.t; (* no parent for roots *)
	     rank : int M.t (* from roots to ranks *)
	   }

  let empty = { elements = []; parent = M.empty; rank = M.empty }
    
  let rec (*private*) find_root (x : X.t) (o : t) : X.t * t =
    try
      let parent_x = M.find x o.parent in
      let root, o = find_root parent_x o in
      let o =
	if root <> parent_x
	then {o with parent = M.add x root o.parent}
	else o in
      root, o
    with Not_found -> (* x is a root *)
      let root = x in
      if M.mem root o.rank (* is this a known root *)
      then root, o
      else root, { o with elements = x::o.elements; rank = M.add root 0 o.rank }
(*      let r = 0 in
      let new_elements = if M.mem x o.rank then o.elements else x::o.elements in
      let o = { o with elements = new_elements; rank = M.add root r o.rank } in
      root, o *)

  let (*private*) merge_roots (root1 : X.t) (root2 : X.t) (o : t): X.t * t =
    if root1 = root2
    then root1, o
    else begin
      let r1 = try M.find root1 o.rank with Not_found -> assert false (* 0 *) in
      let r2 = try M.find root2 o.rank with Not_found -> assert false (* 0 *) in
      let new_root, new_rank, old_root =
	if r1 < r2 then root2, r2, root1
	else if r1 > r2 then root1, r1, root2
	else root1, r1+1, root2 in
      let o = { elements = o.elements;
		parent = M.add old_root new_root o.parent;
		rank = M.add new_root new_rank (M.remove old_root o.rank) } in
      new_root, o
    end

  let add (x : X.t) (o : t) : t =
    let root, o = find_root x o in
    o

  let merge (lx : X.t list) (o : t) : X.t * t =
    match lx with
    | [] -> invalid_arg "Find_merge.Set.merge: empty list"
    | x::lx1 ->
      List.fold_left
	(fun (root,o) x1 ->
	  let root1, o = find_root x1 o in
	  merge_roots root root1 o)
	(find_root x o) lx1

  let merged (x1 : X.t) (x2 : X.t) (o : t) : bool =
    try fst (find_root x1 o) = fst (find_root x2 o)
    with _ -> false

  let merged_with (x : X.t) (o : t) : X.t list =
    List.filter
      (fun y -> merged x y o)
      o.elements

  let cardinal (o : t) : int =
    M.cardinal o.rank
      
  let fold : 'c. (X.t -> 'c -> 'c) -> t -> 'c -> 'c =
    (* the [X.t] is a represant key for the value ['b] *)
    fun f o init ->
      M.fold
	(fun x r -> f x)
	o.rank init

  let iter (f : X.t -> unit) (o : t) : unit =
    M.iter
      (fun x r -> f x)
      o.rank
end

module type Val =
sig
  type t
  val init : t
  val merge : t -> t -> t
end
  
(* exposes an interface similar to maps plus the possibility to merge keys *)
module Map (X : Map.OrderedType) (V : Val) =
struct
  module M = Map.Make(X)
  type t = { parent : X.t M.t; (* no parent for roots *)
	     rank_value : (int * V.t) M.t (* from roots to (rank, value) *)
	   }

  let empty = { parent = M.empty; rank_value = M.empty }
    
  let rec (*private*) find_root (x : X.t) (o : t) : X.t * t =
    try
      let parent_x = M.find x o.parent in
      let root, o = find_root parent_x o in
      let o =
	if root <> parent_x
	then {o with parent = M.add x root o.parent}
	else o in
      root, o
    with Not_found ->
      let o = {o with rank_value = M.add x (0,V.init) o.rank_value} in
      x, o

  let (*private*) merge_roots (root1 : X.t) (root2 : X.t) (o : t): X.t * t =
    if root1 = root2
    then root1, o
    else begin
      let r1, v1 = try M.find root1 o.rank_value with Not_found -> 0, V.init in
      let r2, v2 = try M.find root2 o.rank_value with Not_found -> 0, V.init in
      let new_root, new_rank, old_root =
	if r1 < r2 then root2, r2, root1
	else if r1 > r2 then root1, r1, root2
	else root1, r1+1, root2 in
      let new_val = V.merge v1 v2 in
      let o = { parent = M.add old_root new_root o.parent;
		rank_value = M.add new_root (new_rank, new_val) (M.remove old_root o.rank_value) } in
      new_root, o
    end

  let find (x : X.t) (o : t) : X.t * V.t * t =
    let root, o = find_root x o in
    let rank, v = try M.find root o.rank_value with _ -> 0, V.init in
    root, v, o

  let replace (x : X.t) (v : V.t) (o : t) : t =
    let root, o = find_root x o in
    try
      let r, _ = M.find root o.rank_value in
      { o with rank_value = M.add x (r,v) o.rank_value }
    with Not_found ->
      { o with rank_value = M.add x (0,v) o.rank_value }
    
  let merge (lx : X.t list) (o : t) : X.t * t =
    match lx with
    | [] -> invalid_arg "Find_merge.Map.merge: empty list"
    | x::lx1 ->
      List.fold_left
	(fun (root,o) x1 ->
	  let root1, o = find_root x1 o in
	  merge_roots root root1 o)
	(find_root x o) lx1

  let merged (x1 : X.t) (x2 : X.t) (o : t) : bool =
    try fst (find_root x1 o) = fst (find_root x2 o)
    with _ -> false

  let cardinal (o : t) : int =
    M.cardinal o.rank_value
      
  let fold : 'c. (X.t -> V.t -> 'c -> 'c) -> t -> 'c -> 'c =
    (* the [X.t] is a represant key for the value [V.t] *)
    fun f o init ->
      M.fold
	(fun x (r,v) -> f x v)
	o.rank_value init

  let iter (f : X.t -> V.t -> unit) (o : t) : unit =
    M.iter
      (fun x (r,v) -> f x v)
      o.rank_value
end

