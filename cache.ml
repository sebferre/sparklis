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

open Js_of_ocaml
   
class virtual ['a,'b] cache =
object
  method virtual info : 'a -> 'b
  method virtual enqueue : 'a -> unit
  method virtual sync : (unit -> unit) -> unit
end

let make_js_cache (js_key_map : 'a Jsutils.js_map) (js_val_map : 'b Jsutils.js_map) (cache : ('a,'b) cache) =
  object%js
    (*val __cache = cache*)
    method info (js_key : Js.Unsafe.any) : Js.Unsafe.any =
      let key = js_key_map.extract js_key in
      let v = cache#info key in
      js_val_map.inject v
    method enqueue (js_key : Js.Unsafe.any) : unit =
      let key = js_key_map.extract js_key in
      cache#enqueue key
    method sync (callback : Js.Unsafe.any (* unit -> unit *)) : unit =
      cache#sync
        (fun () -> Js.Unsafe.fun_call callback [||])
  end


class ['a,'b] pure_cache ~(get : 'a -> 'b) =
object
  inherit ['a,'b] cache
  method info key = get key (* TODO: memoize results of calls to get *)
  method enqueue key = ()
  method sync k = k ()
end

class ['a,'b] init_cache ~(default : 'a -> 'b) ~(bind : (('a * 'b option) list -> unit) -> unit) =
object
  inherit ['a,'b] cache
  val h : ('a,'b) Hashtbl.t = Hashtbl.create 101
  method info key =
    try Hashtbl.find h key
    with Not_found -> default key

  val mutable synced = false
  method enqueue key = ()
  method sync k =
    if synced
    then k ()
    else
      bind
        (fun lxy ->
          List.iter
            (function
             | (x, Some y) -> Hashtbl.add h x y
             | (x, None) -> ())
            lxy;
          synced <- true;
          k ())
end
  
class ['a,'b] tabled_cache ~(default : 'a -> 'b) ~(bind : 'a list -> (('a * 'b option) list -> unit) -> unit) =
object (self)
  val h : ('a,'b option) Hashtbl.t = Hashtbl.create 1001
  method info (key : 'a) : 'b =
    try Common.unsome (Hashtbl.find h key)
    with _ -> self#enqueue key; default key

  val mutable todo : ('a,unit) Hashtbl.t = Hashtbl.create 101
  method enqueue (key : 'a) : unit =
    if not (Hashtbl.mem todo key || Hashtbl.mem h key)
    then Hashtbl.add todo key ()
  method sync (k : unit -> unit) : unit =
    if Hashtbl.length todo = 0
    then k ()
    else begin
      let l_key = Hashtbl.fold (fun key () res -> key::res) todo [] in
      bind l_key
	(fun l_key_info_opt ->
	  List.iter
	    (fun (key,info_opt) -> Hashtbl.add h key info_opt)
	    l_key_info_opt;
	  Hashtbl.clear todo;
	  k ())
    end
end
