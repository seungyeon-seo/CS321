open Fjava

exception NotImplemented
exception TypeError
exception Stuck
exception NotFound


let rec isSubClass a b l =
  let rec findCdec c l =
    match l with
    | [] -> raise NotFound
    | h::t ->
      let (cls, su, _, _, _) = h in
      if (cls = c) then h else findCdec c t
  in
  let (cl, super, _, _, _) = a in
  if cl = b then true
  else if super = b then true
  else try isSubClass (findCdec super l) b with | NotFound -> false

let rec isSubClass2 alist blist l =
  match (alist, blist) with
  | [] -> true
  | (a::at, b::bt) ->
    if isSubClass a b l then isSubClass2 at bt l else false


let rec fields c clDlist =
  match clDlist with
  | [] -> rasie NotFound
  | (cls, _, flist, _, _)::t ->
    if c = cls then flist else fields c t

let rec mtype m c0 clDlist =
  let rec mtype2 m mlist =
    match mlist with
    | [] -> mtype m sup clDlist
    | (rt, mn, plist, body)::t ->
      if mn = m then
      let b_ = List.map (fun (x,y) -> x) plist in
      (b_, rt) else mtype2 m t
  in
  match clDlist with
  | [] -> raise NotFound
  | (cls, sup, _, conDlist, mlist)::t ->
    if c0 = cls then mtype2 m mlist

let rec typeOfexps elist clDlist res =
  match elist with
  | [] -> res
  | e::t ->
    typeOfexps t clDlist res@[(typeOf (clDlist, e)]

(* Fjava.program -> Fjava.typ *)
let rec typeOf p =
  let (clDlist, exp) = p in
  match exp with
  (* T-Var *)
  | Var v -> v
  | Field (e', s) ->
    (* T-Field *)
    let flist = fields (typeOf (clDlist, e')) clDlist in
    List.asso s (List.map (fun (x,y) -> (y,x)) flist)
  | Method (e0, m, e_) ->
    (* T-Invk *)
    let c0 = typeOf (clDlist, e0) in
    let c_ = typeOfexps e_ clDlist [] in 
    let (d_, c) = mtype m c0 clDlist in
    if isSubClass2 c_ d_ clDlist then c else raise TypeError
  | New (c, e_) -> 
    (* T-New *)
    let flist = fields c clDlist in
    let d_ = List.map (fun (x,y) -> x) flist in
    let c_ = typeOfexps e_ clDlist [] in
    if isSubClass2 c_ d_ then c else raise TypeError
  | Cast (t, e') ->


let step p = raise NotImplemented

let typeOpt p = try Some (typeOf p) with TypeError -> None
let stepOpt p = try Some (step p) with Stuck -> None
let rec multiStep p = try multiStep (step p) with Stuck -> p

let rec stepStream e =
  let rec steps e =
    match stepOpt e with
        None -> Stream.from (fun _ -> None)
      | Some e' -> Stream.icons e' (steps e')
  in Stream.icons e (steps e)
