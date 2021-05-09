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

let rec fields c clDlist =
  match clDlist with
  | [] -> rasie NotFound
  | (cls, _, flist, _, _)::t ->
    if c = cls then flist else fields c t

let rec mtype m c0 clDlist =
  match clDlist with
  | [] -> raise NotFound
  | (cls, _, _, _, mlist)::t ->
    if c0 = c then 
  (* match mlist with
  | [] -> raise NotFound
  | (ty, mname, plist, body)::t ->
    if c = mname then (plist, ty) else getTypeMethod c t *)

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
    (* T-Invk *) (* ?? D->C가 뭘까? *)
    let c0 = typeOf (clDlist, e0) in
    let mt = mtype m c0 in
    (* try let (d_, c) = getTypeMethod c0 flist with | NotFound -> raise TypeError in
    let c_ = in *)
    
  | New (t, l) -> 

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
