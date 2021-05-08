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

(* Fjava.program -> Fjava.typ *)
let typeOf p =


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
