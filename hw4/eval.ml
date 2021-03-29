(*
 * Call-by-value reduction   
 *)

exception NotImplemented 
exception Stuck

let freshVarCounter = ref 0
                          
(*   getFreshVariable : string -> string 
 *   use this function if you need to generate a fresh variable from s. 
 *)
let getFreshVariable s = 
  let _ = freshVarCounter := !freshVarCounter + 1
  in
  s ^ "__" ^ (string_of_int (!freshVarCounter))
               
(*
 * implement a single step with reduction using the call-by-value strategy.
 *)

let rec freeVariable e  =
  match e with
  | Var v -> [v]
  | Lam (v, e') -> List.filter (fun x -> x<>v) (freeVariable e')
  | App (e1, e2) -> (freeVariable e1)@(freeVariable e2)

let isFreeVariable v e =
  let fv = freeVariable e in
  if List.exists (fun x -> x=v) fv then true else false

(* let rec stepv e = raise NotImplemented *)
let rec stepv e =
   let rec substitution e x e' =
  match e' with
  | Var y ->
    if x=y then stepv e else y
  | Lam (y, e1) ->
    if x=y then 
  | App (e1, e2) -> 
    stepv (App ((substitution e x e1) (substitution e x e2)))
  in      
  match e with
  | Var x -> x
  | Lam (x, e') -> 


(*
 * implement a single step with reduction using the call-by-name strategy.
 *)
let rec stepn e = raise NotImplemented         

let stepOpt stepf e = try Some (stepf e) with Stuck -> None

let rec multiStep stepf e = try multiStep stepf (stepf e) with Stuck -> e

let stepStream stepf e =
  let rec steps e = 
    match (stepOpt stepf e) with 
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

