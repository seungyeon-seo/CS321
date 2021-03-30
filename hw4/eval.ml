(*
 * Call-by-value reduction   
 *)
open Uml

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

let swapExp e x y =
    match e with 
    | Var x -> e
    | _ -> e
    (* TODO: implement swap function *)

let rec isAlphaEq e1 e2 =
  match (e1, e2) with
  | (Var x, Var y) -> if x=y then true else false
  | (Lam (x, e1'), Lam (y, e2')) ->
    if x<>y && ((isFreeVariable y e1')=false) && (isAlphaEq (swapExp e1' x y) e2') then true else false
  | (App (e11, e12), App (e21, e22)) ->
    if (isAlphaEq e11 e21) && (isAlphaEq e12 e22) then true else false
  | _ -> false

(* let rec stepv e = raise NotImplemented *)
let rec stepv e =
  let rec substitution e x e' =
  match e' with
  | Var y ->
    if x=y then e else Var y
  | Lam (y, e1) ->
    if x=y then Lam (y, e1)
    else if isFreeVariable y e then
      let z = getFreshVariable x in Lam (z, (substitution e x (swapExp e1 y (Var(z)))))
    else Lam (y, (substitution e x e1))
  | App (e1, e2) -> 
    (App ((substitution e x e1), (substitution e x e2)))
  in
  match e with
  | Var x -> raise Stuck
  | Lam (x, e') ->
    (match e' with
    | Var y -> e'
    | Lam (y, ee) -> Lam (y, (stepv ee))
    | App (e1, e2) -> Lam (x, e2))
  | App (e1, e2) -> 
    let e1' = stepv e1 in
    let e2' = stepv e2 in
    match (e1', e2') with
    | ((Lam (a, e11)), Var b) -> substitution e2' a e11 (* App: B-reduction *)
    | (Var a, _) -> Lam (a, e2') (* Arg *)
    | (_, _) -> App (e1', e2) (* Lam *)


(*
 * implement a single step with reduction using the call-by-name strategy.
 *)
let rec stepn e = stepv e    

let stepOpt stepf e = try Some (stepf e) with Stuck -> None

let rec multiStep stepf e = try multiStep stepf (stepf e) with Stuck -> e

let stepStream stepf e =
  let rec steps e = 
    match (stepOpt stepf e) with 
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

