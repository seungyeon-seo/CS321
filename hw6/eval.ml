open Tml
exception NotImplemented 
exception Stuck
exception NotConvertible

type stoval = 
    Computed of value 
  | Delayed of exp * env

 and stack =
   Hole_SK
   | Frame_SK of stack * frame

 and state =
   Anal_ST of (stoval Heap.heap) * stack * exp * env
   | Return_ST of (stoval Heap.heap) * stack * value 

 (* Define your own datatypes *)
 and env = NOT_IMPLEMENT_ENV
 and value = NOT_IMPLEMENT_VALUE
 and frame = NOT_IMPLEMENT_FRAME

(* Define your own empty environment *)
let emptyEnv = NOT_IMPLEMENT_ENV

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let value2exp _ = raise NotImplemented

(* Problem 1. 
 * texp2exp : Tml.texp -> Tml.exp *)  

let rec fvariable e= 
  let union l1 l2 =
    let rec uni l1 l2 =
    match l2 with
    | [] -> l1
    | h::t ->
      if List.mem h l1 
      then uni (h::(List.filter (fun x -> h<>x) l1)) t
      else uni (h::l1) t
    in
    uni l1 (List.rev l2)
  in
  let rec fvar e =
    match e with
    | Tvar x -> [x]
    | Tlam (x, t, e') ->
      List.filter (fun v -> x<>v) (fvar e')
    | Tapp (e1, e2) ->
      union (fvar e1) (fvar e2)
    | Tpair (e1, e2) ->
      union (fvar e1) (fvar e2)
    | Tfst e' -> fvar e'
    | Tsnd e' -> fvar e'
    | Teunit -> []
    | Tinl (e', t) -> fvar e'
    | Tinr (e', t) ->fvar e'
    | Tcase (e', x1, e1, x2, e2) ->
      let fe' = fvar e' in
      let fe1 = List.filter (fun v -> x1<>v) (fvar e1) in
      let fe2 = List.filter (fun v -> x2<>v) (fvar e2) in
      union (union fe' fe1) fe2
    | Tfix (x, t, e') ->
      List.filter (fun v -> x<>v) (fvar e')
    | Ttrue -> []
    | Tfalse -> []
    | Tifthenelse (e', e1, e2) ->
      union (union (fvar e') (fvar e1)) (fvar e2)
    | Tnum i -> []
    | Tplus -> []
    | Tminus -> []
    | Teq -> []
  in
  fvar e

let texp2exp e = 
  let rec texp2exp' e naming =
    let n = List.length naming in
    match e with
    | Tvar x ->
      Ind (n - 1 - (try List.assoc x naming with Not_found -> 0))
    | Tlam (x, t, e') ->
      Lam (texp2exp' e' (naming@[x, n]))
    | Tapp (e1, e2) ->
      App ((texp2exp' e1 naming), (texp2exp' e2 naming))
    | Tpair (e1, e2) ->
      Pair ((texp2exp' e1 naming), (texp2exp' e2 naming))
    | Tfst e' ->
      Fst (texp2exp' e' naming)
    | Tsnd e' ->
      Snd (texp2exp' e' naming)
    | Teunit ->
      Eunit
    | Tinl (e', t) ->
      Inl (texp2exp' e' naming)
    | Tinr (e', t) ->
      Inr (texp2exp' e' naming)
    | Tcase (e', x1, e1, x2, e2) ->
      let ne' = texp2exp' e' naming in
      let ne1 = texp2exp' e1 (naming@[(x1, n)]) in
      let ne2 = texp2exp' e2 (naming@[(x2, n)]) in
      Case (ne', ne1, ne2)
    | Tfix (x, t, e') ->
      Fix (texp2exp' e' (naming@[(x, n)]))
    | Ttrue -> True
    | Tfalse -> False
    | Tifthenelse (e', e1, e2) ->
      let ne' = texp2exp' e' naming in
      let ne1 = texp2exp' e1 naming in
      let ne2 = texp2exp' e2 naming in
      Ifthenelse (ne', ne1, ne2)
    | Tnum i -> Num i
    | Tplus -> Plus
    | Tminus -> Minus
    | Teq -> Eq
  in
  let rec makePair list n res = 
    match list with
    | [] -> res
    | h::t -> makePair t (n-1) (res@[(h, n)])
  in
  let fr = fvariable e in
  let free = makePair fr ((List.length fr)-1) [] in
  texp2exp' e free

(* Problem 2. 
 * step1 : Tml.exp -> Tml.exp *)   
let rec step1 e = raise Stuck

(* Problem 3. 
 * step2 : state -> state *)
let step2 _ = raise NotImplemented
                    
(* exp2string : Tml.exp -> string *)
let rec exp2string exp = 
  match exp with 
    Ind x -> string_of_int x
  | Lam e -> "(lam. " ^ (exp2string e) ^ ")"
  | App (e1, e2) -> "(" ^ (exp2string e1) ^ " " ^ (exp2string e2) ^ ")"
  | Pair (e1, e2) -> "(" ^ (exp2string e1) ^ "," ^ (exp2string e2) ^ ")"
  | Fst e -> "(fst " ^ (exp2string e) ^ ")"
  | Snd e -> "(snd " ^ (exp2string e) ^ ")"
  | Eunit -> "()"
  | Inl e -> "(inl " ^ (exp2string e) ^ ")"
  | Inr e -> "(inr " ^ (exp2string e) ^ ")"
  | Case (e, e1, e2) -> "(case " ^ (exp2string e) ^" of " ^ (exp2string e1) ^
                          " | " ^ (exp2string e2) ^ ")"
  | Fix e -> "fix. "  ^ (exp2string e) ^ ")"
  | Ifthenelse (e, e1, e2) -> 
     "(if " ^ (exp2string e) ^ " then " ^ (exp2string e1) ^ 
       " else " ^ (exp2string e2) ^ ")"
  | True -> "true"  | False -> "false"
  | Num n -> "<" ^ (string_of_int n) ^ ">"
  | Plus -> "+"  | Minus -> "-" | Eq -> "="

(* state2string : state -> string 
 * you may modify this function for debugging your code *)
let state2string st = match st with
    Anal_ST(_,_,exp,_) -> "Analysis : ???"
  | Return_ST(_,_,_) -> "Return : ??? "

(* ------------------------------------------------------------- *)     
let stepOpt1 e = try Some (step1 e) with Stuck -> None
let stepOpt2 st = try Some (step2 st) with Stuck -> None

let rec multiStep1 e = try multiStep1 (step1 e) with Stuck -> e
let rec multiStep2 st = try multiStep2 (step2 st) with Stuck -> st

let stepStream1 e =
  let rec steps e = 
    match (stepOpt1 e) with
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

let stepStream2 st =
  let rec steps st = 
    match (stepOpt2 st) with
      None -> Stream.from (fun _ -> None)
    | Some st' -> Stream.icons st' (steps st')
  in 
  Stream.icons st (steps st)
