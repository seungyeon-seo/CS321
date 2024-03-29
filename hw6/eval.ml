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
 and env = Eenv of Heap.loc list

 and value = 
  | VInd of index * env
  | VLam of exp * env
  | VPair of exp * exp * env
  | VEunit
  | VInl of exp * env
  | VInr of exp * env
  | VTrue
  | VFalse
  | VNum of int * env
  | VPlus
  | VMinus
  | VEq

 and frame =
  | FApp of env * exp
  | Floc of Heap.loc
  | FIf of env * exp * exp
  | FLam of env * exp

(* Define your own empty environment *)
let emptyEnv = Eenv (Heap.empty)

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let value2exp v =
  match v with
  | VEunit -> Eunit
  | VTrue -> True
  | VFalse -> False
  | VNum (i, _) -> Num i
  | _ -> raise NotConvertible

(* Problem 1. 
 * texp2exp : Tml.texp -> Tml.exp *)  

let rec fvariable e= 
  let union l1 l2 =
    let rec uni l1 l2 =
    match l2 with
    | [] -> l1
    | h::t -> uni (h::(List.filter (fun x -> h<>x) l1)) t
    in
    uni l1 (List.rev l2)
  in
  let rec fvar e =
    match e with
    | Tvar x -> [x]
    | Tlam (x, t, e') ->
      List.filter (fun v -> x<>v) (fvar e')
    | Tapp (e1, e2) ->
      union (fvar e1) (fvariable e2)
    | Tpair (e1, e2) ->
      union (fvar e1) (fvariable e2)
    | Tfst e' -> fvar e'
    | Tsnd e' -> fvar e'
    | Teunit -> []
    | Tinl (e', t) -> fvar e'
    | Tinr (e', t) ->fvar e'
    | Tcase (e', x1, e1, x2, e2) ->
      let fe' = fvar e' in
      let fe1 = List.filter (fun v -> x1<>v) (fvariable e1) in
      let fe2 = List.filter (fun v -> x2<>v) (fvariable e2) in
      union (union fe' fe1) fe2
    | Tfix (x, t, e') ->
      List.filter (fun v -> x<>v) (fvar e')
    | Ttrue -> []
    | Tfalse -> []
    | Tifthenelse (e', e1, e2) ->
      union (union (fvar e') (fvariable e1)) (fvariable e2)
    | Tnum i -> []
    | Tplus -> []
    | Tminus -> []
    | Teq -> []
  in
  fvar e

let rec getOrder ele list res =
  match list with
  | [] -> -1
  | h::t ->
    if h=ele then res else getOrder ele t (res+1)

let rec texp2exp e = 
  let rec texp2exp' e naming =
    match e with
    | Tvar x ->
      Ind (getOrder x naming 0)
      (* Ind (n-1-(List.assoc x naming)) *)
    | Tlam (x, t, e') ->
      Lam (texp2exp' e' (x::naming))
      (* Lam (texp2exp' e' (naming@[(x, n)])) *)
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
      (* let ne1 = texp2exp' e1 (naming@[(x1, n)]) in *)
      let ne1 = texp2exp' e1 (x1::naming) in
      (* let ne2 = texp2exp' e2 (naming@[(x2, n)]) in *)
      let ne2 = texp2exp' e2 (x2::naming) in
      Case (ne', ne1, ne2)
    | Tfix (x, t, e') ->
      Fix (texp2exp' e' (x::naming))
      (* Fix (texp2exp' e' (naming@[(x, n)])) *)
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
  let fr = fvariable e in
  texp2exp' e fr

(* Problem 2. 
 * step1 : Tml.exp -> Tml.exp *)   

let rec isValue e =
  match e with
    | Ind i -> true
    | Lam e' -> true
    | App (e1, e2) -> false
    | Pair (e1, e2) -> (isValue e1)&&(isValue e2)
    | Fst e' -> false
    | Snd e' -> false
    | Eunit -> true
    | Inl e' -> isValue e'
    | Inr e' -> isValue e'
    | Case (e', e1, e2) -> false
    | Fix e' -> false
    | True -> true
    | False -> true
    | Ifthenelse (e', e1, e2) -> false
    | Num i -> true
    | Plus -> true
    | Minus -> true
    | Eq -> true

let rec shift i n m =
  match m with
  | App (m1, m2) ->
    App (shift i n m1, shift i n m2)
  | Lam m' ->
    Lam (shift (i+1) n m')
  | Ind j ->
    if j<i then Ind j else Ind (j+n)
  | Pair (m1, m2) ->
    Pair (shift i n m1, shift i n m2)
  | Fst m' -> Fst (shift i n m')
  | Snd m' -> Snd (shift i n m')
  | Eunit -> m
  | Inl m' -> Inl (shift i n m')
  | Inr m' -> Inr (shift i n m')
  | Case (m', m1, m2) ->
    Case (shift i n m', shift (i+1) n m1, shift (i+1) n m2)
  | Fix m' -> Fix (shift i n m')
  | True -> m
  | False -> m
  | Ifthenelse (m', m1, m2) ->
    Ifthenelse (shift i n m', shift (i+1) n m1, shift (i+1) n m2)
  | Num i -> m
  | Plus -> m
  | Minus -> m
  | Eq -> m
  | _ -> m

(* [m/i]n *)
let rec substitution m i n =
  match n with
  | Ind j ->
    if i>j then Ind j
    else if i<j then Ind (j-1)
    else shift 0 i m
  | Lam n' ->
    Lam (substitution m (i+1) n')
  | App (n1, n2) ->
    App ((substitution m i n1), (substitution m i n2))
  | Pair (n1, n2) ->
    Pair ((substitution m i n1), (substitution m i n2))
  | Inl n' ->
    Inl (substitution m i n')
  | Inr n' ->
    Inr (substitution m i n')
  | Case (n', n1, n2) ->
    Case ((substitution m i n'), (substitution m (i+1) n1), (substitution m (i+1) n2))
  | Fix n' ->
    Fix (substitution m (i+1) n')
  | Ifthenelse (n', n1, n2) ->
    Ifthenelse ((substitution m i n'), (substitution m i n1), (substitution m i n2))
  | Fst n' -> Fst (substitution m i n')
  | Snd n' -> Snd (substitution m i n')
  (* Values *)
  | _ -> n

let rec step1 e =
  if isValue e then raise Stuck else
  match e with
    | App (e1, e2) ->
      (match e1 with
      | Lam e1' ->
        if isValue e2
        (* App *)
        then substitution e2 0 e1'
        (* Arg *)
        else App(e1, step1 e2)
      | Plus ->
        (match e2 with
          (* Plus *)
          | Pair (Num i, Num j) -> Num (i+j)
          (* Arith *)
          | _ -> if isValue e2 then raise Stuck else App(e1, step1 e2)
        )
      | Minus ->
        (match e2 with
          (* Minus *)
          | Pair (Num i, Num j) -> Num (i-j)
          (* Arith *)
          | _ -> if isValue e2 then raise Stuck else App(e1, step1 e2)
        )
      | Eq ->
        (match e2 with
          (* Eq *)
          | Pair (Num i, Num j) ->
            if (i=j) then True else False
          (* Arith *)
          | _ -> if isValue e2 then raise Stuck else App(e1, step1 e2)
        )
      | _ ->
        (* Lam *)
        App(step1 e1, e2)
      )
    | Pair (e1, e2) ->
      if isValue e1
      (* Pair' *)
      then Pair(e1, step1 e2)
      (* Pair *)
      else Pair(step1 e1, e2)
    | Fst e' ->
      (match e' with
      | Pair (v1, v2) -> if (isValue v1)&&(isValue v2)
        (* Fst' *)
        then v1
        (* Fst *)
        else Fst(step1 e')
      | _ -> Fst (step1 e')
      )
    | Snd e' ->
      (match e' with
      | Pair (v1, v2) -> if (isValue v1)&&(isValue v2)
        (* Snd' *)
        then v2
        (* Snd *)
        else Snd(step1 e')
      | _ -> Snd (step1 e')
      )
    | Inl e' ->
    (* Inl *)
      Inl (step1 e')
    | Inr e' ->
    (* Inr *)
      Inr (step1 e')
    | Case (e', e1, e2) ->
      (match e' with
      | Inl v -> if isValue v
        (* Case' *)
        then substitution v 0 e1
        (* Case *)
        else Case (step1 e', e1, e2)
      | Inr v -> if isValue v
        (* Case'' *)
        then substitution v 0 e2
        (* Case *)
        else Case (step1 e', e1, e2)
      | _ -> Case (step1 e', e1, e2)
      )
    | Fix e' ->
      (* Fix *)
      substitution e 0 e'
    | Ifthenelse (e', e1, e2) ->
      (match e' with
      (* If True *)
      | True -> e1
      (* If False *)
      | False -> e2
      (* If *)
      | _ ->
        Ifthenelse (step1 e', e1, e2)
      )
    | _ -> raise Stuck

let getMem h en i =
  match en with
  | Eenv l ->
    try Heap.deref h (List.nth l i) with | Not_found -> raise Stuck


(* Problem 3. 
 * step2 : state -> state *)
let step2 s =
  match s with
  | Anal_ST (h, sk, exp, en) ->
    (match exp with
    | Ind i ->
      (* (match en with | Eenv(ll) ->
      let l = (List.hd ll) in
      let (h', l') = Heap.deref h l in
      (match l' with
      | Delayed(e', en') ->
        (* insert [li] to stack *)
        if (List.tl en) = en' then
        Anal_ST (h, Frame_SK(sk, Floc l), e', en')
        else
        (* Var_E *)
        let v = getMem h en i in
        Return_ST (h, sk, VInd(i, en))
      | _ -> let v = getMem h en i in Return_ST (h, sk, VInd(i, en))
      )) *)
      (* Var_E *)
      let v = getMem h en i in 
      Return_ST (h, sk, VInd(i, en))
    | Lam e' ->
      (* Closure_E *)
      Return_ST (h, sk, VLam(e', en))
    | App (e1, e2) ->
      (* Lam_E *)
      Anal_ST (h, Frame_SK (sk, FApp (en, e2)), e1, en)
    (* | Pair (e1, e2) ->
    | Fst e' ->
    | Snd e' ->
    | Eunit ->
    | Inl e' ->
    | Inr e' ->
    | Case (e', e1, e2) ->
    | Fix e' -> *)
    | True ->
      (* True_E *)
      Return_ST (h, sk, VTrue)
    | False ->
      (* False_E *)
      Return_ST (h, sk, VFalse)
    | Ifthenelse (e', e1, e2) ->
      (* If_E *)
      Anal_ST (h, Frame_SK(sk, FIf(en, e1, e2)), e', en)
    (* | Num i ->
    | Plus ->
    | Minus ->
    | Eq -> *)
    | _ -> raise Stuck
    )
  | Return_ST (h, sk, v) ->
    (match v with
    | VLam (e, en) ->
      (match sk with
      (* Arg_E *)
      | Frame_SK (sk', FApp(fen, fe)) ->
        Anal_ST (h, Frame_SK(sk', FLam(en, e)), fe, fen)
      | _ -> raise Stuck
      )
    | VTrue ->
      (* If True_E *)
      (match sk with
      | Frame_SK (sk', FIf (en', e1, e2)) ->
        Anal_ST (h, sk', e1, en')
      | _ -> raise Stuck
      )
    | VFalse ->
      (* If False_E *)
      (match sk with
      | Frame_SK (sk', FIf (en', e1, e2)) ->
        Anal_ST (h, sk', e2, en')
      | _ -> raise Stuck
      )
    | _ ->
      (* App_E (alloc) *)
      (match sk with
      | Frame_SK (sk', FLam(en', e')) ->
        let (h', l') = Heap.allocate h (Delayed(e', en')) in
        (* Anal_ST (h', sk', e', l'::en') *)
        Anal_ST (h', sk', e', en')
      | _ -> raise Stuck
      )
    )
                    
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
