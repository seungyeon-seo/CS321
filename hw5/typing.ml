open Tml

exception TypeError

(* val createEmptyContext : unit -> context
val typing : context -> Tml.exp -> Tml.tp
val typeOf : Tml.exp -> Tml.tp
val typeOpt : Tml.exp -> Tml.tp option *)

(***************************************************** 
 * replace unit by your own type for typing contexts *
 *****************************************************)
type context = Empty | Next of context * (Tml.var * Tml.tp)

(*
 * For each function you introduce, 
 * write its type, specification, and invariant. 
 *)

let createEmptyContext () = raise TypeError 

(* if x:t in cxt then true else false *)
let rec isElement cxt x=
    match cxt with
    | Empty -> raise TypeError
    | Next (cxt', (x', t)) -> if x=x' then t else isElement cxt' x

(* val typing : context -> Tml.exp -> Tml.tp *)
let rec typing cxt e =
    match e with
    | Var x -> isElement cxt x (* Var *)
    | Lam (x, t, e') -> (* ->I *)
        let b = typing (Next (cxt, (x, t))) e' in Fun (t, b)
    | App (e1, e2) ->
        let t1 = typing cxt e1 in
        let t2 = typing cxt e2 in
        (match t1 with
        | Fun (t11, t12) -> if t11=t2 then t12 (* ->E *)
                            else raise TypeError (*TODO*)
        | _ -> raise TypeError)(*TODO*)
    | Pair (e1, e2) -> (* xI *)
        let t1 = typing cxt e1 in
        let t2 = typing cxt e2 in
        Prod (t1, t2)
    | Fst e' -> (* xE1 *)
        (match (typing cxt e') with
        | Prod (t1, t2) -> t1
        | _ -> raise TypeError) (*TODO*)
    | Snd e' -> (* xE2 *)
        (match (typing cxt e') with
        | Prod (t1, t2) -> t2
        | _ -> raise TypeError) (*TODO*)
    | Eunit -> Unit (* Unit *)
    | Inl (e', t2) -> (* +IL *)
        let t1 = typing cxt e' in
        Sum (t1, t2)
    | Inr (e', t1) -> (* +IR *)
        let t2 = typing cxt e' in
        Sum (t1, t2)
    | Case (e', x1, e1, x2, e2) -> (* +E *)
        let t = typing cxt e' in
        (match t with
        | Sum (a1, a2) ->
            let t1 = typing (Next (cxt, (x1, a1))) e1 in
            let t2 = typing (Next (cxt, (x2, a2))) e2 in
            if t1=t2 then t1 else raise TypeError
        | _ -> raise TypeError )
    | Fix (x, a, e') -> (* Fix *)
        if (typing (Next (cxt, (x, a))) e') = a then a else raise TypeError
    | True -> Bool (* True *)
    | False -> Bool (* False *)
    | Ifthenelse (e', e1, e2) -> (* If *)
        if (typing cxt e') <> Bool then raise TypeError else
        let t1 = typing cxt e1 in
        let t2 = typing cxt e2 in
        if t1=t2 then t1 else raise TypeError
    | Plus -> Fun (Prod (Int, Int), Int) (* Plus *)
    | Minus -> Fun (Prod (Int, Int), Int) (* Minus *)
    | Eq -> Fun (Prod (Int, Int), Bool) (* Eq *)

let typeOf e = typing (createEmptyContext ()) e 
let typeOpt e = try Some (typeOf e) 
                with TypeError -> None
