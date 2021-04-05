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
let rec isElement cxt x t =
    match cxt with
    | Empty -> false
    | Next (cxt', (x', t')) -> if x=x' then t=t' else isElement cxt' x t

(* val typing : context -> Tml.exp -> Tml.tp *)
let typing cxt e = raise TypeError
    (* match e with
    | Var x -> isElement *)

let typeOf e = typing (createEmptyContext ()) e 
let typeOpt e = try Some (typeOf e) 
                with TypeError -> None
