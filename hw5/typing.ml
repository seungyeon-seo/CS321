open Tml

exception TypeError

(* val createEmptyContext : unit -> context
val typing : context -> Tml.exp -> Tml.tp
val typeOf : Tml.exp -> Tml.tp
val typeOpt : Tml.exp -> Tml.tp option *)

(***************************************************** 
 * replace unit by your own type for typing contexts *
 *****************************************************)
type context = unit
(* (string * int * term) list *)

(*
 * For each function you introduce, 
 * write its type, specification, and invariant. 
 *)

let createEmptyContext () = raise TypeError 

(* val typing : context -> Tml.exp -> Tml.tp *)
let typing cxt e = raise TypeError

let typeOf e = typing (createEmptyContext ()) e 
let typeOpt e = try Some (typeOf e) 
                with TypeError -> None
