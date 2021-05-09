type typ = string
type exp =
    Var of string
  | Field of exp * string
  | Method of exp * string * exp list
  | New of typ * exp list
  | Cast of typ * exp

(* Return Type, Method Name, Parameters, Method Body *)
(* M ::= C m (C_ x_) {return e;} *)
type methodDecl = typ * string * (typ * string) list * exp

(* Class Name, Parameters, Arguments of super(), Assignments *)
(* K ::= C(C_ f_) {super(f_); this.f_ = f_;} *)
type constructorDecl = typ * (typ * string) list * string list * (string * string) list

(* Class Name, Super Class, Fields, Constructor, Methods *)
(* CL ::= class C extends C {C_ f_; K M_} *)
type classDecl = typ * typ * (typ * string) list * constructorDecl * (methodDecl list)

(* Classes, Expression *)
type program = classDecl list * exp
