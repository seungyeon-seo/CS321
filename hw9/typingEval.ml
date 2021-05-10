open Fjava

exception NotImplemented
exception TypeError
exception Stuck
exception NotFound

(* classname -> classDecl list -> classDecl *)
let rec getCls c clsDecl =
  match clsDecl with
  | [] -> raise NotFound
  | h::t ->
    let (cls, _, _, _, _) = h in
    if cls = c then h else getCls c t

(* classname -> classname -> bool *)
let rec isSubclass a b clsDecl =
  let (_, sup, _, _, _) = try getCls a clsDecl with | NotFound -> false in
  if sup = b then true else isSubClass sup b clsDecl

(* classname -> classDecl list -> fields: (classname, fieldname) list *)
let rec fields c clsDecl =
  let (_, d, (c_, f_), _, _) = getCls c clsDecl in
  let flist = fields d clsDecl in
  (c_, f_)::flist

(* check if flist in plist *)
let rec checkList plist flist =
  match flist with
  | [] -> true
  | (a, b)::t ->
    if List.mem a plist
    then (if (List.assoc a plist) = b then checkList plist t else false)
    else false

(* exp -> env(string * typ list) -> classDecl list *)
let exp_typing e env clsDecl = raise NotImplemented

(* methodDecl -> classDecl -> classDecl list -> bool *)
let t_method m' cls clsDecl =
  let (c0, m, (c_, x_), e0) = m' in
  let (c, d, _, _, _) = cls in
  if override m d, (c_, c0) then
  (let env = (x_, c_)::(m, c) in
  let e0t = exp_typing e0 env clsDecl in
  isSubclass e0t c0
  )
  else false

(* methodDecl list -> classDecl -> classDecl list -> bool *)
let rec t_methods mlist c clsDecl =
  match mlist with
  | [] -> true
  | m::t ->
    if t_method m c clsDecl then t_methods t c clsDecl else false

(* classDecl -> bool *)
let t_class cls clsDecl = 
  let (c, d, flist, k, m_) = cls in
  let (c_, f_) = List.split flist in
  let (concls, plist, arglist, assignlist) = constr in
  if concls <> c then false else
    (* let (d_, g_) = List.split (fields d clsDecl) in *)
    let flist = fields d clsDecl in
    if checkList plist flist then t_methods mlist cls clsDecl else false

let typeOf p = raise NotImplemented

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
