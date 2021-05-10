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

(* method name -> methodDecl list -> methodDecl *)
let rec getMthd m mlist =
  match mlist with
  | [] -> raise NotFound
  | h::t ->
    let (_, mn, _, _) = h in
    if mn = m then h else getMthd m t

(* classname -> classname -> classDecl list -> bool *)
let rec isSubclass a b clsDecl =
  let (_, sup, _, _, _) = try getCls a clsDecl with | NotFound -> false in
  if sup = b then true else isSubclass sup b clsDecl

(* classname list -> classname list -> classDecl list -> bool *)
let rec isSubclass2 a_ b_ clsDecl =
  match (a_, b_) with
  | ([], []) -> true
  | (a::at, b::bt) ->
    if isSubclass a b clsDecl then isSubclass2 at bt clsDecl else false

(* classname -> classDecl list -> fields: (classname, fieldname) list *)
let rec fields c clsDecl =
  let (_, d, (c_, f_), _, _) = getCls c clsDecl in
  let flist = fields d clsDecl in
  (c_, f_)::flist

(* check if flist in plist *)
(* (typ*string) list -> (typ*string) list -> bool *)
let rec checkList plist flist =
  match flist with
  | [] -> true
  | (a, b)::t ->
    if List.mem a plist
    then (if (List.assoc a plist) = b then checkList plist t else false)
    else false

(* methodname -> classname -> (typlist of parameters, return type)*)
let rec mtype m c clsDecl = 
  let (_, d, flist, k, mlist) = try getCls c clsDecl with | NotFound -> raise NotFound in
  let (b, _, plist, e) = try getMthd m mlist
                        with | NotFound -> mtype m d clsDecl in
  let (b_, _) = List.split plist in
  (b_, b)

(* exp -> env(string * typ list) -> classDecl list *)
(* let typeofexp e env clsDecl =
  match e with
  | Var x ->
    (* T-Var *)
    try List.assoc x env with | Not_found -> raise NotFound
  | Field (e0, f) ->
    try let c0 = List.assoc e0 env with | Not_found -> rasie NotFound in
    let (d_, c) = mtype m c0 clsDecl in
    typeofexps e_ env
  | Method (e0, m, e_) ->
  | New (c, e_) ->
  | Cast (c, e0) -> *)

(* methodname -> classname -> field type list -> m return type -> classDecl list -> bool *)
let override m d c_ c0 clsDecl =
  let (d_, d0) = try mtype m d with | NotFound -> true in
  if (isSubclass2 c_ d_)&&(isSubclass2 d_ c_)&&(c0 = d0) then true else false

(* methodDecl -> classDecl -> classDecl list -> bool *)
let t_method m' cls clsDecl =
  let (c0, m, flist, e0) = m' in
  let (c_, x_) = List.split flist in 
  let (c, d, _, _, _) = cls in
  if override m d c_ c0 clsDecl then
  (let env = (x_, c_)::(m, c) in
  let e0t = typeofexp e0 env clsDecl in
  isSubclass e0t c0
  )
  else false

(* methodDecl list -> classDecl -> classDecl list -> bool *)
let rec t_methods mlist c clsDecl =
  match mlist with
  | [] -> true
  | m::t ->
    if t_method m c clsDecl then t_methods t c clsDecl else false

(* classDecl -> classDecl list -> bool *)
let t_class cls clsDecl = 
  let (c, d, flist, k, m_) = cls in
  let (c_, f_) = List.split flist in
  let (concls, plist, arglist, assignlist) = constr in
  if concls <> c then false else
    (* let (d_, g_) = List.split (fields d clsDecl) in *)
    let flist = fields d clsDecl in
    if checkList plist flist then t_methods mlist cls clsDecl else false

(* Fjava.program -> Fjava.typ *)
let typeOf p = 
  let rec checkClass clsDecl =
    match clsDecl with
    | [] -> true
    | h::t -> if t_class h clsDecl then checkClass t else false
  in
  let (clsDecl, exp) = p in
  (* TODO: env? *)
  if checkClass then try typeofexp exp env clsDecl with | NotFound -> raise TypeError
  else raise TypeError
  

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
