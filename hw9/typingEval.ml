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

(* method name -> methodDecl list -> (methodDecl, bool) *)
let rec getMthd m mlist =
  match mlist with
  | [] -> raise NotFound
  | h::t -> 
    let (_, mn, _, _) = h in
    if mn = m then h else getMthd m t

(* classname -> classname -> classDecl list -> bool *)
let rec isSubclass a b clsDecl =
  if a = b then true
  else if a = "Object" then false else
  let (_, sup, _, _, _) = getCls a clsDecl in
  (isSubclass sup b clsDecl)

(* classname list -> classname list -> classDecl list -> bool *)
let rec isSubclass2 a_ b_ clsDecl =
  match (a_, b_) with
  | ([], []) -> true
  | (a::at, b::bt) ->
    if try isSubclass a b clsDecl with NotFound -> false then isSubclass2 at bt clsDecl else false
  | (a::at, []) -> false
  | ([], _) -> false

(* classname -> classDecl list -> fields: (classname, fieldname) list *)
let rec fields c clsDecl =
  if c = "Object" then [] else
  let (_, d, fl, _, _) = getCls c clsDecl in
  let flist = try fields d clsDecl with | NotFound -> [] in
  fl@flist

(* check if flist in plist *)
(* (typ*string) list -> (typ*string) list -> bool *)
let rec checkList plist flist =
  match flist with
  | [] -> true
  | (a, b)::t ->
    if List.mem (a, b) plist
    then (if (List.assoc a plist) = b then checkList plist t else false)
    else false

(* methodname -> classname -> (typlist of parameters, return type)*)
let rec mtype m c clsDecl =
  if c = "Object" then ([], c) else
  let (_, d, _, k, mlist) = try getCls c clsDecl with | NotFound -> raise NotFound in
  if List.exists (fun (x, y, z, w) -> y = m) mlist then
    let (b, _, plist, e) = getMthd m mlist in
    let (b_, _) = List.split plist in (b_, b)
  else mtype m d clsDecl

(* exp -> env(string * typ list) -> classDecl list -> type list *)
let rec typeofexps elist env clsDecl res =
  let rec typeofexp e env clsDecl =
    match e with
    | Var x ->
      (* T-Var *)
      List.assoc x env

    | Field (e0, f) ->
      (* T-Field *)
      let c0 = typeofexp e0 env clsDecl in
      let (x, y) = List.split (fields c0 clsDecl) in
      let flist = List.combine y x in
      let c = List.assoc f flist in (* Not_found *)
      c

    | Method (e0, m, e_) ->
      (* T-Invk *)
      let c0 = typeofexp e0 env clsDecl in
      let (d_, c) = mtype m c0 clsDecl in
      let c_ = List.map (fun x -> typeofexp x env clsDecl) e_ in
      if (isSubclass2 c_ d_ clsDecl) then c
      else raise TypeError

    | New (c, e_) ->
      (* T-New *)
      let (d_, f_) = List.split (fields c clsDecl) in
      let c_ = List.map (fun x -> typeofexp x env clsDecl) e_ in
      if isSubclass2 c_ d_ clsDecl then c 
      else raise TypeError

    | Cast (c, e0) ->
      let d = typeofexp e0 env clsDecl in
      (* T-UCast *)
      if isSubclass d c clsDecl then c
      (* T-DCast *)
      else if isSubclass c d clsDecl then c
      (* T-SCast *)
      else let _ = print_endline "Stupid Warning" in c
  in
  match elist with
  | [] -> res
  | h::t -> try typeofexps t env clsDecl (res@[typeofexp h env clsDecl]) with Not_found -> raise TypeError

(* methodname -> classname -> field type list -> m return type -> classDecl list -> bool *)
let override m d c_ c0 clsDecl =
  let (d_, d0) = mtype m d clsDecl in
  if d0 = "Object" then true else  
  if (c0 = d0)&&(isSubclass2 c_ d_ clsDecl)&&(isSubclass2 d_ c_ clsDecl) then true 
  else false

(* methodDecl -> classDecl -> classDecl list -> bool *)
let t_method m' cls clsDecl =
  let (c0, m, flist, e0) = m' in
  let (c_, x_) = List.split flist in
  (* let fl = List.map (fun (x, y) -> (y, x)) flist in *)
  let fl = List.combine x_ c_ in
  let (c, d, _, _, _) = cls in
  if try override m d c_ c0 clsDecl with | NotFound -> false then
  (
  let e0t = List.hd (typeofexps [e0] (("this", c)::fl) clsDecl []) in
  isSubclass e0t c0 clsDecl
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
  let (concls, plist, arglist, assignlist) = k in
  if concls <> c then false else
    let fl = fields d clsDecl in
    if checkList plist fl then t_methods m_ cls clsDecl else false

(* Fjava.program -> Fjava.typ *)
let typeOf p = 
  let rec checkClass clist clsDecl =
    match clist with
    | [] -> true
    | h::t -> if (t_class h clsDecl) then (checkClass t clsDecl) else false
  in
  let (clsDecl, exp) = p in
  if try checkClass clsDecl clsDecl with | NotFound -> raise TypeError
  then List.hd (typeofexps [exp] [] clsDecl []) else raise TypeError




(* Problem 2 evaluation *)

(* exp -> bool *)
let rec isValue e =
  match e with
  | Var x -> false
  | Field (e0, f) -> false
  | Method (e0, m, e_) -> false
  | New (c, e_) -> 
    if List.exists (fun e' -> not (isValue e')) e_ then false else true
  | Cast (c, e0) -> false

(* [d_/x_, e/y]e0 *)
let rec subst d_ x_ e y e0 =
  match e0 with
  | Var x ->
    let l = List.combine x_ d_ in
    (try List.assoc x l with | Not_found -> e)
    (* (try Var (List.assoc e0 l) with | Not_found -> raise Stuck) *)
  | Field (e', f) ->
    Field ((subst d_ x_ e y e'), f)
  | Method (e', m, e_) ->
    let ne_ = List.map (fun x -> subst d_ x_ e y x) e_ in
    Method ((subst d_ x_ e y e'), m, ne_)
  | New (c, e_) ->
    let ne_ = List.map (fun x -> subst d_ x_ e y x) e_ in
    New (c, ne_)
  | Cast (c, e') ->
    Cast (c, (subst d_ x_ e y e'))

(* method name -> class name -> classDecl list -> (parameter string list, body) *)
let rec mbody m cls clsDecl = 
  let (c, d, flist, k, mlist) = try getCls cls clsDecl with NotFound -> raise Stuck in
  if List.exists (fun (x, y, z, w) -> y = m) mlist then
    let (_, _, plist, e) = getMthd m mlist in
    let (_, x_) = List.split plist in
    (x_, e)
  else mbody m d clsDecl

let rec findtoreduce e_ prev =
  match e_ with
  | [] -> raise NotFound
  | e::t ->
    if isValue e then findtoreduce t (prev@[e]) else (prev, e, t)

(* Fjava.program -> Fjava.program *)
let rec step p = 
  let rec stepexp exp clsDecl =
    match exp with
    | Var x -> raise Stuck
    | Field (e0, f) ->
      (* R-Field *)
      if isValue e0 then
        (match e0 with
        | Var x -> raise Stuck
        | New (c, e_) ->
          let (c_, f_) = List.split (fields c clsDecl) in
          let fe = List.combine f_ e_ in
          try List.assoc f fe with Not_found -> raise Stuck
        )
      (* RC-Field *)
      else 
      Field ((stepexp e0 clsDecl), f)
    | Method (e0, m, e_) ->
      if (isValue e0) then (
        if List.exists (fun x -> not (isValue x)) e_ then
          (* RC-Invk-Arg *)
          let (f, e, l) = findtoreduce e_ [] in
          Method (e0, m, (f@[(stepexp e clsDecl)]@l))
        (* R-Invk *)
        else 
          (match e0 with
          | Var x -> raise Stuck
          | New (c, es) ->
            let (x_, e0') = mbody m c clsDecl in
            subst e_ x_ e0 c e0'
          )
      )
      (* RC-Invk-Recv *)
      else 
      Method ((stepexp e0 clsDecl), m, e_)
    | New (c, e_) ->
      (* RC-New-Arg *)
      let (f, e, l) = findtoreduce e_ [] in
      New (c, (f@[(stepexp e clsDecl)]@l))
    | Cast (c, e0) ->
      (* R-Cast *)
      if isValue e0 then
      (match e0 with
      | Var x -> raise Stuck
      | New (c', e_) ->
        if isSubclass c c' clsDecl then e0 else raise Stuck
      )
      (* RC-Cast *)
      else 
      Cast (c, stepexp e0 clsDecl)
  in
  let (clsDecl, exp) = p in
  if isValue exp then raise Stuck else
  let e = stepexp exp clsDecl in
  (clsDecl, e)
  

let typeOpt p = try Some (typeOf p) with TypeError -> None
let stepOpt p = try Some (step p) with Stuck -> None
let rec multiStep p = try multiStep (step p) with Stuck -> p

let rec stepStream e =
  let rec steps e =
    match stepOpt e with
        None -> Stream.from (fun _ -> None)
      | Some e' -> Stream.icons e' (steps e')
  in Stream.icons e (steps e)
