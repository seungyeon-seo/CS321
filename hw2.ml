exception NotImplemented
	    
type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree
						      
(** Recursive functions **)

let rec lconcat list =
  match list with
  | [] -> []
  | h::t -> match t with
            | [] -> h
            | hh::tt -> lconcat ((h@hh)::tt)

let rec lfoldl f e list =
  match list with
  | [] -> e
  | h::t -> lfoldl f (f (h, e)) t

(** Tail recursive functions  **)

let fact n =
  let rec fact_aux num acc =
    if num = 1 then acc
    else fact_aux (num-1) (acc*num)
  in
  if n = 0 then 1
  else fact_aux n 1

let power x n =
  let rec power_aux x n acc =
    if n = 0 then acc
    else power_aux x (n-1) (acc*x)
  in
  if n = 0 then 1
  else power_aux x n 1

let fib n =
  let rec fib_aux n i pre cur =
    if n = i then cur
    else fib_aux n (i+1) cur (pre+cur)
  in
  if n = 0 then 1
  else if n = 1 then 1
  else fib_aux n 1 1 1

let lfilter p l =
  let rec lfilter_aux p src res =
    match src with 
    | [] -> res
    | h::t -> if (p h) then lfilter_aux p t (res@[h])
              else lfilter_aux p t res
  in
  lfilter_aux p l []

let ltabulate n f =
  let rec ltabulate_aux n f res =
    if n = 0 then (f n)::res
      else ltabulate_aux (n-1) f ((f n)::res)
  in
  ltabulate_aux (n-1) f []

let rec union l1 l2 =
  let rec find_ele list e =
    match list with
    | [] -> false
    | h::t -> if h = e then true
              else find_ele t e
  in
  match l2 with
  | [] -> l1
  | h::t -> if (find_ele l1 h) then union l1 t
            else union (h::l1) t

let inorder t =
  let rec inorder_aux t list roots tlist =
    match t with
    | Leaf v ->
      (match tlist with
      | [] -> list@[v]@roots
      | hh::tt -> 
        (match roots with
        | [] -> inorder_aux hh (list@[v]@roots) [] tt
        | hhh::ttt -> inorder_aux hh (list@[v; hhh]) ttt tt))
    | Node (l, y, r) ->
      (match l with
      | Leaf vv -> inorder_aux r (list@[vv; y]) roots tlist
      | Node (ll, yy, rr) -> inorder_aux l list (y::roots) (r::tlist))
  in
  match t with
  | Leaf v -> [v]
  | Node (ll, yy, rr) -> inorder_aux t [] [] []

let postorder t =
  let rec postorder_aux t list roots tlist n =
    let rec getele l n res =
      match l with
      | [] -> res
      | h1::t1 -> if n = 1 then res@[h1]
                  else getele t1 (n-1) (res@[h1])
    in
    let rec getele2 l n =
      match l with
      | [] -> l
      | h1::t1 -> if n = 1 then t1
                  else getele2 t1 (n-1)
    in
    match t with
    | Leaf v ->
      (match tlist with
      | [] -> list@[v]@roots
      | hh::tt ->
        (match tt with
        | [] ->
          (match roots with
          | [] -> postorder_aux hh (list@[v]) [] [] n
          | hhh::ttt -> postorder_aux hh (list@[v]@(getele roots n [])) (getele2 roots n) [] 1)
        | h4::t4 ->
          (match roots with
          | [] -> postorder_aux hh (list@[v]@roots) [] tt n
          | hhh::ttt -> postorder_aux hh (list@[v; hhh]) ttt tt n)))
    | Node (l, y, r) ->
      (match l with
      | Leaf vv -> postorder_aux r (list@[vv]) (y::roots) tlist n
      | Node (ll, yy, rr) -> postorder_aux l list (y::roots) (r::tlist) (n+1))
  in
  match t with
  | Leaf v -> [v]
  | Node (ll, yy, rr) -> postorder_aux t [] [] [] 0

let preorder t =
  let rec preorder_aux t list tlist =
    match t with
    | Leaf v ->
      (match tlist with
      | [] -> list@[v]
      | hh::tt -> preorder_aux hh (list@[v]) tt)
    | Node (l, y, r) ->
      (match l with
      | Leaf vv -> preorder_aux r (list@[y; vv]) tlist
      | Node (ll, yy, rr) -> preorder_aux l (list@[y]) (r::tlist))
  in
  match t with
  | Leaf v -> [v]
  | Node (ll, yy, rr) -> preorder_aux t [] []
		       
(** Sorting in the ascending order **)

let rec quicksort l =
  let rec getless p list res =
    match list with
    | [] -> res
    | h::t -> if h < p then getless p t (h::res)
              else getless p t res
  in
  let rec getmore p list res =
    match list with
    | [] -> res
    | h::t -> if h < p then getmore p t res
              else getmore p t (h::res)
  in
  match l with
  | [] -> l
  | h::t -> (quicksort (getless h t []))@[h]@(quicksort (getmore h t []))

let rec mergesort l =
  let rec getlength l n =
    match l with
    | [] -> n
    | h::t -> getlength t (n+1)
  in
  let rec conquer l1 l2 =
    match (l1, l2) with
    | (_, []) -> l1
    | ([], _) -> l2
    | (h1::t1, h2::t2) -> 
      if h1 <= h2 then h1::(conquer t1 l2)
      else h2::(conquer l1 t2)
  in
  let rec divide list =
    match list with
    | [] -> ([], [])
    | h::t ->
      match t with
      | [] -> (list, [])
      | hh::tt ->
        let (l1, l2) = divide t in
        if (getlength l1 0) <= (getlength l2 0) then (h::l1, l2)
        else (l1, h::l2)
  in
  match l with
  | [] -> l
  | [x] -> l
  | h::t ->
    let (l1, l2) = divide l in
    conquer (mergesort l1) (mergesort l2)

(** Structures **)

module type HEAP = 
  sig
    exception InvalidLocation
    type loc
    type 'a heap
    val empty : unit -> 'a heap
    val allocate : 'a heap -> 'a -> 'a heap * loc
    val dereference : 'a heap -> loc -> 'a 
    val update : 'a heap -> loc -> 'a -> 'a heap
  end
    
module type DICT =
  sig
    type key
    type 'a dict
    val empty : unit -> 'a dict
    val lookup : 'a dict -> key -> 'a option
    val delete : 'a dict -> key -> 'a dict
    val insert : 'a dict -> key * 'a -> 'a dict 
  end

module Heap : HEAP =
  struct
    exception InvalidLocation 
		
    type loc = int       (* dummy type, to be chosen by students *) 
    type 'a heap = (loc * 'a) list   (* dummy type, to be chosen by students *)
  
    let empty () = []

    let allocate h v =
      let newloc = List.length h + 1 in 
      ((newloc, v)::h, newloc)

    let dereference h l =
      if l > List.length h then raise InvalidLocation
      else
      let (loc, v) = List.nth h (l-1) in
      v

    let update h l v =
      if l > List.length h then raise InvalidLocation
      else
      let (left, right) = List.partition (fun (x, y) -> if x < l then true else false) h in
      left@[(l,v)]@right
  end
    
module DictList : DICT with type key = string =
  struct
    type key = string
    type 'a dict = (key * 'a) list
			      
    let empty () = []
    let rec lookup d k =
      match d with
      | [] -> None
      | h::t ->
        match h with
        | (k1, v1) -> if k = k1 then Some v1
                      else lookup t k

    let delete d k =
      let v = lookup d k in
      if v = None then d
      else let f (k1, _) = if k1 <> k then true else false in
      List.filter f d
     
    let insert d (k, v) =
      (delete d k)@[(k, v)]

  end
    
module DictFun : DICT with type key = string =
  struct
    type key = string
    type 'a dict = key -> 'a option
			     
    let empty () = fun x -> None
    let lookup d k = d k

    let delete d k =
      if (d k) = None then d
      else empty ()

    let insert d (k, v) =
      fun x -> if x = k then Some v else None

  end
