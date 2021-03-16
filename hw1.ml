exception Not_implemented

type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree

let rec sum n =
    if n = 0 then 0
    else sum(n-1) + n

let rec fac n =
    if n = 1 then 1
    else fac(n-1) * n

let rec fib n =
    if n = 0 then 1
    else if n = 1 then 1
    else fib(n-1) + fib(n-2)

let rec gcd n m =
    if m = 0 then n
    else gcd(m) (n mod m)

let rec max list =
    match list with 
    | [] -> 0
    | h :: t -> match t with
                | [] -> h
                | hh :: tt -> if (h > hh) then max (h::tt)
                            else max t

let rec sum_tree tree = 
    match tree with
    | Leaf n -> n
    | Node (l, v, r) -> sum_tree l + v + sum_tree r

let rec depth tree = 
    match tree with 
    | Leaf n -> 0
    | Node (l, v, r) -> depth l + 1 + depth r

let rec bin_search tree element = 
    match tree with
    | Leaf n -> if n = element then true
                else false
    | Node (l, v, r) -> if v = element then true
                        else bin_search l element || bin_search r element

let rec preorder tree =
    match tree with 
    | Leaf n -> n :: []
    | Node (l, v, r) -> [v] @ preorder l @ preorder r

let rec list_add l1 l2 =
    match (l1, l2) with 
    | [], [] -> []
    | [], _ -> l2
    | _, [] -> l1
    | h::t, hh::tt -> [h+hh] @ list_add t tt
                
let rec insert element list = 
    match list with 
    | [] -> [element]
    | h::t -> if h > element then element :: list
              else h :: insert element t

let rec insort list =
    let rec insort2 sorted unsorted =
        match unsorted with 
        | [] -> sorted
        | h::t -> insort2 (insert h sorted) t
        in
    insort2 [] list

let rec compose f g =
    fun x -> g (f x)

let rec curry f x y =
    f (x, y)

let rec uncurry f args =
    match args with
    | (x, y) -> f x y

let rec multifun f n =
    fun x -> if n = 1 then f x
             else multifun f (n-1) (f x)

let rec ltake list n =
    if n = 0 then []
    else match list with
    | [] -> list
    | h::t -> [h] @ ltake t (n-1)

let rec lall f list =
    match list with
    | [] -> true
    | h::t -> if (f h) = false then false
            else lall f t

let rec lmap f list =
    match list with 
    | [] -> []
    | h::t -> (f h) :: (lmap f t)

let rec lrev list =
    match list with
    | [] -> []
    | h::t -> (lrev t) @ [h]

let rec lzip l1 l2 =
    match l1 with
    | [] -> []
    | h::t -> match l2 with
            | [] -> []
            | hh::tt -> [(h, hh)] @ (lzip t tt)

let rec split list =
    let rec split2 origin left right =
        match origin with
        | [] -> (left, right)
        | h::t -> match t with
                | [] -> (left@[h], right)
                | hh::tt -> split2 tt (left@[h]) (right@[hh])
        in
    match list with 
    | [] -> ([], [])
    | h::t -> split2 list [] []

let rec cartprod l1 l2 =
    let rec helper x list res =
        match list with
        | [] -> res
        | h::t -> helper x t (res@[(x, h)])
        in
    match l1 with
    | [] -> []
    | h::t -> (helper h l2 []) @ (cartprod t l2)
