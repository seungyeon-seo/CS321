open Common

exception NotImplemented

exception IllegalFormat

module Integer : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 0
  let one = 1

  let (++) x y = x + y
  let ( ** ) x y = x * y
  let (==) x y = x = y 
end

(* Problem 1-1 *)
(* Scalars *)

module Boolean : SCALAR with type t = bool 
=
struct
  type t = bool

  exception ScalarIllegal

  let zero = false
  let one = true

  let (++) x y =
    if x = one then one
    else if y = one then one
    else zero

  let ( ** ) x y =
    if x = zero then zero
    else if y = zero then zero
    else one

  let (==) x y =
    if x = y then one
    else zero
end

(* Problem 1-2 *)
(* Vectors *)

module VectorFn (Scal : SCALAR) : VECTOR with type elem = Scal.t
=
struct
  type elem = Scal.t
  type t = elem list

  exception VectorIllegal

  let create list = list
  let to_list v = v
  let dim v = List.length v
  let nth v n =
    if n >= (dim v) then raise VectorIllegal
    else List.nth v n
  
  let (++) x y =
    let rec vadder v1 v2 res =
      match (v1, v2) with
      | ([], _) -> res
      | (_, []) -> res
      | (h1::t1, h2::t2) -> vadder t1 t2 res@[(Scal.(++) h1 h2)]
    in
    let d1 = dim x in
    let d2 = dim y in 
    if d1 <> d2 then raise VectorIllegal
    else vadder x y []

  let (==) x y =
    let rec vequal v1 v2 =
      match (v1, v2) with
      | ([], _) -> true
      | (_, []) -> true
      | (h1::t1, h2::t2) -> if (Scal.(==) h1 h2) = false then false
                            else vequal t1 t2
    in
    let d1 = dim x in
    let d2 = dim y in
    if d1 <> d2 then raise VectorIllegal
    else vequal x y

  let innerp x y =
    let rec vmul v1 v2 res =
      match (v1, v2) with
      | ([], _) -> res
      | (_, []) -> res
      | (h1::t1, h2::t2) -> vmul t1 t2 (Scal.(++) res (Scal.( ** ) h1 h2))
    in
    let d1 = dim x in
    let d2 = dim y in
    if d1 <> d2 then raise VectorIllegal
    else
    match (x, y) with
      | ([], _) -> raise VectorIllegal
      | (_, []) -> raise VectorIllegal
      | (h1::t1, h2::t2) -> vmul t1 t2 (Scal.( ** ) h1 h2)

end

(* Problem 1-3 *)
(* Matrices *)

module MatrixFn (Scal : SCALAR) : MATRIX with type elem = Scal.t
=
struct
  type elem = Scal.t
  type t = unit

  exception MatrixIllegal

  let create _ = raise NotImplemented
  let identity _ = raise NotImplemented
  let dim _ = raise NotImplemented
  let transpose _ = raise NotImplemented
  let to_list _ = raise NotImplemented
  let get _ _ _ = raise NotImplemented 

  let (++) _ _ = raise NotImplemented
  let ( ** ) _ _ = raise NotImplemented
  let (==) _ _ = raise NotImplemented
end

(* Problem 2-1 *)
(* Closure *)

module ClosureFn (Mat : MATRIX) :
sig
  val closure : Mat.t -> Mat.t
end
=
struct
  let closure _ = raise NotImplemented
end

(* Problem 2-2 *)
(* Applications to Graph Problems *)

module BoolMat = MatrixFn (Boolean)
module BoolMatClosure = ClosureFn (BoolMat)

let reach _ = raise NotImplemented

let al = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  false; false];
   [false; true;  true;  false; true;  false];
   [false; true;  false; true;  true;  true];
   [false; false; true;  true;  true;  false];
   [false; false; false; true;  false; true]]

let solution_al' = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true]]

module Distance : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 999999              (* Dummy value : Rewrite it! *)
  let one = 999999               (* Dummy value : Rewrite it! *)

  let (++) _ _ = raise NotImplemented
  let ( ** ) _ _ = raise NotImplemented
  let (==) _ _ = raise NotImplemented
end

(* .. Write some code here .. *)

let distance _ = raise NotImplemented

let dl =
  [[  0;  -1;  -1;  -1;  -1;  -1 ];
   [ -1; 0  ; 35 ; 200; -1 ; -1  ];
   [ -1; 50 ; 0  ; -1 ; 150; -1  ];
   [ -1; 75;  -1 ; 0  ; 100; 25  ];
   [ -1; -1 ; 50 ; 65 ; 0  ; -1  ];
   [ -1; -1 ; -1 ; -1 ; -1 ; 0   ]]

let solution_dl' =
  [[0;  -1;  -1;  -1;  -1;  -1  ];
   [-1; 0;   35;  200; 185; 225 ];
   [-1; 50;  0;   215; 150; 240 ];
   [-1; 75;  110; 0;   100; 25  ];
   [-1; 100; 50;  65;  0;   90  ];
   [-1; -1;  -1;  -1;  -1;  0   ]]

module Weight : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 999999              (* Dummy value : Rewrite it! *)
  let one = 999999               (* Dummy value : Rewrite it! *)
 
  let (++) _ _ = raise NotImplemented
  let ( ** ) _ _ = raise NotImplemented
  let (==) _ _ = raise NotImplemented
end

(* .. Write some code here .. *)

let weight _ = raise NotImplemented

let ml =
  [[-1; 0  ; 0  ; 0  ; 0  ; 0   ];
   [0 ; -1 ; 10 ; 100; 0  ; 0   ];
   [0 ; 50 ; -1 ; 0  ; 150; 0   ];
   [0 ; 75 ; 0  ; -1 ; 125; 40 ];
   [0 ; 0  ; 25 ; -1 ; -1 ; 0   ];
   [0 ; 0  ; 0  ; 0  ; 0  ; -1  ]]

let solution_ml' =
  [[-1; 0;  0;   0;   0;   0  ];
   [0;  -1; 25;  100; 100; 40 ];
   [0;  75; -1;  150; 150; 40 ];
   [0;  75; 25;  -1;  125; 40 ];
   [0;  75; 25;  -1;  -1;  40 ];
   [0;  0;  0;   0;   0;   -1 ]]

let _ =
  try 
  if reach al = solution_al' && distance dl = solution_dl' && weight ml = solution_ml' then
    print_endline "\nYour program seems fine (but no guarantee)!"
  else
    print_endline "\nYour program might have bugs!"
  with _ -> print_endline "\nYour program is not complete yet!" 

