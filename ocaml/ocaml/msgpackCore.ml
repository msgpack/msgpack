let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
  | (x, y) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
  | (x, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
  | [] -> 0
  | y::l' -> succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
    | [] -> m
    | a::l1 -> a::(app l1 m)

(** val plus : int -> int -> int **)

let rec plus = (+)

(** val mult : int -> int -> int **)

let rec mult = ( * )

type positive =
  | XI of positive
  | XO of positive
  | XH

(** val psucc : positive -> positive **)

let rec psucc = function
  | XI p -> XO (psucc p)
  | XO p -> XI p
  | XH -> XO XH

(** val pplus : positive -> positive -> positive **)

let rec pplus x y =
  match x with
    | XI p ->
        (match y with
           | XI q -> XO (pplus_carry p q)
           | XO q -> XI (pplus p q)
           | XH -> XO (psucc p))
    | XO p ->
        (match y with
           | XI q -> XI (pplus p q)
           | XO q -> XO (pplus p q)
           | XH -> XI p)
    | XH ->
        (match y with
           | XI q -> XO (psucc q)
           | XO q -> XI q
           | XH -> XO XH)

(** val pplus_carry : positive -> positive -> positive **)

and pplus_carry x y =
  match x with
    | XI p ->
        (match y with
           | XI q -> XI (pplus_carry p q)
           | XO q -> XO (pplus_carry p q)
           | XH -> XI (psucc p))
    | XO p ->
        (match y with
           | XI q -> XO (pplus_carry p q)
           | XO q -> XI (pplus p q)
           | XH -> XO (psucc p))
    | XH ->
        (match y with
           | XI q -> XI (psucc q)
           | XO q -> XO (psucc q)
           | XH -> XI XH)

(** val pmult_nat : positive -> int -> int **)

let rec pmult_nat x pow2 =
  match x with
    | XI p -> plus pow2 (pmult_nat p (plus pow2 pow2))
    | XO p -> pmult_nat p (plus pow2 pow2)
    | XH -> pow2

(** val nat_of_P : positive -> int **)

let nat_of_P x =
  pmult_nat x (succ 0)

(** val p_of_succ_nat : int -> positive **)

let rec p_of_succ_nat n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> XH)
    (fun x -> psucc (p_of_succ_nat x))
    n0

(** val pmult : positive -> positive -> positive **)

let rec pmult x y =
  match x with
    | XI p -> pplus y (XO (pmult p y))
    | XO p -> XO (pmult p y)
    | XH -> y

type n =
  | N0
  | Npos of positive

(** val nplus : n -> n -> n **)

let nplus n0 m =
  match n0 with
    | N0 -> m
    | Npos p -> (match m with
                   | N0 -> n0
                   | Npos q -> Npos (pplus p q))

(** val nmult : n -> n -> n **)

let nmult n0 m =
  match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                   | N0 -> N0
                   | Npos q -> Npos (pmult p q))

(** val nat_of_N : n -> int **)

let nat_of_N = function
  | N0 -> 0
  | Npos p -> nat_of_P p

(** val n_of_nat : int -> n **)

let n_of_nat n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> N0)
    (fun n' -> Npos (p_of_succ_nat n'))
    n0

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
  | [] -> []
  | x::t -> app (f x) (flat_map f t)

(** val eucl_dev : int -> int -> (int * int) **)

let eucl_dev = fun n m -> (m/n, m mod n)

type ascii =
  | Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val zero : ascii **)

let zero =
  Ascii (false, false, false, false, false, false, false, false)

(** val one : ascii **)

let one =
  Ascii (true, false, false, false, false, false, false, false)

(** val shift : bool -> ascii -> ascii **)

let shift c = function
  | Ascii (a1, a2, a3, a4, a5, a6, a7, a8) -> Ascii (c, a1, a2, a3, a4, a5,
      a6, a7)

(** val ascii_of_pos : positive -> ascii **)

let ascii_of_pos =
  let rec loop n0 p =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> zero)
      (fun n' ->
      match p with
        | XI p' -> shift true (loop n' p')
        | XO p' -> shift false (loop n' p')
        | XH -> one)
      n0
  in loop (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))

(** val ascii_of_N : n -> ascii **)

let ascii_of_N = function
  | N0 -> zero
  | Npos p -> ascii_of_pos p

(** val ascii_of_nat : int -> ascii **)

let ascii_of_nat a =
  ascii_of_N (n_of_nat a)

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
  | [] -> N0
  | b::l' ->
      nplus (if b then Npos XH else N0)
        (nmult (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : ascii -> n **)

let n_of_ascii = function
  | Ascii (a0, a1, a2, a3, a4, a5, a6, a7) ->
      n_of_digits (a0::(a1::(a2::(a3::(a4::(a5::(a6::(a7::[]))))))))

(** val nat_of_ascii : ascii -> int **)

let nat_of_ascii a =
  nat_of_N (n_of_ascii a)

(** val take : int -> 'a1 list -> 'a1 list **)

let rec take n0 xs =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun m -> match xs with
                | [] -> []
                | x::xs0 -> x::(take m xs0))
    n0

(** val drop : int -> 'a1 list -> 'a1 list **)

let rec drop n0 xs =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> xs)
    (fun m -> match xs with
                | [] -> []
                | x::xs0 -> drop m xs0)
    n0

(** val split_at : int -> 'a1 list -> 'a1 list * 'a1 list **)

let split_at n0 xs =
  ((take n0 xs), (drop n0 xs))

(** val pair : 'a1 list -> ('a1 * 'a1) list **)

let rec pair = function
  | [] -> []
  | k::l -> (match l with
               | [] -> []
               | v::ys -> (k, v)::(pair ys))

(** val pow : int -> int **)

let rec pow n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> succ 0)
    (fun n' -> mult (succ (succ 0)) (pow n'))
    n0

(** val divmod : int -> int -> (int * int) **)

let divmod n0 m =
  eucl_dev m n0

type ascii8 = ascii

type ascii16 = ascii8 * ascii8

type ascii32 = ascii16 * ascii16

type ascii64 = ascii32 * ascii32

(** val nat_of_ascii8 : ascii -> int **)

let nat_of_ascii8 =
  nat_of_ascii

(** val ascii8_of_nat : int -> ascii **)

let ascii8_of_nat =
  ascii_of_nat

(** val ascii16_of_nat : int -> ascii * ascii **)

let ascii16_of_nat a =
  let (q, r) =
    divmod a (pow (succ (succ (succ (succ (succ (succ (succ (succ 0)))))))))
  in
  ((ascii8_of_nat q), (ascii8_of_nat r))

(** val nat_of_ascii16 : ascii16 -> int **)

let nat_of_ascii16 = function
  | (a1, a2) ->
      plus
        (mult (nat_of_ascii8 a1)
          (pow (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))))
        (nat_of_ascii8 a2)

(** val ascii32_of_nat : int -> (ascii * ascii) * (ascii * ascii) **)

let ascii32_of_nat a =
  let (q, r) =
    divmod a
      (pow (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ 0)))))))))))))))))
  in
  ((ascii16_of_nat q), (ascii16_of_nat r))

(** val nat_of_ascii32 : ascii32 -> int **)

let nat_of_ascii32 = function
  | (a1, a2) ->
      plus
        (mult (nat_of_ascii16 a1)
          (pow (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ 0))))))))))))))))))
        (nat_of_ascii16 a2)

(** val list_of_ascii8 : ascii8 -> ascii8 list **)

let list_of_ascii8 x =
  x::[]

(** val list_of_ascii16 : ascii16 -> ascii8 list **)

let list_of_ascii16 = function
  | (x1, x2) -> app (list_of_ascii8 x1) (list_of_ascii8 x2)

(** val list_of_ascii32 : ascii32 -> ascii8 list **)

let list_of_ascii32 = function
  | (x1, x2) -> app (list_of_ascii16 x1) (list_of_ascii16 x2)

(** val list_of_ascii64 : ascii64 -> ascii8 list **)

let list_of_ascii64 = function
  | (x1, x2) -> app (list_of_ascii32 x1) (list_of_ascii32 x2)

type object0 =
  | Bool of bool
  | Nil
  | PFixnum of ascii8
  | NFixnum of ascii8
  | Uint8 of ascii8
  | Uint16 of ascii16
  | Uint32 of ascii32
  | Uint64 of ascii64
  | Int8 of ascii8
  | Int16 of ascii16
  | Int32 of ascii32
  | Int64 of ascii64
  | Float of ascii32
  | Double of ascii64
  | FixRaw of ascii8 list
  | Raw16 of ascii8 list
  | Raw32 of ascii8 list
  | FixArray of object0 list
  | Array16 of object0 list
  | Array32 of object0 list
  | FixMap of (object0 * object0) list
  | Map16 of (object0 * object0) list
  | Map32 of (object0 * object0) list

(** val atat : ('a1 -> 'a2) -> 'a1 -> 'a2 **)

let atat f x =
  f x

(** val serialize : object0 -> ascii8 list **)

let rec serialize = function
  | Bool b ->
      if b
      then (Ascii (true, true, false, false, false, false, true, true))::[]
      else (Ascii (false, true, false, false, false, false, true, true))::[]
  | Nil -> (Ascii (false, false, false, false, false, false, true, true))::[]
  | PFixnum a ->
      let Ascii (b1, b2, b3, b4, b5, b6, b7, b) = a in
      (Ascii (b1, b2, b3, b4, b5, b6, b7, false))::[]
  | NFixnum a ->
      let Ascii (b1, b2, b3, b4, b5, b, b0, b6) = a in
      (Ascii (b1, b2, b3, b4, b5, true, true, true))::[]
  | Uint8 c -> (Ascii (false, false, true, true, false, false, true,
      true))::(list_of_ascii8 c)
  | Uint16 c -> (Ascii (true, false, true, true, false, false, true,
      true))::(list_of_ascii16 c)
  | Uint32 c -> (Ascii (false, true, true, true, false, false, true,
      true))::(list_of_ascii32 c)
  | Uint64 c -> (Ascii (true, true, true, true, false, false, true,
      true))::(list_of_ascii64 c)
  | Int8 c -> (Ascii (false, false, false, false, true, false, true,
      true))::(list_of_ascii8 c)
  | Int16 c -> (Ascii (true, false, false, false, true, false, true,
      true))::(list_of_ascii16 c)
  | Int32 c -> (Ascii (false, true, false, false, true, false, true,
      true))::(list_of_ascii32 c)
  | Int64 c -> (Ascii (true, true, false, false, true, false, true,
      true))::(list_of_ascii64 c)
  | Float c -> (Ascii (false, true, false, true, false, false, true,
      true))::(list_of_ascii32 c)
  | Double c -> (Ascii (true, true, false, true, false, false, true,
      true))::(list_of_ascii64 c)
  | FixRaw xs ->
      let Ascii (b1, b2, b3, b4, b5, b, b0, b6) =
        atat ascii8_of_nat (length xs)
      in
      (Ascii (b1, b2, b3, b4, b5, true, false, true))::xs
  | Raw16 xs ->
      let (s1, s2) = atat ascii16_of_nat (length xs) in
      (Ascii (false, true, false, true, true, false, true,
      true))::(s1::(s2::xs))
  | Raw32 xs ->
      let (p, p0) = atat ascii32_of_nat (length xs) in
      let (s1, s2) = p in
      let (s3, s4) = p0 in
      (Ascii (true, true, false, true, true, false, true,
      true))::(s1::(s2::(s3::(s4::xs))))
  | FixArray xs ->
      let ys = flat_map serialize xs in
      let Ascii (b1, b2, b3, b4, b, b0, b5, b6) =
        atat ascii8_of_nat (length xs)
      in
      (Ascii (b1, b2, b3, b4, true, false, false, true))::ys
  | Array16 xs ->
      let ys = flat_map serialize xs in
      let (s1, s2) = ascii16_of_nat (length xs) in
      (Ascii (false, false, true, true, true, false, true,
      true))::(s1::(s2::ys))
  | Array32 xs ->
      let ys = flat_map serialize xs in
      let (p, p0) = atat ascii32_of_nat (length xs) in
      let (s1, s2) = p in
      let (s3, s4) = p0 in
      (Ascii (true, false, true, true, true, false, true,
      true))::(s1::(s2::(s3::(s4::ys))))
  | FixMap xs ->
      let ys =
        flat_map (fun p -> app (serialize (fst p)) (serialize (snd p))) xs
      in
      let Ascii (b1, b2, b3, b4, b, b0, b5, b6) =
        atat ascii8_of_nat (length xs)
      in
      (Ascii (b1, b2, b3, b4, false, false, false, true))::ys
  | Map16 xs ->
      let ys =
        flat_map (fun p -> app (serialize (fst p)) (serialize (snd p))) xs
      in
      let (s1, s2) = ascii16_of_nat (length xs) in
      (Ascii (false, true, true, true, true, false, true,
      true))::(s1::(s2::ys))
  | Map32 xs ->
      let ys =
        flat_map (fun p -> app (serialize (fst p)) (serialize (snd p))) xs
      in
      let (p, p0) = atat ascii32_of_nat (length xs) in
      let (s1, s2) = p in
      let (s3, s4) = p0 in
      (Ascii (true, true, true, true, true, false, true,
      true))::(s1::(s2::(s3::(s4::ys))))

(** val compact : object0 list -> ascii8 list **)

let compact xs =
  flat_map (fun x -> match x with
                       | FixRaw xs0 -> xs0
                       | _ -> []) xs

(** val deserialize : int -> ascii8 list -> object0 list **)

let rec deserialize n0 xs =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    match xs with
      | [] -> []
      | a::ys ->
          let Ascii (b1, b2, b3, b4, b5, b6, b7, b) = a in
          if b1
          then if b2
               then if b3
                    then if b4
                         then if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s1::l ->
                                                  (match l with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s2::l0 ->
                                                  (match l0 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s3::l1 ->
                                                  (match l1 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s4::ys0 ->
                                                  let n1 =
                                                  nat_of_ascii32 ((s1, s2),
                                                  (s3, s4))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys0)
                                                  in
                                                  (Map32 (pair zs))::ws))))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c1::l ->
                                                  (match l with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c2::l0 ->
                                                  (match l0 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c3::l1 ->
                                                  (match l1 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c4::l2 ->
                                                  (match l2 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c5::l3 ->
                                                  (match l3 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c6::l4 ->
                                                  (match l4 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c7::l5 ->
                                                  (match l5 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c8::ys0 -> (Uint64 (((c1,
                                                  c2), (c3, c4)), ((c5, c6),
                                                  (c7,
                                                  c8))))::
                                                  (deserialize 0 ys0)))))))))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                         else if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then []
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then []
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                    else if b4
                         then if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s1::l ->
                                                  (match l with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s2::l0 ->
                                                  (match l0 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s3::l1 ->
                                                  (match l1 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s4::ys0 ->
                                                  let n1 =
                                                  nat_of_ascii32 ((s1, s2),
                                                  (s3, s4))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys0)
                                                  in
                                                  (Raw32 (compact zs))::ws))))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c1::l ->
                                                  (match l with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c2::l0 ->
                                                  (match l0 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c3::l1 ->
                                                  (match l1 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c4::l2 ->
                                                  (match l2 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c5::l3 ->
                                                  (match l3 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c6::l4 ->
                                                  (match l4 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c7::l5 ->
                                                  (match l5 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c8::ys0 -> (Double (((c1,
                                                  c2), (c3, c4)), ((c5, c6),
                                                  (c7,
                                                  c8))))::
                                                  (deserialize 0 ys0)))))))))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                         else if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c1::l ->
                                                  (match l with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c2::l0 ->
                                                  (match l0 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c3::l1 ->
                                                  (match l1 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c4::l2 ->
                                                  (match l2 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c5::l3 ->
                                                  (match l3 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c6::l4 ->
                                                  (match l4 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c7::l5 ->
                                                  (match l5 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c8::ys0 -> (Int64 (((c1,
                                                  c2), (c3, c4)), ((c5, c6),
                                                  (c7,
                                                  c8))))::
                                                  (deserialize 0 ys0)))))))))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (Bool
                                                  true)::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
               else if b3
                    then if b4
                         then if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s1::l ->
                                                  (match l with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s2::l0 ->
                                                  (match l0 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s3::l1 ->
                                                  (match l1 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s4::ys0 ->
                                                  let n1 =
                                                  nat_of_ascii32 ((s1, s2),
                                                  (s3, s4))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys0)
                                                  in
                                                  (Array32 zs)::ws))))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c1::l ->
                                                  (match l with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c2::ys0 -> (Uint16 (c1,
                                                  c2))::
                                                  (deserialize 0 ys0)))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                         else if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then []
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then []
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                    else if b4
                         then if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then []
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then []
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                         else if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c1::l ->
                                                  (match l with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c2::ys0 -> (Int16 (c1,
                                                  c2))::
                                                  (deserialize 0 ys0)))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then []
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
          else if b2
               then if b3
                    then if b4
                         then if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s1::l ->
                                                  (match l with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s2::ys0 ->
                                                  let n1 =
                                                  nat_of_ascii16 (s1, s2)
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys0)
                                                  in
                                                  (Map16 (pair zs))::ws))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c1::l ->
                                                  (match l with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c2::l0 ->
                                                  (match l0 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c3::l1 ->
                                                  (match l1 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c4::ys0 -> (Uint32 ((c1,
                                                  c2), (c3,
                                                  c4)))::
                                                  (deserialize 0 ys0)))))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                         else if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then []
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then []
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                    else if b4
                         then if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s1::l ->
                                                  (match l with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s2::ys0 ->
                                                  let n1 =
                                                  nat_of_ascii16 (s1, s2)
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys0)
                                                  in
                                                  (Raw16 (compact zs))::ws))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c1::l ->
                                                  (match l with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c2::l0 ->
                                                  (match l0 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c3::l1 ->
                                                  (match l1 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c4::ys0 -> (Float ((c1,
                                                  c2), (c3,
                                                  c4)))::
                                                  (deserialize 0 ys0)))))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                         else if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c1::l ->
                                                  (match l with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c2::l0 ->
                                                  (match l0 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c3::l1 ->
                                                  (match l1 with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c4::ys0 -> (Int32 ((c1,
                                                  c2), (c3,
                                                  c4)))::
                                                  (deserialize 0 ys0)))))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (Bool
                                                  false)::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
               else if b3
                    then if b4
                         then if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s1::l ->
                                                  (match l with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  s2::ys0 ->
                                                  let n1 =
                                                  nat_of_ascii16 (s1, s2)
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys0)
                                                  in
                                                  (Array16 zs)::ws))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c1::ys0 -> (Uint8
                                                  c1)::
                                                  (deserialize 0 ys0))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                         else if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then []
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then []
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                    else if b4
                         then if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then []
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then []
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                         else if b5
                              then if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then (match ys with
                                                    | 
                                                  [] -> []
                                                    | 
                                                  c1::ys0 -> (Int8
                                                  c1)::
                                                  (deserialize 0 ys0))
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixArray zs)::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                              else if b6
                                   then if b7
                                        then if b
                                             then (NFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, true, true,
                                                  true)))::
                                                  (deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, b5, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat 
                                                  (split_at n1)
                                                  (deserialize n1 ys)
                                                  in
                                                  (FixRaw (compact zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                   else if b7
                                        then if b
                                             then Nil::(deserialize 0 ys)
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys)
                                        else if b
                                             then let n1 =
                                                  nat_of_ascii8 (Ascii (b1,
                                                  b2, b3, b4, false, false,
                                                  false, false))
                                                  in
                                                  let (
                                                  zs, ws) =
                                                  atat
                                                  (split_at
                                                  (mult (succ (succ 0)) n1))
                                                  (deserialize 0 ys)
                                                  in
                                                  (FixMap (pair zs))::ws
                                             else (PFixnum (Ascii (b1, b2,
                                                  b3, b4, b5, b6, b7,
                                                  false)))::
                                                  (deserialize 0 ys))
    (fun m ->
    match xs with
      | [] -> []
      | y::ys -> (FixRaw (y::[]))::(deserialize m ys))
    n0

