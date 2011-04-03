open Base

let rec last =
  function
      [] ->
	invalid_arg "HList.last"
    | [x] ->
	x
    | _::xs ->
	last xs

let init xs =
  let rec init' ys =
    function
	[]  ->
	  invalid_arg "HList.init"
      |	[_] ->
	  List.rev ys
      | x::xs ->
	  init' (x::ys) xs in
    init' [] xs

let null =
  function
      [] ->
	true
    | _ ->
	false

let fold_left1 f =
  function
      [] ->
	invalid_arg "HList.fold_left1"
    | x::xs ->
	List.fold_left f x xs

let rec fold_right1 f =
  function
      []    ->
	invalid_arg "HList.fold_right1"
    | [x]   ->
	x
    | x::xs ->
	f x (fold_right1 f xs)

let conj =
  List.fold_left (&&) true

let disj =
  List.fold_left (||) false

let sum =
  List.fold_left (+) 0

let product =
  List.fold_left ( * ) 1

let concat_map f xs =
  List.fold_right ((@) $ f) xs []

let maximum xs =
  fold_left1 max xs

let minimum xs =
  fold_left1 min xs

let rec scanl f y =
  function
      [] ->
	[y]
    | x::xs ->
	y::scanl f (f y x) xs

let scanl1 f =
  function
      [] ->
	[]
    | x::xs ->
	scanl f x xs

let rec scanr f z =
  function
      [] ->
	[z]
    | x::xs ->
	match scanr f z xs with
	    y::_ as yss ->
	      (f x y) :: yss
	  | _ ->
	      failwith "must not happen"

let scanr1 f =
  function
    [] ->
      []
  | x::xs ->
      scanr f x xs

let replicate n x =
  let rec loop i ys =
    if i = 0 then
      ys
    else
      loop (i-1) (x::ys) in
    loop n []

let rec take n =
  function
      [] ->
	[]
    | x::xs ->
	if n <= 0 then
	  []
	else
	  x :: take (n - 1) xs

let rec drop n =
  function
      [] ->
	[]
    | xs when n <= 0 ->
	xs
    | _::xs ->
      drop (n-1) xs

let rec splitAt n xs =
  match n,xs with
      0,_  | _,[] ->
	[],xs
    | _,y::ys ->
	let p,q =
	  splitAt (n-1) ys in
	  y::p,q

let rec takeWhile f =
  function
      x::xs when f x ->
	x :: takeWhile f xs
    | _ ->
	[]

let rec dropWhile f =
  function
      x::xs when f x ->
	dropWhile f xs
    | xs ->
	xs

let rec span f =
  function
      x::xs when f x ->
	let ys,zs =
	  span f xs in
	  x::ys,zs
    | xs ->
	[],xs

let break f =
  span (not $ f)

let rec zip_with f xs ys =
  match xs,ys with
      [],_ | _,[] ->
	[]
    | x::xs',y::ys' ->
	(f x y)::zip_with f xs' ys'

let rec zip_with3 f xs ys zs =
  match xs,ys,zs with
      [],_,_ | _,[],_ | _,_,[] ->
	[]
    | x::xs',y::ys',z::zs' ->
	(f x y z)::zip_with3 f xs' ys' zs'

let zip xs ys =
  zip_with (fun x y -> (x,y)) xs ys

let zip3 xs ys zs =
  zip_with3 (fun x y z -> (x,y,z)) xs ys zs

let unzip xs =
  List.fold_right (fun (x,y) (xs,ys) -> (x::xs,y::ys)) xs ([],[])

let unzip3 xs =
  List.fold_right (fun (x,y,z) (xs,ys,zs) -> (x::xs,y::ys,z::zs)) xs ([],[],[])

let lookup x xs =
  try
    Some (List.assoc x xs)
  with Not_found ->
    None
