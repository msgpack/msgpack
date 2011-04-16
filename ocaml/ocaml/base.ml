let (@@) f g = f g
let (+>) f g = g f
let ($) f g x = f (g x)
let (!$) = Lazy.force
external id : 'a -> 'a = "%identity"

let uncurry f a b = f (a,b)
let curry f (a,b) = f a b
let flip f a b = f b a
let const a _ = a

let sure f =
  function
      Some x ->
	Some (f x)
    | None ->
	None

let option f x = try Some (f x) with Not_found -> None
let maybe  f x = try `Val (f x) with e -> `Error e
let tee f x = try ignore @@ f x; x with _ -> x

type ('a,'b) either = Left of 'a | Right of 'b
let left x = Left x
let right x = Right x

let failwithf fmt = Printf.kprintf (fun s () -> failwith s) fmt

let lookup x xs = (option @@ List.assoc x) xs

let string_of_list xs =
  Printf.sprintf "[%s]"
    @@ String.concat ";" xs

let rec unfold f init =
     match f init with
	 Some (a, b) -> a :: unfold f b
       | None        -> []

let rec range a b =
  if a >= b then
    []
  else
    a::range (a+1) b

let rec interperse delim =
  function
      []  -> []
    | [x] -> [x]
    | x::xs -> x::delim::interperse delim xs

let map_accum_left f init xs =
  let f (accum,ys) x =
    let accum',y =
      f accum x in
      (accum',y::ys) in
  let accum,ys =
    List.fold_left f (init,[]) xs in
    accum,List.rev ys

let rec map_accum_right f init =
  function
      [] ->
	init,[]
    | x::xs ->
	let (accum,ys) =
	  map_accum_right f init xs in
	let (accum,y) =
	  f accum x in
	  accum,y::ys

let rec filter_map f =
  function
      x::xs ->
	begin match f x with
	    Some y -> y::filter_map f xs
	  | None   -> filter_map f xs
	end
    | [] ->
	[]

let rec group_by f =
  function
      [] ->
	[]
    | x1::x2::xs when f x1 x2 ->
	begin match group_by f @@ x2::xs with
	    y::ys ->
	      (x1::y)::ys
	  | _ ->
	      failwith "must not happen"
	end
    | x::xs ->
	[x]::group_by f xs

let index x xs =
  let rec loop i = function
      [] ->
	raise Not_found
    | y::ys ->
	if x = y then
	  i
	else
	  loop (i+1) ys in
    loop 0 xs

let string_of_char =
  String.make 1

let hex =
  Printf.sprintf "0x%x"

let open_out_with path f =
  let ch =
    open_out_bin path in
    maybe f ch
    +> tee (fun _ -> close_out ch)
    +> function
	`Val v ->  v
      | `Error e -> raise e

let open_in_with path f =
  let ch =
    open_in_bin path in
    maybe f ch
    +> tee (fun _ -> close_in ch)
    +> function
	`Val v ->  v
      | `Error e -> raise e

let forever f () =
  while true do
    f ()
  done

let undefined =  Obj.magic 42
let undef     = undefined

let p fmt = Printf.kprintf (fun s () -> print_endline s; flush stdout) fmt

let ret x _ =
  x
