open Base
open MsgpackCore

exception Not_conversion of string

type t =
  [ `Bool of bool
  | `Nil
  | `PFixnum of int
  | `NFixnum of int
  | `Uint8 of int
  | `Uint16 of int
  | `Uint32 of int64
  | `Uint64 of Big_int.big_int
  | `Int8 of int
  | `Int16 of int
  | `Int32 of int32
  | `Int64 of int64
  | `Float of float
  | `Double of float
  | `FixRaw of char list
  | `Raw16 of char list
  | `Raw32 of char list
  | `FixArray of t list
  | `Array16 of t list
  | `Array32 of t list
  | `FixMap of (t * t) list
  | `Map16 of (t * t) list
  | `Map32 of (t * t) list ]

let ascii8 n =
  Ascii(n land 0b0000_0001 <> 0,
	n land 0b0000_0010 <> 0,
	n land 0b0000_0100 <> 0,
	n land 0b0000_1000 <> 0,
	n land 0b0001_0000 <> 0,
	n land 0b0010_0000 <> 0,
	n land 0b0100_0000 <> 0,
	n land 0b1000_0000 <> 0)

let ascii8_of_char c =
  c +> Char.code +> ascii8

let ascii16 n =
  (ascii8 (n lsr 8), ascii8 n)

let ascii32 n =
  (ascii16 (Int64.to_int (Int64.shift_right_logical n 16)),
   ascii16 (Int64.to_int (Int64.logand n 0xFFFFL)))

let ascii64 n =
  let open Big_int in
  let x =
    shift_right_big_int n 32
    +> int64_of_big_int
    +> ascii32 in
  let y =
    and_big_int n (big_int_of_int64 0xFFFF_FFFFL)
    +> int64_of_big_int
    +> ascii32 in
    (x, y)

let ascii32_of_int32 n =
  (ascii16 (Int32.to_int (Int32.shift_right_logical n 16)),
   ascii16 (Int32.to_int n))

let ascii64_of_int64 n =
  (ascii32 (Int64.shift_right_logical n 32),
   ascii32 n)

let not_conversion msg =
  raise @@ Not_conversion msg

let rec pack = function
    `Nil ->
      Nil
  | `Bool b ->
      Bool b
  | `PFixnum n ->
      if 0 <= n && n < 128 then
	PFixnum (ascii8 n)
      else
	not_conversion "pfixnum"
  | `NFixnum n ->
      if -32 <= n && n < 0 then
	NFixnum (ascii8 n)
      else
	not_conversion "nfixnum"
  | `Uint8 n ->
      if 0 <= n && n <= 0xFF then
	Uint8 (ascii8 n)
      else
	not_conversion "uint8"
  | `Uint16 n ->
      if 0 <= n && n <= 0xFF_FF then
	Uint16 (ascii16 n)
      else
	not_conversion "uint16"
  | `Uint32 n ->
      if 0L <= n && n <= 0xFFFF_FFFFL then
	Uint32 (ascii32 n)
      else
	not_conversion "uint32"
  | `Uint64 n ->
      let open Big_int in
      let (<=%) = le_big_int in
      let (<<)  = shift_left_big_int in
      if zero_big_int <=% n && n <=%  (unit_big_int << 64) then
	Uint64 (ascii64 n)
      else
	not_conversion "uint64"
  | `Int8 n ->
      if -127 <= n && n <= 128 then
	Int8 (ascii8 n)
      else
	not_conversion "int8"
  | `Int16 n ->
      if -32767 <= n && n <= 32768 then
	Int16 (ascii16 n)
      else
	not_conversion "int16"
  | `Int32 n ->
      Int32 (ascii16 (Int32.to_int (Int32.shift_right_logical n 16)),
	     ascii16 (Int32.to_int n))
  | `Int64 n ->
      Int64 (ascii64_of_int64 n)
  | `Float n ->
      Float (ascii32_of_int32 @@ Int32.bits_of_float n)
  | `Double n ->
      Double (ascii64_of_int64 @@ Int64.bits_of_float n)
  | `FixRaw cs ->
      FixRaw (List.map ascii8_of_char cs)
  | `Raw16 cs ->
      Raw16 (List.map ascii8_of_char cs)
  | `Raw32 cs ->
      Raw32 (List.map ascii8_of_char cs)
  | `FixArray xs ->
      FixArray (List.map pack xs)
  | `Array16 xs ->
      Array16 (List.map pack xs)
  | `Array32 xs ->
      Array32 (List.map pack xs)
  | `FixMap xs ->
      FixMap (List.map (fun (x,y) -> (pack x, pack y)) xs)
  | `Map16 xs ->
      Map16 (List.map (fun (x,y) -> (pack x, pack y)) xs)
  | `Map32 xs ->
      Map32 (List.map (fun (x,y) -> (pack x, pack y)) xs)

let of_ascii8 (Ascii(b1,b2,b3,b4,b5,b6,b7,b8)) =
  List.fold_left (fun x y -> 2 * x + (if y then 1 else 0)) 0 [ b8; b7; b6; b5; b4; b3; b2; b1 ]

let char_of_ascii8 c =
  c +> of_ascii8 +> Char.chr

let of_ascii16 (c1, c2) =
  of_ascii8 c1 lsl 8 + of_ascii8 c2

let of_ascii32 (c1,c2) =
  let (+%) = Int64.add in
  let (<<) = Int64.shift_left in
    ((Int64.of_int (of_ascii16 c1)) << 16) +% Int64.of_int (of_ascii16 c2)

let int32_of_ascii32 (c1,c2) =
  let (+%) = Int32.add in
  let (<<) = Int32.shift_left in
    ((Int32.of_int @@ of_ascii16 c1) << 16) +% (Int32.of_int @@ of_ascii16 c2)

let int64_of_ascii64 (c1,c2) =
  let (+%) = Int64.add in
  let (<<) = Int64.shift_left in
    (of_ascii32 c1 << 32) +% (of_ascii32 c2)

let of_ascii64 (c1, c2) =
  let open Big_int in
  let (+%) = add_big_int in
  let (<<) = shift_left_big_int in
    ((big_int_of_int64 @@ of_ascii32 c1) << 32) +% (big_int_of_int64 @@ of_ascii32 c2)

let int width n =
  (n lsl (Sys.word_size-width-1)) asr (Sys.word_size-width-1);;

let rec unpack  = function
  | Nil -> `Nil
  | Bool b -> `Bool b
  | PFixnum c -> `PFixnum (of_ascii8 c)
  | NFixnum c -> `NFixnum (int 8 @@ of_ascii8 c)
  | Uint8  c -> `Uint8  (of_ascii8 c)
  | Uint16 c -> `Uint16 (of_ascii16 c)
  | Uint32 c -> `Uint32 (of_ascii32 c)
  | Uint64 c -> `Uint64 (of_ascii64 c)
  | Int8   c -> `Int8  (int  8 @@ of_ascii8 c)
  | Int16  c -> `Int16 (int 16 @@ of_ascii16 c)
  | Int32  c -> `Int32 (int32_of_ascii32 c)
  | Int64  c -> `Int64 (int64_of_ascii64 c)
  | Float  c -> `Float (Int32.float_of_bits (int32_of_ascii32 c))
  | Double c -> `Double (Int64.float_of_bits (int64_of_ascii64 c))
  | FixRaw cs -> `FixRaw (List.map char_of_ascii8 cs)
  | Raw16  cs -> `Raw16 (List.map char_of_ascii8 cs)
  | Raw32  cs -> `Raw32 (List.map char_of_ascii8 cs)
  | FixArray xs -> `FixArray (List.map unpack xs)
  | Array16 xs -> `Array16 (List.map unpack xs)
  | Array32 xs -> `Array32 (List.map unpack xs)
  | FixMap  xs -> `FixMap (List.map (fun (x,y) -> (unpack x, unpack y)) xs)
  | Map16  xs -> `Map16 (List.map (fun (x,y) -> (unpack x, unpack y)) xs)
  | Map32  xs -> `Map32 (List.map (fun (x,y) -> (unpack x, unpack y)) xs)
