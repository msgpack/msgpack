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

val pack : t -> MsgpackCore.object0
val unpack : MsgpackCore.object0 -> t

val char_of_ascii8 : MsgpackCore.ascii -> char
val ascii8_of_char : char -> MsgpackCore.ascii
