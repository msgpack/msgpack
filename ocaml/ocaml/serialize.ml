open Base
open ExtString

type t = Pack.t

let deserialize_string str =
  str
  +> String.explode
  +> List.map Pack.ascii8_of_char
  +> MsgpackCore.deserialize 0
  +> List.hd
  +> Pack.unpack

let serialize_string obj =
  obj
  +> Pack.pack
  +> MsgpackCore.serialize
  +> List.map Pack.char_of_ascii8
  +> String.implode

