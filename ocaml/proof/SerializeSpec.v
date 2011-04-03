Require Import List Ascii.
Require Import MultiByte Object ListUtil.

Open Scope list_scope.
Open Scope char_scope.

Inductive Serialized : object -> list ascii8 -> Prop :=
| SNil :
  Serialized Nil ["192"]
| STrue :
  Serialized (Bool true)  ["195"]
| SFalse :
  Serialized (Bool false) ["194"]
| SPFixnum : forall x1 x2 x3 x4 x5 x6 x7,
  Serialized (PFixnum   (Ascii x1 x2 x3 x4 x5 x6 x7 false))
             [Ascii x1 x2 x3 x4 x5 x6 x7 false]
| SNFixnum : forall  x1 x2 x3 x4 x5,
  Serialized (NFixnum   (Ascii x1 x2 x3 x4 x5 true true true))
             [Ascii x1 x2 x3 x4 x5 true true true]
| SUint8 : forall c,
  Serialized (Uint8 c) ("204"::list_of_ascii8 c)
| SUint16 : forall c,
  Serialized (Uint16 c) ("205"::list_of_ascii16 c)
| SUint32 : forall c,
  Serialized (Uint32 c) ("206"::list_of_ascii32 c)
| SUint64 : forall c,
  Serialized (Uint64 c) ("207"::list_of_ascii64 c)
| SInt8 : forall c,
  Serialized (Int8 c) ("208"::list_of_ascii8 c)
| SInt16 : forall c,
  Serialized (Int16 c) ("209"::list_of_ascii16 c)
| SInt32 : forall c,
  Serialized (Int32 c) ("210"::list_of_ascii32 c)
| SInt64 : forall c,
  Serialized (Int64 c) ("211"::list_of_ascii64 c)
| SFloat : forall c,
  Serialized (Float c) ("202"::list_of_ascii32 c)
| SDouble : forall c,
  Serialized (Double c) ("203"::list_of_ascii64 c)
| SFixRaw : forall cs b1 b2 b3 b4 b5,
  Ascii b1 b2 b3 b4 b5 false false false = ascii8_of_nat (length cs) ->
  Serialized (FixRaw cs) ((Ascii b1 b2 b3 b4 b5 true false true)::cs)
| SRaw16 : forall cs s1 s2,
  (s1,s2) =  ascii16_of_nat (length cs) ->
  Serialized (Raw16 cs) ("218"::s1::s2::cs)
| SRaw32 : forall cs s1 s2 s3 s4,
  ((s1,s2),(s3,s4)) =  ascii32_of_nat (length cs) ->
   Serialized (Raw32 cs) ("219"::s1::s2::s3::s4::cs)
| SFixArrayNil :
  Serialized (FixArray []) ["144"]
| SFixArrayCons : forall x xs y ys b1 b2 b3 b4 b5 b6 b7 b8,
  Ascii b1 b2 b3 b4 false false false false = ascii8_of_nat (length xs) ->
  Ascii b5 b6 b7 b8 false false false false = ascii8_of_nat (length (x::xs)) ->
  Serialized x y ->
  Serialized (FixArray xs) ((Ascii b1 b2 b3 b4 true false false true)::ys) ->
  Serialized (FixArray (x::xs)) ((Ascii b5 b6 b7 b8 true false false true)::y ++ ys)
| SArray16Nil :
  Serialized (Array16 []) ["220"; "000"; "000"]
| SArray16Cons : forall x xs y ys s1 s2 t1 t2,
  (t1,t2) = ascii16_of_nat (length xs) ->
  (s1,s2) = ascii16_of_nat (length (x::xs)) ->
  Serialized x y ->
  Serialized (Array16 xs) ("220"::t1::t2::ys) ->
  Serialized (Array16 (x::xs)) ("220"::s1::s2::y ++ ys)
| SArray32Nil :
  Serialized (Array32 []) ["221"; "000"; "000";"000"; "000"]
| SArray32Cons : forall x xs y ys s1 s2 s3 s4 t1 t2 t3 t4,
  ((t1,t2),(t3,t4)) = ascii32_of_nat (length xs) ->
  ((s1,s2),(s3,s4)) = ascii32_of_nat (length (x::xs)) ->
  Serialized x y ->
  Serialized (Array32 xs) ("221"::t1::t2::t3::t4::ys) ->
  Serialized (Array32 (x::xs)) ("221"::s1::s2::s3::s4::y ++ ys)
| SFixMapNil :
  Serialized (FixMap []) ["128"]
| SFixMapCons : forall x1 x2 xs y1 y2 ys b1 b2 b3 b4 b5 b6 b7 b8,
  Ascii b1 b2 b3 b4 false false false false = ascii8_of_nat (length xs) ->
  Ascii b5 b6 b7 b8 false false false false = ascii8_of_nat (length ((x1,x2)::xs)) ->
  Serialized x1 y1 ->
  Serialized x2 y2 ->
  Serialized (FixMap xs) ((Ascii b1 b2 b3 b4 false false false true)::ys) ->
  Serialized (FixMap ((x1,x2)::xs)) ((Ascii b5 b6 b7 b8 false false false true)::y1 ++ y2  ++ ys)
| SMap16Nil :
  Serialized (Map16 []) ["222"; "000"; "000"]
| SMap16Cons : forall x1 x2 xs y1 y2 ys s1 s2 t1 t2,
  (t1,t2) = ascii16_of_nat (length xs) ->
  (s1,s2) = ascii16_of_nat (length ((x1,x2)::xs)) ->
  Serialized x1 y1 ->
  Serialized x2 y2 ->
  Serialized (Map16 xs) ("222"::t1::t2::ys) ->
  Serialized (Map16 ((x1,x2)::xs)) ("222"::s1::s2::y1 ++ y2 ++ ys)
| SMap32Nil :
  Serialized (Map32 []) ["223"; "000"; "000";"000"; "000"]
| SMap32Cons : forall x1 x2 xs y1 y2 ys s1 s2 s3 s4 t1 t2 t3 t4,
  ((t1,t2),(t3,t4)) = ascii32_of_nat (length xs) ->
  ((s1,s2),(s3,s4)) = ascii32_of_nat (length ((x1,x2)::xs)) ->
  Serialized x1 y1 ->
  Serialized x2 y2 ->
  Serialized (Map32 xs) ("223"::t1::t2::t3::t4::ys) ->
  Serialized (Map32 ((x1,x2)::xs)) ("223"::s1::s2::s3::s4::y1 ++ y2 ++ ys).
