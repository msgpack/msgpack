(* -*- coding:utf-8 -*- *)
Require Import List Ascii.
Require Import Pow MultiByte ListUtil.

Open Scope char_scope.

(** MsgPackで使うオブジェクトの定義 *)
Inductive object :=
| Bool (_ : bool)
| Nil
| PFixnum (_ : ascii8)
| NFixnum (_ : ascii8)
| Uint8  (_ : ascii8)
| Uint16 (_ : ascii16)
| Uint32 (_ : ascii32)
| Uint64 (_ : ascii64)
| Int8   (_ : ascii8)
| Int16  (_ : ascii16)
| Int32  (_ : ascii32)
| Int64  (_ : ascii64)
| Float  (_ : ascii32)
| Double (_ : ascii64)
| FixRaw (_ : list ascii8)
| Raw16  (_ : list ascii8)
| Raw32  (_ : list ascii8)
| FixArray ( _ : list object)
| Array16  ( _ : list object)
| Array32  ( _ : list object)
| FixMap   ( _ : list (object * object)%type)
| Map16    ( _ : list (object * object)%type)
| Map32    ( _ : list (object * object)%type).

(** 妥当なオブジェクトの定義 *)
Inductive Valid : object -> Prop :=
| VBool : forall b,
  Valid (Bool b)
| VPFixNum : forall n,
  nat_of_ascii8 n < 128 -> Valid (PFixnum n)
| VNFixNum : forall n,
  (* 負の数を導入したくないので、補数表現を使う *)
  223 < nat_of_ascii8 n /\ nat_of_ascii8 n < 256 -> Valid (NFixnum n)
| VUint8  : forall c, Valid (Uint8 c)
| VUint16 : forall c, Valid (Uint16 c)
| VUint32 : forall c, Valid (Uint32 c)
| VUint64 : forall c, Valid (Uint64 c)
| VInt8   : forall c, Valid (Int8 c)
| VInt16  : forall c, Valid (Int16 c)
| VInt32  : forall c, Valid (Int32 c)
| VInt64  : forall c, Valid (Int64 c)
| VFloat  : forall c, Valid (Float c)
| VDouble : forall c, Valid (Double c)
| VFixRaw : forall xs,
  length xs < pow 5 -> Valid (FixRaw xs)
| VRaw16 : forall xs,
  length xs < pow 16 -> Valid (Raw16 xs)
| VRaw32 : forall xs,
  length xs < pow 32 -> Valid (Raw32 xs)
| VFixArrayNil :
  Valid (FixArray [])
| VFixArrayCons : forall x xs,
  Valid x ->
  Valid (FixArray xs) ->
  length (x::xs) < pow 4 ->
  Valid (FixArray (x::xs))
| VArray16Nil :
  Valid (Array16 [])
| VArray16Cons: forall x xs,
  Valid x ->
  Valid (Array16 xs) ->
  length (x::xs) < pow 16 ->
  Valid (Array16 (x::xs))
| VArray32Nil :
  Valid (Array32 [])
| VArray32Cons : forall x xs,
  Valid x ->
  Valid (Array32 xs) ->
  length (x::xs) < pow 32 ->
  Valid (Array32 (x::xs))
| VFixMapNil:
  Valid (FixMap [])
| VFixMapCons : forall k v xs,
  Valid k ->
  Valid v ->
  Valid (FixMap xs)  ->
  length ((k,v)::xs) < pow 4 ->
  Valid (FixMap ((k,v)::xs))
| VMap16Nil :
  Valid (Map16 [])
| VMap16Cons : forall k v xs,
  Valid k ->
  Valid v ->
  Valid (Map16 xs)  ->
  length ((k,v)::xs) < pow 16 ->
  Valid (Map16 ((k,v)::xs))
| VMap32Nil :
  Valid (Map32 [])
| VMap32Cons : forall k v xs,
  Valid k ->
  Valid v ->
  Valid (Map32 xs)  ->
  length ((k,v)::xs) < pow 32 ->
  Valid (Map32 ((k,v)::xs)).

Lemma varray16_inv1: forall x xs,
  Valid (Array16 (x::xs)) ->
  ("000", "000") <> ascii16_of_nat (length (x :: xs)).
Proof.
intros.
apply ascii16_not_O.
split; [ apply length_lt_O | inversion H; auto ].
Qed.

Lemma varray16_inv2 : forall A (x y : A) xs ys,
  pow 16 > length (x :: xs) ->
  pow 16 > length (y :: ys) ->
  ascii16_of_nat (length (x :: xs)) = ascii16_of_nat (length (y :: ys)) ->
  ascii16_of_nat (length xs) = ascii16_of_nat (length ys).
Proof.
intros.
apply ascii16_of_nat_eq in H1; auto.
Qed.

