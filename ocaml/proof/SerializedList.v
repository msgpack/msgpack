Require Import Ascii List.
Require Import ListUtil Object MultiByte Util SerializeSpec Pow.

Open Scope char_scope.

Definition lift P (o : object) (b : list ascii) := forall os bs,
  P os bs -> P (o::os) (b ++ bs).

Inductive SerializedList : list object -> list ascii8 -> Prop :=
| SLbot :
  SerializedList [] []
| SLNil:
  lift SerializedList Nil ["192"]
| SLTrue :
  lift SerializedList (Bool true)  ["195"]
| SLFalse :
  lift SerializedList (Bool false) ["194"]
| SLPFixnum : forall x1 x2 x3 x4 x5 x6 x7,
  lift SerializedList (PFixnum   (Ascii x1 x2 x3 x4 x5 x6 x7 false))
                      [Ascii x1 x2 x3 x4 x5 x6 x7 false]
| SLNFixnum : forall  x1 x2 x3 x4 x5,
  lift SerializedList (NFixnum   (Ascii x1 x2 x3 x4 x5 true true true))
                      [Ascii x1 x2 x3 x4 x5 true true true]
| SLUint8 : forall c,
  lift SerializedList (Uint8 c) ("204" :: list_of_ascii8 c)
| SLUint16 : forall c,
  lift SerializedList (Uint16 c) ("205" :: list_of_ascii16 c)
| SLUint32 : forall c,
  lift SerializedList (Uint32 c) ("206" :: list_of_ascii32 c)
| SLUint64 : forall c,
  lift SerializedList (Uint64 c) ("207" :: list_of_ascii64 c)
| SLInt8 : forall c,
  lift SerializedList (Int8 c) ("208" :: list_of_ascii8 c)
| SLInt16 : forall c,
  lift SerializedList (Int16 c) ("209" :: list_of_ascii16 c)
| SLInt32 : forall c,
  lift SerializedList (Int32 c) ("210" :: list_of_ascii32 c)
| SLInt64 : forall c,
  lift SerializedList (Int64 c) ("211" :: list_of_ascii64 c)
| SLFloat : forall c,
  lift SerializedList (Float c) ("202" :: list_of_ascii32 c)
| SLDouble : forall c,
  lift SerializedList (Double c) ("203" :: list_of_ascii64 c)
| SLFixRaw : forall cs b1 b2 b3 b4 b5,
  Ascii b1 b2 b3 b4 b5 false false false = ascii8_of_nat (length cs) ->
  List.length cs < pow 5 ->
  lift SerializedList (FixRaw cs) ((Ascii b1 b2 b3 b4 b5 true false true) :: cs)
| SLRaw16 : forall cs s1 s2,
  (s1,s2) =  ascii16_of_nat (length cs) ->
  List.length cs < pow 16 ->
  lift SerializedList (Raw16 cs) ("218" :: s1 :: s2 :: cs)
| SLRaw32 : forall cs s1 s2 s3 s4,
  ((s1,s2),(s3,s4)) =  ascii32_of_nat (length cs) ->
  List.length cs < pow 32 ->
   lift SerializedList (Raw32 cs) ("219" :: s1 :: s2 :: s3 :: s4 :: cs)
| SLFixArray : forall os n b1 b2 b3 b4 xs ys bs,
  SerializedList os bs ->
  (xs,ys) = split_at n os ->
  n < pow 4 ->
  (Ascii b1 b2 b3 b4 false false false false) = ascii8_of_nat n ->
  SerializedList ((FixArray xs) :: ys) ((Ascii b1 b2 b3 b4 true false false true) :: bs)
| SLArray16 : forall os n xs ys bs s1 s2,
  SerializedList os bs ->
  (xs,ys) = split_at n os ->
  n < pow 16 ->
  (s1,s2) = ascii16_of_nat n ->
  SerializedList ((Array16 xs)::ys) ("220" :: s1 :: s2 :: bs)
| SLArray32 : forall os n xs ys bs s1 s2 s3 s4,
  SerializedList os bs ->
  (xs,ys) = split_at n os ->
  n < pow 32 ->
  ((s1,s2),(s3,s4)) = ascii32_of_nat n ->
  SerializedList ((Array32 xs)::ys) ("221" :: s1 :: s2 :: s3 :: s4 :: bs)
| SLFixMap : forall os n b1 b2 b3 b4 xs ys bs,
  SerializedList os bs ->
  (xs,ys) = split_at (2 * n) os ->
  List.length xs = 2 * n ->
  n < pow 4 ->
  (Ascii b1 b2 b3 b4 false false false false) = ascii8_of_nat n ->
  SerializedList ((FixMap (pair xs)) :: ys) ((Ascii b1 b2 b3 b4 false false false true) :: bs)
| SLMap16 : forall os n xs ys bs s1 s2,
  SerializedList os bs ->
  (xs,ys) = split_at (2 * n) os ->
  List.length xs = 2 * n ->
  n < pow 16 ->
  (s1,s2) = ascii16_of_nat n ->
  SerializedList ((Map16 (pair xs))::ys) ("222" :: s1 :: s2 :: bs)
| SLMap32 : forall os n xs ys bs s1 s2 s3 s4,
  SerializedList os bs ->
  (xs,ys) = split_at (2 * n) os ->
  List.length xs = 2 * n ->
  n < pow 32 ->
  ((s1,s2),(s3,s4)) = ascii32_of_nat n ->
  SerializedList ((Map32 (pair xs))::ys) ("223" :: s1 :: s2 :: s3 :: s4 :: bs).

Lemma app_cons: forall A (xs ys zs : list A) x,
  x :: (xs ++ ys) ++ zs = x :: (xs ++ ys ++ zs).
Proof.
induction xs; intros; simpl; auto.
rewrite (IHxs ys zs a).
reflexivity.
Qed.

Definition Soundness o bs := forall os bs',
  Serialized o bs ->
  Valid o ->
  SerializedList os bs' ->
  SerializedList (o :: os) (bs ++ bs').

Ltac straitfoward P :=
 intros;
 unfold Soundness;
 intros os bs' Hs Hv Hsl;
 apply P;
 auto.

Lemma soundness_nil:
  Soundness Nil ["192"].
Proof.
straitfoward SLNil.
Qed.

Lemma soundness_false:
  Soundness (Bool false) ["194"].
Proof.
straitfoward SLFalse.
Qed.

Lemma soundness_true:
  Soundness (Bool true) ["195"].
Proof.
straitfoward SLTrue.
Qed.

Lemma soundness_pfixnum: forall x1 x2 x3 x4 x5 x6 x7,
  Soundness (PFixnum   (Ascii x1 x2 x3 x4 x5 x6 x7 false))
          [Ascii x1 x2 x3 x4 x5 x6 x7 false].
Proof.
straitfoward SLPFixnum.
Qed.

Lemma soundness_nfixnum: forall x1 x2 x3 x4 x5,
  Soundness (NFixnum   (Ascii x1 x2 x3 x4 x5 true true true))
          [Ascii x1 x2 x3 x4 x5 true true true].
Proof.
straitfoward SLNFixnum.
Qed.

Lemma soundness_uint8 : forall c,
  Soundness (Uint8 c) ("204"::list_of_ascii8 c).
Proof.
straitfoward SLUint8.
Qed.

Lemma soundness_uint16 : forall c,
  Soundness (Uint16 c) ("205"::list_of_ascii16 c).
Proof.
straitfoward SLUint16.
Qed.

Lemma soundness_uint32 : forall c,
  Soundness (Uint32 c) ("206"::list_of_ascii32 c).
Proof.
straitfoward SLUint32.
Qed.

Lemma soundness_uint64 : forall c,
  Soundness (Uint64 c) ("207"::list_of_ascii64 c).
Proof.
straitfoward SLUint64.
Qed.

Lemma soundness_int8 : forall c,
  Soundness (Int8 c) ("208"::list_of_ascii8 c).
Proof.
straitfoward SLInt8.
Qed.

Lemma soundness_int16 : forall c,
  Soundness (Int16 c) ("209"::list_of_ascii16 c).
Proof.
straitfoward SLInt16.
Qed.

Lemma soundness_int32 : forall c,
  Soundness (Int32 c) ("210"::list_of_ascii32 c).
Proof.
straitfoward SLInt32.
Qed.

Lemma soundness_int64 : forall c,
  Soundness (Int64 c) ("211"::list_of_ascii64 c).
Proof.
straitfoward SLInt64.
Qed.

Lemma soundness_float : forall c,
  Soundness (Float c) ("202"::list_of_ascii32 c).
Proof.
straitfoward SLFloat.
Qed.

Lemma soundness_double : forall c,
  Soundness (Double c) ("203"::list_of_ascii64 c).
Proof.
straitfoward SLDouble.
Qed.

Lemma soundness_fixraw : forall cs b1 b2 b3 b4 b5,
  Ascii b1 b2 b3 b4 b5 false false false = ascii8_of_nat (length cs) ->
  Soundness (FixRaw cs) ((Ascii b1 b2 b3 b4 b5 true false true)::cs).
Proof.
straitfoward SLFixRaw.
inversion Hv.
assumption.
Qed.

Lemma soundness_raw16: forall cs s1 s2,
  (s1,s2) =  ascii16_of_nat (length cs) ->
  Soundness (Raw16 cs) ("218"::s1::s2::cs).
Proof.
straitfoward SLRaw16.
inversion Hv.
assumption.
Qed.

Lemma soundness_raw32 : forall cs s1 s2 s3 s4,
  ((s1,s2),(s3,s4)) =  ascii32_of_nat (length cs) ->
  Soundness (Raw32 cs) ("219"::s1::s2::s3::s4::cs).
Proof.
straitfoward SLRaw32.
inversion Hv.
assumption.
Qed.

Lemma soundness_fixarray_nil :
  Soundness (FixArray []) ["144"].
Proof.
unfold Soundness.
intros.
apply (SLFixArray os 0); auto.
Qed.

Lemma soundness_array16_nil :
  Soundness (Array16 []) ["220"; "000"; "000"].
Proof.
unfold Soundness.
intros.
apply (SLArray16 os 0 _ _ bs' "000" "000"); auto.
rewrite <- ascii16_of_nat_O.
reflexivity.
Qed.

Lemma soundness_array32_nil:
  Soundness (Array32 []) ["221"; "000"; "000";"000"; "000"].
Proof.
unfold Soundness.
intros.
apply (SLArray32 os 0 _ _ bs' "000" "000" "000" "000"); auto.
rewrite <- ascii32_of_nat_O.
reflexivity.
Qed.

Lemma soundness_fixmap_nil:
  Soundness (FixMap []) ["128"].
Proof.
unfold Soundness.
intros.
apply (SLFixMap os 0 _ _ _ _ [] _ bs'); auto.
Qed.

Lemma soundness_map16_nil:
  Soundness (Map16 []) ["222"; "000"; "000"].
Proof.
unfold Soundness.
intros.
apply (SLMap16 os 0 [] _ bs' "000" "000"); auto.
rewrite <- ascii16_of_nat_O.
reflexivity.
Qed.

Lemma soundness_map32_nil:
  Soundness (Map32 []) ["223"; "000"; "000";"000"; "000"].
Proof.
unfold Soundness.
intros.
apply (SLMap32 os 0 [] _ bs' "000" "000" "000" "000"); auto.
rewrite <- ascii32_of_nat_O.
reflexivity.
Qed.

Lemma soundness_fixarray_cons: forall x xs y ys b1 b2 b3 b4 b5 b6 b7 b8,
  Ascii b1 b2 b3 b4 false false false false = ascii8_of_nat (length xs) ->
  Ascii b5 b6 b7 b8 false false false false = ascii8_of_nat (length (x::xs)) ->
  Serialized x y ->
  Soundness x y ->
  Serialized (FixArray xs) ((Ascii b1 b2 b3 b4 true false false true)::ys) ->
  Soundness (FixArray xs) ((Ascii b1 b2 b3 b4 true false false true)::ys) ->
  Soundness (FixArray (x :: xs)) ((Ascii b5 b6 b7 b8 true false false true)::y ++ ys).
Proof.
unfold Soundness.
intros.
simpl.
rewrite app_cons.
inversion H6.
apply (SLFixArray (x::(xs++os)) (length (x::xs))); auto.
 apply (H2 (xs++os) (ys++bs')) in H1; auto.
 apply (H4 os bs') in H3; auto.
 inversion H3.
 apply split_at_soundness in H21.
 rewrite H21 in *.
 assumption.

 apply split_at_length.
Qed.

Lemma soundness_array16_cons: forall x xs t1 t2 s1 s2 y ys,
  (t1, t2) = ascii16_of_nat (length xs) ->
  (s1, s2) = ascii16_of_nat (length (x :: xs)) ->
  Serialized x y ->
  Soundness x y ->
  Serialized (Array16 xs) ("220" :: t1 :: t2 :: ys) ->
  Soundness (Array16 xs) ("220" :: t1 :: t2 :: ys) ->
  Soundness (Array16 (x :: xs)) ("220" :: s1 :: s2 :: y ++ ys).
Proof.
unfold Soundness.
intros.
simpl.
rewrite app_cons.
inversion H6.
apply (SLArray16 (x::(xs++os)) (length (x::xs))); auto.
 apply (H2 (xs++os) (ys++bs')) in H1; auto.
 apply (H4 os bs') in H3; auto.
 inversion H3.
 apply split_at_soundness in H19.
 rewrite H19 in *.
 assumption.

 apply split_at_length.
Qed.

Lemma soundness_array32_cons: forall x xs y ys s1 s2 s3 s4 t1 t2 t3 t4,
  ((t1,t2),(t3,t4)) = ascii32_of_nat (length xs) ->
  ((s1,s2),(s3,s4)) = ascii32_of_nat (length (x::xs)) ->
  Serialized x y ->
  Soundness x y ->
  Serialized (Array32 xs) ("221"::t1::t2::t3::t4::ys) ->
  Soundness (Array32 xs) ("221"::t1::t2::t3::t4::ys) ->
  Soundness (Array32 (x::xs)) ("221"::s1::s2::s3::s4::y ++ ys).
Proof.
unfold Soundness.
intros.
simpl.
rewrite app_cons.
inversion H6.
apply (SLArray32 (x::(xs++os)) (length (x::xs))); auto.
 apply (H2 (xs++os) (ys++bs')) in H1; auto.
 apply (H4 os bs') in H3; auto.
 inversion H3.
 apply split_at_soundness in H21.
 rewrite H21 in *.
 assumption.

 apply split_at_length.
Qed.


Lemma soundness_fixmap_cons: forall x1 x2 xs y1 y2 ys b1 b2 b3 b4 b5 b6 b7 b8,
  Ascii b1 b2 b3 b4 false false false false = ascii8_of_nat (length xs) ->
  Ascii b5 b6 b7 b8 false false false false = ascii8_of_nat (length ((x1,x2)::xs)) ->
  Serialized x1 y1 -> Soundness x1 y1 ->
  Serialized x2 y2 -> Soundness x2 y2 ->
  Serialized (FixMap xs) (Ascii b1 b2 b3 b4 false false false true :: ys) ->
  Soundness (FixMap xs) (Ascii b1 b2 b3 b4 false false false true :: ys) ->
  Soundness (FixMap ((x1, x2) :: xs)) (Ascii b5 b6 b7 b8 false false false true :: y1 ++ y2 ++ ys).
Proof with auto.
unfold Soundness.
intros.
simpl.
rewrite app_cons.
rewrite <- app_assoc.
rewrite <- (pair_unpair _ ( (x1, x2) :: xs )).
inversion H8.
apply (SLFixMap (x1::x2::unpair xs++os)  (length ((x1,x2)::xs))); auto.
 apply (H2 ( x2 :: unpair xs ++ os ) ( y2 ++ ys ++ bs' )) in H1; auto.
 apply (H4 ( unpair xs ++ os) ( ys ++ bs')) in H3; auto.
 apply (H6 os bs') in H5; auto.
 inversion H5.
 rewrite (unpair_pair _ n); auto.
 apply split_at_soundness in H25.
 rewrite <- H25...

 apply unpair_split_at.

 apply unpair_length.
Qed.

Lemma soundness_map16_cons: forall x1 x2 xs y1 y2 ys s1 s2 t1 t2,
  (t1, t2) = ascii16_of_nat (length xs) ->
  (s1, s2) = ascii16_of_nat (length ((x1, x2) :: xs)) ->
  Serialized x1 y1 ->
  Soundness x1 y1 ->
  Serialized x2 y2 ->
  Soundness x2 y2 ->
  Serialized (Map16 xs) ("222" :: t1 :: t2 :: ys) ->
  Soundness (Map16 xs) ("222" :: t1 :: t2 :: ys) ->
  Soundness (Map16 ((x1, x2) :: xs)) ("222" :: s1 :: s2 :: y1 ++ y2 ++ ys).
Proof with auto.
unfold Soundness.
intros.
simpl.
rewrite app_cons.
rewrite <- app_assoc.
rewrite <- (pair_unpair _ ( (x1, x2) :: xs )).
inversion H8.
apply (SLMap16 (x1::x2::unpair xs++os)  (length ((x1,x2)::xs))); auto.
 apply (H2 ( x2 :: unpair xs ++ os ) ( y2 ++ ys ++ bs' )) in H1; auto.
 apply (H4 ( unpair xs ++ os) ( ys ++ bs')) in H3; auto.
 apply (H6 os bs') in H5; auto.
 inversion H5.
 rewrite (unpair_pair _ n); auto.
 apply split_at_soundness in H23.
 rewrite <- H23...

 apply unpair_split_at.

 apply unpair_length.
Qed.

Lemma soundness_map32_cons : forall x1 x2 xs y1 y2 ys s1 s2 s3 s4 t1 t2 t3 t4,
  (t1, t2, (t3, t4)) = ascii32_of_nat (length xs) ->
  (s1, s2, (s3, s4)) = ascii32_of_nat (length ((x1, x2) :: xs)) ->
  Serialized x1 y1 ->
  Soundness x1 y1 ->
  Serialized x2 y2 ->
  Soundness x2 y2 ->
  Serialized (Map32 xs) ("223" :: t1 :: t2 :: t3 :: t4 :: ys) ->
  Soundness (Map32 xs) ("223" :: t1 :: t2 :: t3 :: t4 :: ys) ->
  Soundness (Map32 ((x1, x2) :: xs)) ("223" :: s1 :: s2 :: s3 :: s4 :: y1 ++ y2 ++ ys).
Proof with auto.
unfold Soundness.
intros.
simpl.
rewrite app_cons.
rewrite <- app_assoc.
rewrite <- (pair_unpair _ ( (x1, x2) :: xs )).
inversion H8.
apply (SLMap32 (x1::x2::unpair xs++os)  (length ((x1,x2)::xs))); auto.
 apply (H2 ( x2 :: unpair xs ++ os ) ( y2 ++ ys ++ bs' )) in H1; auto.
 apply (H4 ( unpair xs ++ os) ( ys ++ bs')) in H3; auto.
 apply (H6 os bs') in H5; auto.
 inversion H5.
 rewrite (unpair_pair _ n); auto.
 apply split_at_soundness in H25.
 rewrite <- H25...

 apply unpair_split_at.

 apply unpair_length.
Qed.

Lemma soundness_intro : forall obj xs,
  (Serialized obj xs -> Soundness obj xs) ->
  Soundness obj xs.
Proof.
unfold Soundness.
intros.
eapply H in H0; auto.
apply H0.
auto.
Qed.

Hint Resolve
  soundness_true soundness_false
  soundness_nil soundness_pfixnum soundness_nfixnum
  soundness_uint8 soundness_uint16 soundness_uint32 soundness_uint64
  soundness_int8  soundness_int16  soundness_int32  soundness_int64
  soundness_float soundness_double
  soundness_raw16 soundness_raw32
  soundness_fixarray_nil soundness_array16_nil soundness_array32_nil
  soundness_fixmap_nil soundness_map16_nil soundness_map32_nil
  : soundness.


Theorem serialize_soundness : forall obj xs,
  Soundness obj xs.
Proof.
intros.
apply soundness_intro.
intro.
pattern obj,xs.
apply Serialized_ind; intros; auto with soundness.
 apply soundness_fixraw; auto.
 apply soundness_fixarray_cons with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); auto.
 apply soundness_array16_cons with (t1:=t1) (t2:=t2); auto.
 apply soundness_array32_cons with (t1:=t1) (t2:=t2) (t3:=t3) (t4:=t4); auto.
 apply soundness_fixmap_cons with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); auto.
 apply soundness_map16_cons with (t1:=t1) (t2:=t2); auto.
 apply soundness_map32_cons with (t1:=t1) (t2:=t2) (t3:=t3) (t4:=t4); auto.
Qed.

Lemma sl_soundness: forall o os bs bs',
  Serialized o bs ->
  Valid o ->
  SerializedList os bs' ->
  SerializedList (o :: os) (bs ++ bs').
Proof.
intros.
apply soundness_intro; auto.
intro.
pattern o, bs.
apply Serialized_ind; intros; auto with soundness.
 apply soundness_fixraw; auto.
 apply soundness_fixarray_cons with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); auto.
 apply soundness_array16_cons with (t1:=t1) (t2:=t2); auto.
 apply soundness_array32_cons with (t1:=t1) (t2:=t2) (t3:=t3) (t4:=t4); auto.
 apply soundness_fixmap_cons with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); auto.
 apply soundness_map16_cons with (t1:=t1) (t2:=t2); auto.
 apply soundness_map32_cons with (t1:=t1) (t2:=t2) (t3:=t3) (t4:=t4); auto.
Qed.

