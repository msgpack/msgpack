Require Import Ascii List.
Require Import ListUtil Object MultiByte Util SerializeSpec ProofUtil.

Open Scope char_scope.

Fixpoint serialize (obj : object) : list ascii8 :=
  match obj with
    | Nil        => [ "192" ]
    | Bool false => [ "194" ]
    | Bool true  => [ "195" ]
    | PFixnum (Ascii b1 b2 b3 b4 b5 b6 b7 _) =>
      [ Ascii b1 b2 b3 b4 b5 b6 b7 false ]
    | NFixnum (Ascii b1 b2 b3 b4 b5 _ _ _) =>
      [ Ascii b1 b2 b3 b4 b5 true true true ]
    | Uint8  c => "204"::list_of_ascii8 c
    | Uint16 c => "205"::list_of_ascii16 c
    | Uint32 c => "206"::list_of_ascii32 c
    | Uint64 c => "207"::list_of_ascii64 c
    | Int8   c => "208"::list_of_ascii8 c
    | Int16  c => "209"::list_of_ascii16 c
    | Int32  c => "210"::list_of_ascii32 c
    | Int64  c => "211"::list_of_ascii64 c
    | Float  c => "202"::list_of_ascii32 c
    | Double c => "203"::list_of_ascii64 c
    | FixRaw xs =>
      match ascii8_of_nat @@ length xs with
        | Ascii b1 b2 b3 b4 b5 _ _ _ =>
          (Ascii b1 b2 b3 b4 b5 true false true)::xs
      end
    | Raw16 xs =>
      let (s1,s2) :=
        ascii16_of_nat @@ length xs
      in
        "218"::s1::s2::xs
    | Raw32 xs =>
      match ascii32_of_nat @@ length xs with
        | ((s1,s2),(s3,s4)) =>
          "219"::s1::s2::s3::s4::xs
      end
    | FixArray xs =>
      let ys :=
        flat_map serialize xs
      in
      match ascii8_of_nat @@ length xs with
        | Ascii b1 b2 b3 b4 _ _ _ _ =>
          (Ascii b1 b2 b3 b4 true false false true)::ys
      end
    | Array16 xs =>
      let ys :=
        flat_map serialize xs
      in
      let (s1, s2) :=
        ascii16_of_nat (length  xs)
      in
        "220"::s1::s2::ys
    | Array32 xs =>
      let ys :=
        flat_map serialize xs
      in
      match ascii32_of_nat @@ length xs with
        | ((s1,s2),(s3,s4)) =>
         "221"::s1::s2::s3::s4::ys
      end
    | FixMap xs =>
      let ys :=
        flat_map (fun p => serialize (fst p) ++ serialize (snd p)) xs
      in
      match ascii8_of_nat @@ length xs with
        | Ascii b1 b2 b3 b4 _ _ _ _ =>
          (Ascii b1 b2 b3 b4 false false false true)::ys
      end
    | Map16 xs =>
      let ys :=
        flat_map (fun p => serialize (fst p) ++ serialize (snd p)) xs
      in
      let (s1, s2) :=
        ascii16_of_nat (length  xs)
      in
        "222"::s1::s2::ys
    | Map32 xs =>
      let ys :=
        flat_map (fun p => serialize (fst p) ++ serialize (snd p)) xs
      in
      match ascii32_of_nat @@ length xs with
        | ((s1,s2),(s3,s4)) =>
         "223"::s1::s2::s3::s4::ys
      end
  end.

Definition Correct obj xs :=
  Serialized obj xs ->
  serialize obj = xs.

Ltac straitfoward :=
  unfold Correct;
  intros;
  simpl;
  reflexivity.

Lemma correct_nil:
  Correct Nil ["192"].
Proof.
straitfoward.
Qed.

Lemma correct_false:
  Correct (Bool false) ["194"].
Proof.
straitfoward.
Qed.

Lemma correct_true:
  Correct (Bool true) ["195"].
Proof.
straitfoward.
Qed.

Lemma correct_pfixnum: forall x1 x2 x3 x4 x5 x6 x7,
  Correct (PFixnum   (Ascii x1 x2 x3 x4 x5 x6 x7 false))
          [Ascii x1 x2 x3 x4 x5 x6 x7 false].
Proof.
straitfoward.
Qed.

Lemma correct_nfixnum: forall x1 x2 x3 x4 x5,
  Correct (NFixnum   (Ascii x1 x2 x3 x4 x5 true true true))
          [Ascii x1 x2 x3 x4 x5 true true true].
Proof.
straitfoward.
Qed.

Lemma correct_uint8 : forall c,
  Correct (Uint8 c) ("204"::list_of_ascii8 c).
Proof.
straitfoward.
Qed.

Lemma correct_uint16 : forall c,
  Correct (Uint16 c) ("205"::list_of_ascii16 c).
Proof.
straitfoward.
Qed.

Lemma correct_uint32 : forall c,
  Correct (Uint32 c) ("206"::list_of_ascii32 c).
Proof.
straitfoward.
Qed.

Lemma correct_uint64 : forall c,
  Correct (Uint64 c) ("207"::list_of_ascii64 c).
Proof.
straitfoward.
Qed.

Lemma correct_int8 : forall c,
  Correct (Int8 c) ("208"::list_of_ascii8 c).
Proof.
straitfoward.
Qed.

Lemma correct_int16 : forall c,
  Correct (Int16 c) ("209"::list_of_ascii16 c).
Proof.
straitfoward.
Qed.

Lemma correct_int32 : forall c,
  Correct (Int32 c) ("210"::list_of_ascii32 c).
Proof.
straitfoward.
Qed.

Lemma correct_int64 : forall c,
  Correct (Int64 c) ("211"::list_of_ascii64 c).
Proof.
straitfoward.
Qed.

Lemma correct_float : forall c,
  Correct (Float c) ("202"::list_of_ascii32 c).
Proof.
straitfoward.
Qed.

Lemma correct_double : forall c,
  Correct (Double c) ("203"::list_of_ascii64 c).
Proof.
straitfoward.
Qed.

Lemma correct_fixraw : forall cs b1 b2 b3 b4 b5,
  Ascii b1 b2 b3 b4 b5 false false false = ascii8_of_nat (length cs) ->
  Correct (FixRaw cs) ((Ascii b1 b2 b3 b4 b5 true false true)::cs).
Proof.
unfold Correct.
intros.
inversion H0.
simpl.
unfold atat.
rewrite_for (ascii8_of_nat (length cs)).
reflexivity.
Qed.

Lemma correct_raw16: forall cs s1 s2,
  (s1,s2) =  ascii16_of_nat (length cs) ->
  Correct (Raw16 cs) ("218"::s1::s2::cs).
Proof.
unfold Correct.
intros.
inversion H0.
simpl.
unfold atat.
rewrite_for (ascii16_of_nat (length cs)).
reflexivity.
Qed.

Lemma correct_raw32 : forall cs s1 s2 s3 s4,
  ((s1,s2),(s3,s4)) =  ascii32_of_nat (length cs) ->
  Correct (Raw32 cs) ("219"::s1::s2::s3::s4::cs).
Proof.
unfold Correct.
intros.
inversion H0.
simpl.
unfold atat.
rewrite_for (ascii32_of_nat (length cs)).
reflexivity.
Qed.

Lemma correct_fixarray_nil :
  Correct (FixArray []) ["144"].
Proof.
straitfoward.
Qed.

Lemma correct_array16_nil :
  Correct (Array16 []) ["220"; "000"; "000"].
Proof.
unfold Correct.
intros.
simpl.
rewrite <- ascii16_of_nat_O.
reflexivity.
Qed.

Lemma correct_array32_nil:
  Correct (Array32 []) ["221"; "000"; "000";"000"; "000"].
Proof.
unfold Correct.
intros.
simpl.
unfold atat.
rewrite <- ascii32_of_nat_O.
reflexivity.
Qed.

Lemma correct_fixmap_nil:
  Correct (FixMap []) ["128"].
Proof.
straitfoward.
Qed.

Lemma correct_map16_nil:
  Correct (Map16 []) ["222"; "000"; "000"].
Proof.
unfold Correct.
intros.
simpl.
rewrite <- ascii16_of_nat_O.
reflexivity.
Qed.

Lemma correct_map32_nil:
  Correct (Map32 []) ["223"; "000"; "000";"000"; "000"].
Proof.
unfold Correct.
intros.
simpl.
unfold atat.
rewrite <- ascii32_of_nat_O.
reflexivity.
Qed.

Lemma correct_fixarray_cons: forall x xs y ys b1 b2 b3 b4 b5 b6 b7 b8,
  Ascii b1 b2 b3 b4 false false false false = ascii8_of_nat (length xs) ->
  Ascii b5 b6 b7 b8 false false false false = ascii8_of_nat (length (x::xs)) ->
  Serialized x y ->
  Correct x y ->
  Serialized (FixArray xs) ((Ascii b1 b2 b3 b4 true false false true)::ys) ->
  Correct (FixArray xs) ((Ascii b1 b2 b3 b4 true false false true)::ys) ->
  Correct (FixArray (x :: xs)) ((Ascii b5 b6 b7 b8 true false false true)::y ++ ys).
Proof.
unfold Correct.
intros.
simpl in *.
unfold atat in *.
rewrite_for (ascii8_of_nat (S (length xs))).
apply H2 in H1.
apply H4 in H3.
rewrite_for (ascii8_of_nat (length xs)).
rewrite_for y.
inversion H3.
reflexivity.
Qed.

Lemma correct_array16_cons: forall x xs t1 t2 s1 s2 y ys,
  (t1, t2) = ascii16_of_nat (length xs) ->
  (s1, s2) = ascii16_of_nat (length (x :: xs)) ->
  Serialized x y ->
  (Serialized x y -> Correct x y) ->
  Serialized (Array16 xs) ("220" :: t1 :: t2 :: ys) ->
  (Serialized (Array16 xs) ("220" :: t1 :: t2 :: ys) ->
    Correct (Array16 xs) ("220" :: t1 :: t2 :: ys)) ->
  Correct (Array16 (x :: xs)) ("220" :: s1 :: s2 :: y ++ ys).
Proof.
unfold Correct.
intros.
simpl in *.
rewrite_for (ascii16_of_nat (S (length xs))).
apply H2 in H1; auto.
apply H4 in H3; auto.
rewrite_for (ascii16_of_nat (length xs)).
rewrite_for y.
inversion H3.
reflexivity.
Qed.

Lemma correct_array32_cons: forall x xs y ys s1 s2 s3 s4 t1 t2 t3 t4,
  ((t1,t2),(t3,t4)) = ascii32_of_nat (length xs) ->
  ((s1,s2),(s3,s4)) = ascii32_of_nat (length (x::xs)) ->
  Serialized x y ->
  (Serialized x y -> Correct x y) ->
  Serialized (Array32 xs) ("221"::t1::t2::t3::t4::ys) ->
  (Serialized (Array32 xs) ("221"::t1::t2::t3::t4::ys) -> Correct (Array32 xs) ("221"::t1::t2::t3::t4::ys)) ->
  Correct (Array32 (x::xs)) ("221"::s1::s2::s3::s4::y ++ ys).
Proof.
unfold Correct.
intros.
simpl in *.
unfold atat in *.
rewrite_for (ascii32_of_nat (S (length xs))).
apply H2 in H1; auto.
apply H4 in H3; auto.
rewrite_for (ascii32_of_nat (length xs)).
rewrite_for y.
inversion H3.
reflexivity.
Qed.

Lemma correct_fixmap_cons: forall x1 x2 xs y1 y2 ys b1 b2 b3 b4 b5 b6 b7 b8,
  Ascii b1 b2 b3 b4 false false false false = ascii8_of_nat (length xs) ->
  Ascii b5 b6 b7 b8 false false false false = ascii8_of_nat (length ((x1,x2)::xs)) ->
  Serialized x1 y1 -> Correct x1 y1 ->
  Serialized x2 y2 -> Correct x2 y2 ->
  Serialized (FixMap xs) (Ascii b1 b2 b3 b4 false false false true :: ys) ->
  Correct (FixMap xs) (Ascii b1 b2 b3 b4 false false false true :: ys) ->
  Correct (FixMap ((x1, x2) :: xs)) (Ascii b5 b6 b7 b8 false false false true :: y1 ++ y2 ++ ys).
Proof.
unfold Correct.
intros.
simpl in *.
unfold atat in *.
rewrite_for (ascii8_of_nat (S (length xs))).
apply H2 in H1.
apply H4 in H3.
apply H6 in H5.
rewrite_for (ascii8_of_nat (length xs)).
rewrite_for y1.
rewrite_for y2.
inversion H5.
rewrite <- app_assoc.
reflexivity.
Qed.

Lemma correct_map16_cons: forall x1 x2 xs y1 y2 ys s1 s2 t1 t2,
  (t1, t2) = ascii16_of_nat (length xs) ->
  (s1, s2) = ascii16_of_nat (length ((x1, x2) :: xs)) ->
  Serialized x1 y1 ->
  Correct x1 y1 ->
  Serialized x2 y2 ->
  Correct x2 y2 ->
  Serialized (Map16 xs) ("222" :: t1 :: t2 :: ys) ->
  Correct (Map16 xs) ("222" :: t1 :: t2 :: ys) ->
  Correct (Map16 ((x1, x2) :: xs)) ("222" :: s1 :: s2 :: y1 ++ y2 ++ ys).
Proof.
unfold Correct.
intros.
simpl in *.
rewrite_for (ascii16_of_nat (S (length xs))).
apply H2 in H1.
apply H4 in H3.
apply H6 in H5.
rewrite_for (ascii16_of_nat (length xs)).
rewrite_for y1.
rewrite_for y2.
inversion H5.
rewrite <- app_assoc.
reflexivity.
Qed.

Lemma correct_map32_cons : forall x1 x2 xs y1 y2 ys s1 s2 s3 s4 t1 t2 t3 t4,
  (t1, t2, (t3, t4)) = ascii32_of_nat (length xs) ->
  (s1, s2, (s3, s4)) = ascii32_of_nat (length ((x1, x2) :: xs)) ->
  Serialized x1 y1 ->
  Correct x1 y1 ->
  Serialized x2 y2 ->
  Correct x2 y2 ->
  Serialized (Map32 xs) ("223" :: t1 :: t2 :: t3 :: t4 :: ys) ->
  Correct (Map32 xs) ("223" :: t1 :: t2 :: t3 :: t4 :: ys) ->
  Correct (Map32 ((x1, x2) :: xs)) ("223" :: s1 :: s2 :: s3 :: s4 :: y1 ++ y2 ++ ys).
Proof.
unfold Correct.
intros.
simpl in *.
unfold atat in *.
rewrite_for (ascii32_of_nat (S (length xs))).
apply H2 in H1.
apply H4 in H3.
apply H6 in H5.
rewrite_for (ascii32_of_nat (length xs)).
rewrite_for y1.
rewrite_for y2.
inversion H5.
rewrite <- app_assoc.
reflexivity.
Qed.

Lemma correct_intro : forall obj xs,
  (Serialized obj xs -> Correct obj xs) ->
  Correct obj xs.
Proof.
unfold Correct.
intros.
apply H in H0; auto.
Qed.

Hint Resolve
  correct_true correct_false
  correct_nil correct_pfixnum correct_nfixnum
  correct_uint8 correct_uint16 correct_uint32 correct_uint64
  correct_int8  correct_int16  correct_int32  correct_int64
  correct_float correct_double
  correct_raw16 correct_raw32
  correct_fixarray_nil correct_array16_nil correct_array32_nil
  correct_fixmap_nil correct_map16_nil correct_map32_nil
  : correct.


Theorem serialize_correct : forall obj xs,
  Correct obj xs.
Proof.
intros.
apply correct_intro.
intro.
pattern obj,xs.
apply Serialized_ind; intros; auto with correct.
 apply correct_fixraw; auto.
 apply correct_fixarray_cons with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); auto.
 apply correct_array16_cons with (t1:=t1) (t2:=t2); auto.
 apply correct_array32_cons with (t1:=t1) (t2:=t2) (t3:=t3) (t4:=t4); auto.
 apply correct_fixmap_cons with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); auto.
 apply correct_map16_cons with (t1:=t1) (t2:=t2); auto.
 apply correct_map32_cons with (t1:=t1) (t2:=t2) (t3:=t3) (t4:=t4); auto.
Qed.
