Require Import List Ascii.
Require Import ListUtil Object SerializeSpec MultiByte ProofUtil Pow.

Definition Prefix obj1 x : Prop := forall obj2 y xs ys,
  Serialized obj1 x ->
  Serialized obj2 y ->
  Valid obj1 ->
  Valid obj2 ->
  x ++ xs = y ++ ys ->
  x = y.

Ltac destruct_serialize obj y :=
  match goal with
    | [ H1 : _ ++ _ = y ++ _,
        H2 : Serialized obj y |- _ ] =>
    destruct y as [ | a ] ;
      [ inversion H2 | inversion H1 ; rewrite_for a; inversion H2 ];
      auto
  end.

(* 結果が1バイトになる変換 *)
Ltac straight_forward :=
  intros;
  unfold Prefix;
  intros obj2 y xs ys S1 S2 V1 V2 Happ;
  destruct_serialize obj2 y.

Lemma prefix_true :
  Prefix (Bool true) ["195"].
Proof.
straight_forward.
Qed.

Lemma prefix_false :
  Prefix (Bool false) ["194"].
Proof.
straight_forward.
Qed.

Lemma prefix_nil :
  Prefix Nil ["192"].
Proof.
straight_forward.
Qed.

Lemma prefix_pfixnum: forall x1 x2 x3 x4 x5 x6 x7,
  Prefix (PFixnum   (Ascii x1 x2 x3 x4 x5 x6 x7 false))
         [Ascii x1 x2 x3 x4 x5 x6 x7 false].
Proof.
straight_forward.
Qed.

Lemma prefix_nfixnum : forall  x1 x2 x3 x4 x5,
  Prefix (NFixnum   (Ascii x1 x2 x3 x4 x5 true true true))
         [Ascii x1 x2 x3 x4 x5 true true true].
Proof.
straight_forward.
Qed.

(* 結果が固定長多バイトになる変換 *)
Lemma prefix_same : forall A (x y xs ys : list A),
  x ++ xs = y ++ ys ->
  length x = length y ->
  x = y.
Proof.
induction x; induction y; intros; auto.
 simpl in H0.
 discriminate.

 simpl in H0.
 discriminate.

 inversion H.
 inversion H0.
 apply IHx in H3; auto.
 rewrite_for y.
 reflexivity.
Qed.

Ltac same_as_uint8 :=
  unfold Prefix;
  intros c obj2 y xs ys S1 S2 V1 V2 Happ;
  destruct_serialize obj2 y;
  rewrite_for y;
  apply prefix_same in Happ; simpl;  auto with ascii.

Lemma prefix_uint8 : forall c,
  Prefix (Uint8 c) ("204"::list_of_ascii8 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_uint16: forall c,
  Prefix (Uint16 c) ("205"::list_of_ascii16 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_uint32: forall c,
  Prefix (Uint32 c) ("206"::list_of_ascii32 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_uint64 : forall c,
  Prefix (Uint64 c) ("207"::list_of_ascii64 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_int8 : forall c,
  Prefix (Int8 c) ("208"::list_of_ascii8 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_int16 : forall c,
  Prefix (Int16 c) ("209"::list_of_ascii16 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_int32 : forall c,
  Prefix (Int32 c) ("210"::list_of_ascii32 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_int64 : forall c,
  Prefix (Int64 c) ("211"::list_of_ascii64 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_float : forall c,
  Prefix (Float c) ("202"::list_of_ascii32 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_double : forall c,
  Prefix (Double c) ("203"::list_of_ascii64 c).
Proof.
same_as_uint8.
Qed.

Lemma app_length_eq : forall A (xs ys zs ws : list A),
  xs ++zs = ys ++ ws ->
  length xs = length ys ->
  xs = ys.
Proof.
induction xs; induction ys; simpl; intros; auto.
 inversion H0.

 inversion H0.

 inversion H.
 inversion H0.
 assert (xs = ys); [| rewrite_for xs; auto].
 apply (IHxs _ zs ws); auto.
Qed.

Lemma prefix_fixraw : forall cs b1 b2 b3 b4 b5,
  Ascii b1 b2 b3 b4 b5 false false false = ascii8_of_nat (length cs) ->
  Prefix (FixRaw cs) ((Ascii b1 b2 b3 b4 b5 true false true)::cs).
Proof.
unfold Prefix.
intros.
destruct_serialize obj2 y.
rewrite_for obj2.
rewrite_for y.
inversion H2.
inversion H3.
assert (cs = cs0); [| rewrite_for cs; auto ].
apply (app_length_eq _ _ _ xs ys); auto.
rewrite <- (nat_ascii8_embedding (length cs)),
        <- (nat_ascii8_embedding (length cs0)).
 rewrite <- H, <- H8.
 reflexivity.

 transitivity (pow 5); auto with pow.

 transitivity (pow 5); auto with pow.
Qed.

Lemma prefix_raw16 : forall cs s1 s2,
  (s1,s2) =  ascii16_of_nat (length cs) ->
  Prefix (Raw16 cs) ("218"::s1::s2::cs).
Proof.
unfold Prefix.
intros.
destruct_serialize obj2 y.
rewrite_for obj2.
rewrite_for y.
inversion H2.
inversion H3.
inversion H7.
assert (cs = cs0); [| rewrite_for cs; auto ].
apply (app_length_eq _ _ _ xs ys); auto.
rewrite <- (nat_ascii16_embedding (length cs)),
        <- (nat_ascii16_embedding (length cs0)); auto.
rewrite <- H, <- H8, H12, H13.
reflexivity.
Qed.

Lemma prefix_raw32 : forall cs s1 s2 s3 s4,
  ((s1,s2),(s3,s4)) =  ascii32_of_nat (length cs) ->
  Prefix (Raw32 cs) ("219"::s1::s2::s3::s4::cs).
Proof.
unfold Prefix.
intros.
destruct_serialize obj2 y.
rewrite_for obj2.
rewrite_for y.
inversion H2.
inversion H3.
inversion H7.
assert (cs = cs0); [| rewrite_for cs; auto ].
apply (app_length_eq _ _ _ xs ys); auto.
rewrite <- (nat_ascii32_embedding (length cs)),
        <- (nat_ascii32_embedding (length cs0)); auto.
rewrite <- H, <- H8, H12, H13, H14, H15.
reflexivity.
Qed.

Lemma prefix_fixarray_nil:
  Prefix (FixArray []) ["144"].
Proof.
straight_forward.
apply ascii8_not_O in H7; [ contradiction |].
rewrite_for obj2.
inversion V2.
split; [ simpl; omega |].
transitivity (pow 4); [ exact H13 | apply pow_lt; auto ].
Qed.

Lemma  prefix_array16_nil:
  Prefix (Array16 []) ["220"; "000"; "000"].
Proof.
unfold Prefix; intros.
destruct_serialize obj2 y.
rewrite_for obj2.
rewrite_for y.
inversion H3.
rewrite <- H9, <- H11 in *.
assert (("000", "000") <> ascii16_of_nat ((length (x::xs0)))); try contradiction.
inversion H2.
apply ascii16_not_O.
split; auto.
simpl.
omega.
Qed.

Lemma  prefix_array32_nil:
  Prefix (Array32 []) ["221"; "000"; "000";"000"; "000"].
Proof.
unfold Prefix; intros.
destruct_serialize obj2 y.
rewrite_for obj2.
rewrite_for y.
inversion H3.
rewrite <- H9, <- H11, <- H12, <- H13 in *.
assert (("000", "000",("000","000")) <> ascii32_of_nat ((length (x::xs0)))); try contradiction.
inversion H2.
apply ascii32_not_O.
split; auto.
simpl.
omega.
Qed.

Lemma prefix_fixmap_nil:
  Prefix (FixMap []) ["128"].
Proof.
unfold Prefix; intros.
destruct_serialize obj2 y.
rewrite_for obj2.
apply ascii8_not_O in H12; [ contradiction |].
inversion H2.
split; [ simpl; omega |].
transitivity (pow 4); [ exact H21 |].
apply pow_lt.
auto.
Qed.

Lemma prefix_map16_nil:
  Prefix (Map16 []) ["222"; "000"; "000"].
Proof.
unfold Prefix; intros.
destruct_serialize obj2 y.
rewrite_for obj2.
rewrite_for y.
inversion H3.
rewrite <- H10, <- H12 in *.
assert (("000", "000") <> ascii16_of_nat ((length ((x1, x2)::xs0)))); try contradiction.
inversion H2.
apply ascii16_not_O.
split.
 simpl.
 omega.

 exact H19.
Qed.

Lemma prefix_map32_nil:
  Prefix (Map32 []) ["223"; "000"; "000";"000"; "000"].
Proof.
unfold Prefix; intros.
destruct_serialize obj2 y.
rewrite_for obj2.
rewrite_for y.
inversion H3.
rewrite <- H10, <- H12, <- H13, <- H14 in *.
assert (("000", "000",("000","000")) <> ascii32_of_nat ((length ((x1, x2)::xs0)))); try contradiction.
inversion H2.
apply ascii32_not_O.
split.
 simpl.
 omega.

 exact H21.
Qed.

Lemma prefix_fixarray_cons: forall x xs y ys b1 b2 b3 b4 b5 b6 b7 b8,
  Ascii b1 b2 b3 b4 false false false false = ascii8_of_nat (length xs) ->
  Ascii b5 b6 b7 b8 false false false false = ascii8_of_nat (length (x::xs)) ->
  Serialized x y ->
  Prefix x y ->
  Serialized (FixArray xs) ((Ascii b1 b2 b3 b4 true false false true)::ys) ->
  Prefix (FixArray xs) ((Ascii b1 b2 b3 b4 true false false true)::ys) ->
  Prefix (FixArray (x :: xs)) ((Ascii b5 b6 b7 b8 true false false true)::y ++ ys).
Proof.
unfold Prefix.
intros.
destruct_serialize obj2 y0; rewrite_for y0; rewrite_for obj2.
 inversion H6.
 rewrite_for b5.
 rewrite_for b6.
 rewrite_for b7.
 rewrite_for b8.
 apply ascii8_not_O in H0; [contradiction |].
 split; [ simpl; omega |].
 inversion H7.
 transitivity (pow 4); [ exact H19 | apply pow_lt; auto].

 assert (y ++ ys = y1 ++ ys1); [| rewrite_for (y++ys); reflexivity ].
 generalize H12; intro Happ; clear H12.
 rewrite <- (app_assoc y ys xs0), <- (app_assoc y1 ys1 ys0) in Happ.
 inversion H7.
 inversion H8.
 apply (H2 x0 y1 (ys++xs0) (ys1++ys0))in H1; auto.
 rewrite_for y1.
 apply app_same in Happ.
 apply (H4 (FixArray xs1) (Ascii b0 b9 b10 b11 true false false true :: ys1) xs0 ys0) in H3; auto.
  inversion H3.
  reflexivity.

  simpl.
  unfold ascii8 in *.
  rewrite <- Happ.
  rewrite H0 in H18.
  apply ascii8_of_nat_eq in H18; [
    | transitivity (pow 4); [| apply pow_lt]; auto
    | transitivity (pow 4); [| apply pow_lt]; auto ].
  simpl in H18.
  inversion H18.
  rewrite <- H28 in H16.
  rewrite <- H16 in H.
  inversion H.
  reflexivity.
Qed.

Lemma prefix_array16_cons: forall x xs y ys s1 s2 t1 t2,
  (t1, t2) = ascii16_of_nat (length xs) ->
  (s1, s2) = ascii16_of_nat (length (x :: xs)) ->
  Serialized x y ->
  Prefix x y ->
  Serialized (Array16 xs) ("220" :: t1 :: t2 :: ys) ->
  Prefix (Array16 xs) ("220" :: t1 :: t2 :: ys) ->
  Prefix (Array16 (x::xs)) ("220"::s1::s2::y ++ ys).
Proof.
unfold Prefix.
intros.
destruct_serialize obj2 y0.
 rewrite_for y0.
 inversion H9.
 rewrite_for s1.
 rewrite_for s2.
 apply ascii16_not_O in H0; [ contradiction |].
 inversion H7.
 split; [ simpl; omega | exact H17 ].

 rewrite_for y0.
 rewrite_for obj2.
 inversion H9.
 rewrite_for s0.
 rewrite_for s3.
 assert( y++ ys = y1 ++ ys1); [| rewrite_for (y++ys); reflexivity ].
 rewrite <- (app_assoc y ys xs0), <- (app_assoc y1 ys1 ys0) in H18.
 inversion H7.
 inversion H8.
 apply (H2 x0 y1 (ys++xs0) (ys1++ys0))in H1; auto.
 rewrite_for y1.
 apply app_same in H18.
 apply (H4 (Array16 xs1)  ("220" :: t0 :: t3 :: ys1) xs0 ys0) in H3; auto.
  inversion H3.
  reflexivity.

  simpl.
  unfold ascii8 in *.
  rewrite <- H18.
  rewrite H0 in H13.
  apply ascii16_of_nat_eq in H13; auto.
  simpl in H13.
  inversion H13.
  rewrite <- H26 in H11.
  rewrite <- H11 in H.
  inversion H.
  reflexivity.
Qed.

Lemma prefix_array32_cons: forall x xs y ys s1 s2 s3 s4 t1 t2 t3 t4,
  (t1, t2, (t3, t4)) = ascii32_of_nat (length xs) ->
  (s1, s2, (s3, s4)) = ascii32_of_nat (length (x :: xs)) ->
  Serialized x y ->
  Prefix x y ->
  Serialized (Array32 xs) ("221" :: t1 :: t2 :: t3 :: t4 :: ys) ->
  Prefix (Array32 xs) ("221" :: t1 :: t2 :: t3 :: t4 :: ys) ->
  Prefix (Array32 (x :: xs)) ("221" :: s1 :: s2 :: s3 :: s4 :: y ++ ys).
Proof.
unfold Prefix.
intros.
destruct_serialize obj2 y0;
 rewrite_for y0; rewrite_for obj2; inversion H9.
 rewrite_for s1.
 rewrite_for s2.
 rewrite_for s3.
 rewrite_for s4.
 apply ascii32_not_O in H0; [ contradiction |].
 inversion H7.
 split; [ simpl; omega | exact H15 ].

 rewrite_for s0.
 rewrite_for s5.
 rewrite_for s6.
 rewrite_for s7.
 assert( y++ ys = y1 ++ ys1); [| rewrite_for (y++ys); reflexivity ].
 rewrite <- (app_assoc y ys xs0), <- (app_assoc y1 ys1 ys0) in H20.
 inversion H7.
 inversion H8.
 apply (H2 x0 y1 (ys++xs0) (ys1++ys0)) in H1; auto.
 rewrite_for y1.
 apply app_same in H20.
 apply (H4 (Array32 xs1)  ("221" :: t0 :: t5 :: t6 :: t7 :: ys1) xs0 ys0) in H3; auto.
  inversion H3.
  reflexivity.

  simpl.
  unfold ascii8 in *.
  rewrite <- H20.
  rewrite H0 in H13.
  apply ascii32_of_nat_eq in H13; auto.
  simpl in H13.
  inversion H13.
  rewrite <- H26 in H11.
  rewrite <- H11 in H.
  inversion H.
  reflexivity.
Qed.

Lemma prefix_fixmap_cons: forall x1 x2 xs y1 y2 ys b1 b2 b3 b4 b5 b6 b7 b8,
  Ascii b1 b2 b3 b4 false false false false = ascii8_of_nat (length xs) ->
  Ascii b5 b6 b7 b8 false false false false = ascii8_of_nat (length ((x1,x2)::xs)) ->
  Serialized x1 y1 -> Prefix x1 y1 ->
  Serialized x2 y2 -> Prefix x2 y2 ->
  Serialized (FixMap xs) (Ascii b1 b2 b3 b4 false false false true :: ys) ->
  Prefix (FixMap xs) (Ascii b1 b2 b3 b4 false false false true :: ys) ->
  Prefix (FixMap ((x1, x2) :: xs)) (Ascii b5 b6 b7 b8 false false false true :: y1 ++ y2 ++ ys).
Proof.
unfold Prefix.
intros.
destruct_serialize obj2 y; rewrite_for y; rewrite_for obj2.
 rewrite_for b5.
 rewrite_for b6.
 rewrite_for b7.
 rewrite_for b8.
 apply ascii8_not_O in H0; [ contradiction |].
 split; [ simpl; omega |].
 inversion H9.
 transitivity (pow 4); auto.
 apply pow_lt.
 auto.

assert (y1 ++ y2 ++ ys = y0 ++ y3 ++ ys1); [| rewrite_for (y1 ++ y2 ++ ys); reflexivity ].
generalize H14; intro Happ; clear H14.
replace ((y1 ++ y2 ++ ys) ++ xs0) with (y1 ++ y2 ++ ys ++ xs0) in Happ;
  [| repeat (rewrite app_assoc); reflexivity ].
replace ((y0 ++ y3 ++ ys1) ++ ys0) with (y0 ++ y3 ++ ys1 ++ ys0) in Happ;
  [| repeat (rewrite app_assoc); reflexivity ].
inversion H9.
inversion H10.
apply (H2 x0 y0 (y2 ++ ys ++ xs0) (y3 ++ ys1 ++ ys0))in H1; auto.
rewrite_for y1.
apply app_same in Happ.
apply (H4 x3 y3 (ys ++ xs0) (ys1 ++ ys0)) in H3; auto.
rewrite_for y3.
apply app_same in Happ.
apply (H6 (FixMap xs1) (Ascii b0 b9 b10 b11 false false false true :: ys1) xs0 ys0) in H5; auto.
 inversion H5.
 reflexivity.

 simpl.
 unfold ascii8 in *.
 rewrite <- Happ.
 rewrite H0 in H20.
  apply ascii8_of_nat_eq in H20; [
    | transitivity (pow 4); [| apply pow_lt]; auto
    | transitivity (pow 4); [| apply pow_lt]; auto ].
 simpl in H20.
 inversion H20.
 rewrite H3 in H.
 rewrite <- H19 in H.
 inversion H.
 reflexivity.
Qed.

Lemma prefix_map16_cons: forall x1 x2 xs y1 y2 ys s1 s2 t1 t2,
  (t1, t2) = ascii16_of_nat (length xs) ->
  (s1, s2) = ascii16_of_nat (length ((x1, x2) :: xs)) ->
  Serialized x1 y1 ->
  Prefix x1 y1 ->
  Serialized x2 y2 ->
  Prefix x2 y2 ->
  Serialized (Map16 xs) ("222" :: t1 :: t2 :: ys) ->
  Prefix (Map16 xs) ("222" :: t1 :: t2 :: ys) ->
  Prefix (Map16 ((x1, x2) :: xs)) ("222" :: s1 :: s2 :: y1 ++ y2 ++ ys).
Proof.
unfold Prefix.
intros.
destruct_serialize obj2 y; rewrite_for y; rewrite_for obj2.
 inversion H11.
 rewrite_for s1.
 rewrite_for s2.
 apply ascii16_not_O in H0; [ contradiction |].
 inversion H9.
 split; [ simpl; omega | exact H20 ].

 inversion H14.
 rewrite_for s1.
 rewrite_for s2.
 assert( y1 ++ y2 ++ ys = y0 ++ y3  ++ ys1); [| rewrite_for (y1 ++ y2 ++ ys); reflexivity ].
 replace ((y1 ++ y2 ++ ys) ++ xs0) with (y1 ++ y2 ++ ys ++ xs0) in H21;
   [| repeat (rewrite app_assoc); reflexivity ].
 replace ((y0 ++ y3 ++ ys1) ++ ys0) with (y0 ++ y3 ++ ys1 ++ ys0) in H21;
   [| repeat (rewrite app_assoc); reflexivity ].
 inversion H9.
 inversion H10.
 apply (H2 x0 y0 (y2 ++ ys ++ xs0) (y3 ++ ys1 ++ ys0))in H1; auto.
 rewrite_for y1.
 apply app_same in H21.
 apply (H4 x3 y3 (ys ++ xs0) (ys1 ++ ys0)) in H3; auto.
 rewrite_for y3.
 apply app_same in H21.
 apply (H6 (Map16 xs1) ("222" :: t0 :: t3 :: ys1) xs0 ys0) in H5; auto.
  inversion H5.
  reflexivity.

  simpl.
  unfold ascii8 in *.
  rewrite <- H21.
  rewrite H0 in H15.
  apply ascii16_of_nat_eq in H15; auto.
  simpl in H15.
  inversion H15.
  rewrite H3 in H.
  rewrite <- H13 in H.
  inversion H.
  reflexivity.
Qed.

Lemma prefix_map32_cons : forall x1 x2 xs y1 y2 ys s1 s2 s3 s4 t1 t2 t3 t4,
  (t1, t2, (t3, t4)) = ascii32_of_nat (length xs) ->
  (s1, s2, (s3, s4)) = ascii32_of_nat (length ((x1, x2) :: xs)) ->
  Serialized x1 y1 ->
  Prefix x1 y1 ->
  Serialized x2 y2 ->
  Prefix x2 y2 ->
  Serialized (Map32 xs) ("223" :: t1 :: t2 :: t3 :: t4 :: ys) ->
  Prefix (Map32 xs) ("223" :: t1 :: t2 :: t3 :: t4 :: ys) ->
  Prefix (Map32 ((x1, x2) :: xs)) ("223" :: s1 :: s2 :: s3 :: s4 :: y1 ++ y2 ++ ys).
Proof.
unfold Prefix.
intros.
destruct_serialize obj2 y; rewrite_for y; rewrite_for obj2.
 inversion H11.
 rewrite_for s1.
 rewrite_for s2.
 rewrite_for s3.
 rewrite_for s4.
 apply ascii32_not_O in H0; [ contradiction |].
 inversion H9.
 split; [ simpl; omega | exact H20 ].

 inversion H14.
 rewrite_for s1.
 rewrite_for s2.
 rewrite_for s3.
 rewrite_for s4.
 generalize H23; intro Happ; clear H23.
 assert( y1 ++ y2 ++ ys = y0 ++ y3  ++ ys1); [| rewrite_for (y1 ++ y2 ++ ys); reflexivity ].
 replace ((y1 ++ y2 ++ ys) ++ xs0) with (y1 ++ y2 ++ ys ++ xs0) in Happ;
   [| repeat (rewrite app_assoc); reflexivity ].
 replace ((y0 ++ y3 ++ ys1) ++ ys0) with (y0 ++ y3 ++ ys1 ++ ys0) in Happ;
   [| repeat (rewrite app_assoc); reflexivity ].
 inversion H9.
 inversion H10.
 apply (H2 x0 y0 (y2 ++ ys ++ xs0) (y3 ++ ys1 ++ ys0)) in H1; auto.
 rewrite_for y1.
 apply app_same in Happ.
 apply (H4 x3 y3 (ys ++ xs0) (ys1 ++ ys0)) in H3; auto.
 rewrite_for y3.
 apply app_same in Happ.
 apply (H6 (Map32 xs1) ("223" :: t0 :: t5 :: t6 :: t7 :: ys1) xs0 ys0) in H5; auto.
  inversion H5.
  reflexivity.

  simpl.
  unfold ascii8 in *.
  rewrite <- Happ.
  rewrite H0 in H15.
  apply ascii32_of_nat_eq in H15; auto.
  simpl in H15.
  inversion H15.
  rewrite H3 in H.
  rewrite <- H13 in H.
  inversion H.
  reflexivity.
Qed.

Hint Resolve
  prefix_true prefix_false
  prefix_nil prefix_pfixnum prefix_nfixnum
  prefix_uint8 prefix_uint16 prefix_uint32 prefix_uint64
  prefix_int8  prefix_int16  prefix_int32  prefix_int64
  prefix_float prefix_double
  prefix_raw16 prefix_raw32
  prefix_fixarray_nil prefix_array16_nil prefix_array32_nil
  prefix_fixmap_nil prefix_map16_nil prefix_map32_nil
  : prefix.

Lemma prefix_intro: forall obj x,
  (Serialized obj x -> Prefix obj x)->
  Prefix obj x.
Proof.
unfold Prefix.
intros.
apply H with (xs:=xs) (ys:=ys) in H1; auto.
Qed.

Lemma prefix : forall obj1 x,
  Prefix obj1 x.
Proof.
intros.
apply prefix_intro.
intro.
pattern obj1,x.
apply Serialized_ind; intros; auto with prefix.
 apply prefix_fixraw; auto.
 apply prefix_fixarray_cons with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); auto.
 apply prefix_array16_cons with (t1:=t1) (t2:=t2); auto.
 apply prefix_array32_cons with (t1:=t1) (t2:=t2) (t3:=t3) (t4:=t4); auto.
 apply prefix_fixmap_cons with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); auto.
 apply prefix_map16_cons with (t1:=t1) (t2:=t2); auto.
 apply prefix_map32_cons with (t1:=t1) (t2:=t2) (t3:=t3) (t4:=t4); auto.
Qed.
