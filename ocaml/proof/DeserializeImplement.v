Require Import Ascii List.
Require Import ListUtil Object MultiByte Util SerializeSpec Pow SerializedList ProofUtil.

Open Scope char_scope.

Definition compact (xs : list object) : list ascii8 :=
  List.flat_map (fun x => match x with
                            FixRaw xs =>  xs
                            | _ => []
                          end)
  xs.

Fixpoint deserialize (n : nat) (xs : list ascii8) {struct xs} :=
  match n with
    | 0 =>
      match xs with
        | "192" :: ys =>
          Nil::deserialize 0 ys
        | "194" :: ys =>
          Bool false :: deserialize 0 ys
        | "195" :: ys =>
          Bool true :: deserialize 0 ys
        | Ascii b1 b2 b3 b4 b5 b6 b7 false :: ys =>
          PFixnum (Ascii b1 b2 b3 b4 b5 b6 b7 false) :: deserialize 0 ys
        | (Ascii b1 b2 b3 b4 b5 true true true) :: ys =>
          NFixnum (Ascii b1 b2 b3 b4 b5 true true true) :: deserialize 0 ys
        | "204" :: c1 :: ys =>
          Uint8 c1 :: deserialize 0 ys
        | "205" :: c1 :: c2 :: ys =>
          Uint16 (c1, c2) :: deserialize 0 ys
        | "206" :: c1 :: c2 :: c3 :: c4 :: ys =>
          Uint32 ((c1, c2), (c3, c4)) :: deserialize 0 ys
        | "207" :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: ys =>
          Uint64 (((c1, c2), (c3, c4)), ((c5, c6), (c7, c8))) :: deserialize 0 ys
        | "208" :: c1 :: ys =>
          Int8 c1 :: deserialize 0 ys
        | "209" :: c1 :: c2 :: ys =>
          Int16 (c1, c2) :: deserialize 0 ys
        | "210" :: c1 :: c2 :: c3 :: c4 :: ys =>
          Int32 ((c1, c2), (c3, c4)) :: deserialize 0 ys
        | "211" :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: ys =>
          Int64 (((c1, c2), (c3, c4)), ((c5, c6), (c7, c8))) :: deserialize 0 ys
        | "202" :: c1 :: c2 :: c3 :: c4 :: ys =>
          Float ((c1,c2), (c3, c4)) :: deserialize 0 ys
        | "203" :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: ys =>
          Double (((c1, c2), (c3, c4)), ((c5, c6), (c7, c8))) :: deserialize 0 ys
        | Ascii b1 b2 b3 b4 b5 true false true :: ys =>
          let n :=
            nat_of_ascii8 (Ascii b1 b2 b3 b4 b5 false false false) in
          let (zs, ws) :=
            split_at n @@ deserialize n ys in
            FixRaw (compact zs) :: ws
        | "218" :: s1 :: s2 :: ys =>
          let n :=
            nat_of_ascii16 (s1,s2) in
          let (zs, ws) :=
            split_at n @@ deserialize n ys in
            Raw16 (compact zs) :: ws
        | "219" :: s1 :: s2 :: s3 :: s4 :: ys =>
          let n :=
            nat_of_ascii32 ((s1,s2),(s3,s4)) in
          let (zs, ws) :=
            split_at n @@ deserialize n ys in
            Raw32 (compact zs) :: ws
        | Ascii b1 b2 b3 b4 true false false true :: ys =>
          let n :=
            nat_of_ascii8 (Ascii b1 b2 b3 b4 false false false false) in
          let (zs, ws) :=
            split_at n @@ deserialize 0 ys in
            FixArray zs :: ws
        | "220" :: s1 :: s2 :: ys =>
          let n :=
            nat_of_ascii16 (s1,s2) in
            let (zs, ws) :=
              split_at n @@ deserialize 0 ys in
              Array16 zs :: ws
        | "221" :: s1 :: s2 :: s3 :: s4 :: ys =>
          let n :=
            nat_of_ascii32 ((s1, s2), (s3, s4)) in
            let (zs, ws) :=
              split_at n @@ deserialize 0 ys in
              Array32 zs :: ws
        | Ascii b1 b2 b3 b4 false false false true :: ys =>
          let n :=
            nat_of_ascii8 (Ascii b1 b2 b3 b4 false false false false) in
            let (zs, ws) :=
              split_at (2 * n) @@ deserialize 0 ys in
              FixMap (pair zs) :: ws
        | "222" :: s1 :: s2 :: ys =>
          let n :=
            nat_of_ascii16 (s1,s2) in
            let (zs, ws) :=
              split_at (2 * n) @@ deserialize 0 ys in
              Map16 (pair zs) :: ws
        | "223" :: s1 :: s2 :: s3 :: s4 :: ys =>
          let n :=
            nat_of_ascii32 ((s1, s2), (s3, s4)) in
            let (zs, ws) :=
              split_at (2 * n) @@ deserialize 0 ys in
              Map32 (pair zs) :: ws
        | _ =>
          []
      end
    | S m =>
      match xs with
        | y::ys => FixRaw [ y ]::deserialize m ys
        | _ => []
      end
  end.

Definition DeserializeCorrect os bs :=
  SerializedList os bs ->
  deserialize 0 bs = os.

Lemma correct_bot :
  DeserializeCorrect [] [].
Proof with auto.
unfold DeserializeCorrect...
Qed.

Lemma correct_nil : forall os bs,
  DeserializeCorrect os bs ->
  DeserializeCorrect (Nil :: os) ("192"::bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H0.
apply H in H3.
rewrite <- H3...
Qed.

Lemma correct_false: forall os bs,
  DeserializeCorrect os bs ->
  DeserializeCorrect ((Bool false) :: os) ("194"::bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H0.
apply H in H3.
rewrite <- H3...
Qed.

Lemma correct_true: forall os bs,
  DeserializeCorrect os bs ->
  DeserializeCorrect ((Bool true) :: os) ("195"::bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H0.
apply H in H3.
rewrite <- H3...
Qed.

Lemma correct_pfixnum: forall os bs x1 x2 x3 x4 x5 x6 x7,
  DeserializeCorrect os bs ->
  DeserializeCorrect ((PFixnum (Ascii x1 x2 x3 x4 x5 x6 x7 false))::os)
                     ((Ascii x1 x2 x3 x4 x5 x6 x7 false)::bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H0.
apply H in H2.
rewrite <- H2.
destruct x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Lemma correct_nfixnum: forall os bs x1 x2 x3 x4 x5,
  DeserializeCorrect os bs ->
  DeserializeCorrect
     ((NFixnum   (Ascii x1 x2 x3 x4 x5 true true true))::os)
     ((Ascii x1 x2 x3 x4 x5 true true true)::bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H0.
apply H in H2.
rewrite <- H2.
destruct x1,x2,x3,x4,x5; reflexivity.
Qed.

Lemma correct_uint8 : forall os bs c,
  DeserializeCorrect os bs ->
  DeserializeCorrect ((Uint8 c)::os) ("204"::list_of_ascii8 c ++ bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H0.
apply H in H2.
rewrite <- H2...
Qed.

Lemma correct_uint16 : forall os bs c,
  DeserializeCorrect os bs ->
  DeserializeCorrect ((Uint16 c)::os) ("205"::list_of_ascii16 c ++ bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
destruct c.
inversion H0.
apply H in H2.
rewrite <- H2...
Qed.

Lemma correct_uint32 : forall os bs c,
  DeserializeCorrect os bs ->
  DeserializeCorrect ((Uint32 c)::os) ("206"::list_of_ascii32 c ++ bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
destruct c.
destruct a, a0.
inversion H0.
apply H in H2.
rewrite <- H2...
Qed.

Lemma correct_uint64 : forall os bs c,
  DeserializeCorrect os bs ->
  DeserializeCorrect ((Uint64 c)::os) ("207"::list_of_ascii64 c ++ bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
destruct c.
destruct a, a0.
destruct a, a0, a1, a2.
inversion H0.
apply H in H2.
rewrite <- H2...
Qed.

Lemma correct_int8 : forall os bs c,
  DeserializeCorrect os bs ->
  DeserializeCorrect ((Int8 c)::os) ("208"::list_of_ascii8 c ++ bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H0.
apply H in H2.
rewrite <- H2...
Qed.

Lemma correct_int16 : forall os bs c,
  DeserializeCorrect os bs ->
  DeserializeCorrect ((Int16 c)::os) ("209"::list_of_ascii16 c ++ bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
destruct c.
inversion H0.
apply H in H2.
rewrite <- H2...
Qed.

Lemma correct_int32 : forall os bs c,
  DeserializeCorrect os bs ->
  DeserializeCorrect ((Int32 c)::os) ("210"::list_of_ascii32 c ++ bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
destruct c.
destruct a, a0.
inversion H0.
apply H in H2.
rewrite <- H2...
Qed.

Lemma correct_int64 : forall os bs c,
  DeserializeCorrect os bs ->
  DeserializeCorrect ((Int64 c)::os) ("211"::list_of_ascii64 c ++ bs).
Proof.
unfold DeserializeCorrect.
intros.
destruct c.
destruct a, a0.
destruct a, a0, a1, a2.
inversion H0.
apply H in H2.
rewrite <- H2.
reflexivity.
Qed.

Lemma correct_float : forall os bs c,
  DeserializeCorrect os bs ->
  DeserializeCorrect ((Float c)::os) ("202"::list_of_ascii32 c ++ bs).
Proof.
unfold DeserializeCorrect.
intros.
destruct c.
destruct a, a0.
inversion H0.
apply H in H2.
rewrite <- H2.
reflexivity.
Qed.

Lemma correct_double : forall os bs c,
  DeserializeCorrect os bs ->
  DeserializeCorrect ((Double c)::os) ("203"::list_of_ascii64 c ++ bs).
Proof.
unfold DeserializeCorrect.
intros.
destruct c.
destruct a, a0.
destruct a, a0, a1, a2.
inversion H0.
apply H in H2.
rewrite <- H2.
reflexivity.
Qed.

Lemma deserialize_take_length: forall xs ys,
  take (List.length xs) (deserialize (List.length xs) (xs ++ ys)) = List.map (fun x => FixRaw [ x ]) xs.
Proof with auto.
induction xs; [ reflexivity | intros ].
simpl.
rewrite IHxs...
Qed.

Lemma deserialize_drop_length: forall xs ys,
  drop (List.length xs) (deserialize (List.length xs) (xs ++ ys)) = deserialize 0 ys.
Proof with auto.
induction xs; [ reflexivity | intros ].
simpl.
rewrite IHxs...
Qed.

Lemma compact_eq : forall xs,
  compact (List.map (fun x => FixRaw [ x ]) xs) = xs.
Proof with auto.
induction xs; [ reflexivity | intros ].
simpl.
rewrite IHxs...
Qed.

Lemma correct_fixraw: forall os bs cs b1 b2 b3 b4 b5,
 DeserializeCorrect os bs ->
 Ascii b1 b2 b3 b4 b5 false false false = ascii8_of_nat (List.length cs) ->
 List.length cs < pow 5 ->
 DeserializeCorrect (FixRaw cs :: os) ((Ascii b1 b2 b3 b4 b5 true false true) :: cs ++ bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H2.
assert (bs0 = bs); [| rewrite_for bs0 ].
 apply app_same in H11...
apply H in H13.
assert (length cs < pow 8).
 transitivity (pow 5); auto.
 apply pow_lt...
destruct b1,b2,b3,b4,b5;
  ((replace (deserialize 0 _ ) with
    (let n := nat_of_ascii8 (ascii8_of_nat (length cs)) in
     let (zs, ws) := split_at n @@ deserialize n (cs++bs) in
     FixRaw (compact zs) :: ws));
  [ unfold atat, split_at;
    rewrite nat_ascii8_embedding, deserialize_take_length, deserialize_drop_length, compact_eq, <- H13
  | rewrite <- H7])...
Qed.

Lemma correct_raw16: forall os bs cs s1 s2,
 DeserializeCorrect os bs ->
 (s1, s2) = ascii16_of_nat (List.length cs) ->
 List.length cs < pow 16 ->
 DeserializeCorrect (Raw16 cs :: os) ("218" :: s1 :: s2 :: cs ++ bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H2.
assert (bs0 = bs); [| rewrite_for bs0 ].
 apply app_same in H8...
apply H in H10.
change (deserialize 0 _ ) with
  (let (zs, ws) :=
    split_at (nat_of_ascii16 (s1,s2)) @@ deserialize (nat_of_ascii16 (s1,s2)) (cs++bs) in
    Raw16 (compact zs) :: ws).
unfold atat, split_at.
rewrite H7, nat_ascii16_embedding, deserialize_take_length, deserialize_drop_length, compact_eq, H10...
Qed.

Lemma correct_raw32: forall os bs cs s1 s2 s3 s4,
  DeserializeCorrect os bs ->
  ((s1, s2), (s3, s4)) = ascii32_of_nat (List.length cs) ->
  List.length cs < pow 32 ->
  DeserializeCorrect (Raw32 cs :: os) ("219" :: s1 :: s2 :: s3 :: s4 :: cs ++ bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H2.
assert (bs0 = bs); [| rewrite_for bs0 ].
 apply app_same in H10...
apply H in H12.
change (deserialize 0 _ ) with
  (let (zs, ws) :=
    split_at (nat_of_ascii32 ((s1,s2),(s3,s4))) @@ deserialize (nat_of_ascii32 ((s1,s2),(s3,s4))) (cs++bs) in
    Raw32 (compact zs) :: ws).
unfold atat, split_at.
rewrite H7, nat_ascii32_embedding, deserialize_take_length, deserialize_drop_length, compact_eq, H12...
Qed.

Lemma correct_fixarray : forall os bs n xs ys b1 b2 b3 b4,
  DeserializeCorrect os bs ->
  (xs, ys) = split_at n os ->
  n < pow 4 ->
  Ascii b1 b2 b3 b4 false false false false = ascii8_of_nat n ->
  DeserializeCorrect (FixArray xs :: ys) (Ascii b1 b2 b3 b4 true false false true :: bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H3.
assert (os = os0); [| rewrite_for os0 ].
 apply split_at_soundness in H0.
 apply split_at_soundness in H12.
 rewrite H0, H12...
apply H in H9.
assert (n0 < pow 8).
 transitivity (pow 4); auto.
 apply pow_lt...
destruct b1, b2, b3, b4;
 (replace (deserialize 0 (_ :: bs)) with
   (let (zs, ws) :=
      split_at (nat_of_ascii8 (ascii8_of_nat n0)) @@ deserialize 0 bs
    in
      FixArray zs :: ws);
   [ unfold atat; rewrite H9, nat_ascii8_embedding, <- H12 | rewrite <- H14])...
Qed.

Lemma correct_array16 : forall os bs n xs ys s1 s2 ,
 DeserializeCorrect os bs ->
 n < pow 16 ->
 (s1, s2) = ascii16_of_nat n ->
 (xs, ys) = split_at n os ->
 DeserializeCorrect (Array16 xs :: ys) ("220" :: s1 :: s2 :: bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H3.
assert (os = os0).
 apply split_at_soundness in H2.
 apply split_at_soundness in H10.
 rewrite H2, H10...

 rewrite_for os0.
 apply H in H9.
 assert ( n = nat_of_ascii16 (s1, s2)).
  rewrite H1.
  rewrite nat_ascii16_embedding...

  simpl.
  change (nat_of_ascii8 s1 * 256 + nat_of_ascii8 s2) with (nat_of_ascii16 (s1, s2)).
  rewrite <- H13.
  inversion H2.
  rewrite <- H9...
Qed.

Lemma correct_array32: forall os bs n xs ys s1 s2 s3 s4,
 DeserializeCorrect os bs ->
 (xs, ys) = split_at n os ->
 n < pow 32 ->
 ((s1, s2), (s3, s4)) = ascii32_of_nat n ->
 DeserializeCorrect (Array32 xs :: ys) ("221" :: s1 :: s2 :: s3 :: s4 :: bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H3.
assert (os = os0).
 apply split_at_soundness in H0.
 apply split_at_soundness in H12.
 rewrite H0, H12...

 rewrite_for os0.
 apply H in H9.
 change (deserialize 0 ("221" :: s1 :: s2 :: s3 :: s4 :: bs)) with
   (let (zs, ws) := split_at (nat_of_ascii32 (s1, s2, (s3, s4))) (deserialize 0 bs) in
    Array32 zs :: ws).
 rewrite H9, H14, nat_ascii32_embedding, <- H12...
Qed.

Lemma correct_fixmap: forall os bs n xs ys b1 b2 b3 b4,
  DeserializeCorrect os bs ->
  (xs, ys) = split_at (2 * n) os ->
  length xs = 2 * n ->
  n < pow 4 ->
  Ascii b1 b2 b3 b4 false false false false = ascii8_of_nat n ->
  DeserializeCorrect (FixMap (pair xs) :: ys) (Ascii b1 b2 b3 b4 false false false true :: bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H4.
assert ( n < pow 8).
 transitivity (pow 4); auto.
 apply pow_lt...
assert ( n0 < pow 8).
 transitivity (pow 4); auto.
 apply pow_lt...
assert (n0 = n); [| rewrite_for n0 ].
 rewrite H3 in H16.
 apply ascii8_of_nat_eq in H16...
assert (xs0 = xs); [| rewrite_for xs0 ].
 rewrite <- (unpair_pair _ n xs), <- (unpair_pair _ n xs0); auto.
 rewrite H5...
assert (os0 = os); [| rewrite_for os0 ].
 apply split_at_soundness in H0.
 apply split_at_soundness in H13.
 rewrite H0, H13...
apply H in H11.
destruct b1, b2, b3, b4;
  (replace (deserialize 0 (_ :: bs)) with
    (let (zs, ws) :=
       split_at (2 * (nat_of_ascii8 (ascii8_of_nat n))) @@ deserialize 0 bs
     in
       FixMap (pair zs) :: ws);
    [ unfold atat; rewrite nat_ascii8_embedding, H11, <- H13
    | rewrite <- H16 ])...
Qed.

Lemma correct_map16: forall os bs n xs ys s1 s2,
  DeserializeCorrect os bs ->
  (xs, ys) = split_at (2 * n) os ->
  length xs = 2 * n ->
  n < pow 16 ->
  (s1, s2) = ascii16_of_nat n ->
  DeserializeCorrect (Map16 (pair xs) :: ys) ("222" :: s1 :: s2 :: bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H4.
assert (n0 = n).
 rewrite H3 in H14.
 apply ascii16_of_nat_eq in H14...
rewrite_for n0.
assert (xs0 = xs).
 rewrite <- (unpair_pair _ n xs), <- (unpair_pair _ n xs0); auto.
 rewrite H5...
rewrite_for xs0.
assert (os0 = os).
 apply split_at_soundness in H0.
 apply split_at_soundness in H11.
 rewrite H0, H11...
rewrite_for os0.
apply H in H10.
change (deserialize 0 ("222" :: s1 :: s2 :: bs)) with
  (let (zs, ws) := split_at (2 * nat_of_ascii16 (s1, s2)) @@ deserialize 0 bs in
  Map16 (pair zs) :: ws).
unfold atat.
rewrite H10, H14, nat_ascii16_embedding, <- H11...
Qed.

Lemma correct_map32: forall os bs n xs ys s1 s2 s3 s4,
  DeserializeCorrect os bs ->
  (xs, ys) = split_at (2 * n) os ->
  length xs = 2 * n ->
  n < pow 32 ->
  ((s1, s2), (s3, s4)) = ascii32_of_nat n ->
  DeserializeCorrect (Map32 (pair xs) :: ys) ("223" :: s1 :: s2 :: s3 :: s4 :: bs).
Proof with auto.
unfold DeserializeCorrect.
intros.
inversion H4.
assert (n0 = n); [| rewrite_for n0 ].
 rewrite H3 in H16.
 apply ascii32_of_nat_eq in H16...
assert (xs0 = xs); [| rewrite_for xs0 ].
 rewrite <- (unpair_pair _ n xs), <- (unpair_pair _ n xs0); auto.
 rewrite H5...
assert (os0 = os); [| rewrite_for os0 ].
 apply split_at_soundness in H0.
 apply split_at_soundness in H13.
 rewrite H0, H13...
apply H in H11.
change (deserialize 0 ("223" :: s1 :: s2 :: s3 :: s4 :: bs)) with
  (let (zs, ws) := split_at (2 * nat_of_ascii32 ((s1, s2),(s3,s4))) @@ deserialize 0 bs in
    Map32 (pair zs) :: ws).
unfold atat.
rewrite H16, H11, nat_ascii32_embedding, <- H13...
Qed.

Lemma correct_intro : forall os bs,
  (SerializedList os bs -> DeserializeCorrect os bs) ->
  DeserializeCorrect os bs.
Proof with auto.
unfold DeserializeCorrect.
intros.
apply H in H0...
Qed.

Theorem deserialize_correct : forall os bs,
  DeserializeCorrect os bs.
Proof with auto.
intros.
apply correct_intro.
intros.
pattern os, bs.
apply SerializedList_ind; intros; auto.
 apply correct_bot...
 apply correct_nil...
 apply correct_true...
 apply correct_false...
 apply correct_pfixnum...
 apply correct_nfixnum...
 apply correct_uint8...
 apply correct_uint16...
 apply correct_uint32...
 apply correct_uint64...
 apply correct_int8...
 apply correct_int16...
 apply correct_int32...
 apply correct_int64...
 apply correct_float...
 apply correct_double...
 apply correct_fixraw...
 simpl; apply correct_raw16...
 simpl; apply correct_raw32...
 apply correct_fixarray with (os:=os0) (n:=n)...
 apply correct_array16 with (os:=os0) (n:=n)...
 apply correct_array32 with (os:=os0) (n:=n)...
 apply correct_fixmap with (os:=os0) (n:=n)...
 apply correct_map16 with (os:=os0) (n:=n)...
 apply correct_map32 with (os:=os0) (n:=n)...
Qed.

Lemma app_nil: forall A (xs : list A),
  xs ++ [] = xs.
Proof.
induction xs.
 reflexivity.
simpl.
rewrite IHxs.
reflexivity.
Qed.

