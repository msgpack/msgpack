(**
   算術演算関連の補題
*)

Require Import Omega NArith Euclid.

(** ** 算術演算 *)
Lemma mult_S_lt_reg_l :
  forall n m p, 0 < n -> n * m < n * p -> m < p.
Proof.
intros.
destruct n.
 inversion H.

elim (le_or_lt m p).
 intro.
 inversion H1.
  rewrite H2 in H0.
   elim (lt_irrefl _ H0).
   omega.

   intro.
   apply (mult_S_lt_compat_l n _ _) in H1.
   omega.
Qed.

Lemma plus_elim: forall p a b,
  a + p < b -> a < b.
Proof.
intros.
omega.
Qed.

(** ** pow *)
Fixpoint pow (n : nat) :=
  match n with
    | 0 =>
      1
    | S n' =>
      2 * pow n'
  end.

Lemma pow_lt_O : forall n,
  0 < pow n.
Proof.
induction n; simpl; omega.
Qed.

Hint Resolve pow_lt_O.

Lemma pow_add: forall n m,
  pow n * pow m = pow (n + m).
Proof.
induction n; intros.
 simpl in *.
 omega.

 simpl.
 repeat rewrite plus_0_r.
 rewrite <- IHn, mult_plus_distr_r.
 reflexivity.
Qed.

(** ** divmod *)
Definition divmod (n m : nat) (P : 0 < m) :=
  eucl_dev m P n.

Lemma divmod_lt_q : forall (n m q r s t: nat),
  n < pow (s + t) ->
  n = q * pow s + r ->
  q < pow t.
Proof.
intros.
rewrite H0 in H.
apply plus_elim in H.
rewrite <- pow_add, mult_comm in H.
apply mult_S_lt_reg_l in H.
 assumption.

 apply pow_lt_O.
Qed.

Lemma divmod_not_O: forall n m q r,
  0 < n ->
  0 < m ->
  n = q * m + r ->
  0 < q \/ 0 < r.
Proof.
intros.
rewrite H1 in H.
destruct q.
 simpl in H.
 right.
 assumption.

 left.
 omega.
Qed.

Lemma divmod_O: forall n q r,
  0 = q * n + r ->
  n <> 0 ->
  q = 0 /\ r = 0.
Proof.
intros.
destruct q; destruct n; destruct r; try omega.
 simpl in H.
 discriminate.

 simpl in H.
 discriminate.
Qed.

Lemma divmod_O_pow: forall n q r,
  0 = q * pow n + r ->
  q = 0 /\ r = 0.
Proof.
intros.
apply (divmod_O (pow n) _ _); auto.
intro.
generalize (pow_lt_O n); intros.
omega.
Qed.

Lemma plus_O : forall n,
  n + 0 = n.
Proof.
Admitted.

Lemma plus_double : forall n,
  n < n + n.
Admitted.

Lemma pow_lt : forall n m,
  n < m ->
  pow n < pow m.
Proof.
induction n; induction m; simpl; intros.
 inversion H.

 destruct m; auto.
 transitivity (pow (S m));
   [ apply IHm | idtac];
  omega.

 inversion H.

 simpl in IHm.
 inversion H; simpl.
  repeat (rewrite plus_O in *).
  apply (Plus.plus_lt_compat_r O _).
  transitivity (pow n); auto.
  apply plus_double.

  assert (S n < m); auto.
  apply IHm in H2.
  transitivity (pow m); auto.
  rewrite plus_O.
  apply plus_double.
Qed.

Hint Resolve pow_lt pow_lt_O: pow.
