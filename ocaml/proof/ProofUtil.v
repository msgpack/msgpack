Ltac rewrite_for x :=
  match goal with
    | [ H : x = _ |- _ ] => rewrite H in *; clear H
    | [ H : _ = x |- _ ] => rewrite <- H in *; clear H
  end.