Require Ascii List.
Require Import ExtractUtil.

Definition mlchar_of_ascii a :=
  mlchar_of_mlint (mlint_of_nat (Ascii.nat_of_ascii a)).
Definition mlstring_of_string s :=
  mlstring_of_list mlchar_of_ascii (list_of_string s).
Definition ascii_of_mlchar c :=
  Ascii.ascii_of_nat (nat_of_mlint (mlint_of_mlchar c)).
Definition string_of_mlstring s :=
  string_of_list (list_of_mlstring ascii_of_mlchar s).

Definition print s := print_mlstring (mlstring_of_string s).
Definition println s := println_mlstring (mlstring_of_string s).
Definition prerr s := prerr_mlstring (mlstring_of_string s).
Definition prerrln s := prerrln_mlstring (mlstring_of_string s).

CoFixpoint lmap {A B:Type} (f: A -> B) (xs : llist A) : llist B :=
  match xs with
  | LNil => LNil
  | LCons x xs => LCons (f x) (lmap f xs)
  end.

Fixpoint ltake {A:Type} n (xs: llist A) :=
  match (n, xs) with
  | (O, _) => List.nil
  | (_, LNil) => List.nil
  | (S n', LCons x xs) => List.cons x (ltake n' xs)
  end.

Definition get_contents := lmap ascii_of_mlchar get_contents_mlchars.

Definition id {A:Type} (x:A) := x.

Definition atat {A B:Type} (f:A -> B) (x: A) := f x.
Infix "@@" := atat (right associativity, at level 75).

Definition doll {A B C:Type} (g:B->C) (f:A->B) (x:A) := g (f x).
Infix "$" := doll (at level 75).
