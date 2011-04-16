Require Ascii.
Require String.
Require List.


(* basic types for OCaml *)
Parameter mlunit mlchar mlint mlstring : Set.

(* unit *)
Extract Constant mlunit => "unit".

(* bool *)
Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive sumbool => "bool" ["true" "false"].

(* int *)
Extract Constant mlint => "int".
Parameter mlint_of_nat : nat -> mlint.
Parameter nat_of_mlint : mlint -> nat.
Extract Constant mlint_of_nat =>
  "let rec iter = function O -> 0 | S p -> succ (iter p) in iter".
Extract Constant nat_of_mlint =>
  "let rec iter = function 0 -> O | n -> S (iter (pred n)) in iter".

(* char *)
Extract Constant mlchar => "char".
Parameter mlchar_of_mlint : mlint -> mlchar.
Parameter mlint_of_mlchar : mlchar -> mlint.
Extract Constant mlchar_of_mlint => "char_of_int".
Extract Constant mlint_of_mlchar => "int_of_char".

(* list *)
Extract Inductive list => "list" ["[]" "(::)"].

(* option *)
Extract Inductive option => "option" ["None" "Some"].

(* string *)
Extract Constant mlstring => "string".
Extract Inductive String.string => "ascii list" ["[]" "(::)"].
Parameter string_of_list : List.list Ascii.ascii -> String.string.
Parameter list_of_string : String.string -> List.list Ascii.ascii.
Extract Constant list_of_string => "(fun x -> x)".
Extract Constant string_of_list => "(fun x -> x)".

Parameter mlstring_of_list : forall {A:Type},
  (A->mlchar) -> List.list A -> mlstring.
Parameter list_of_mlstring : forall {A:Type},
  (mlchar->A) -> mlstring -> List.list A.
Extract Constant mlstring_of_list =>
  "(fun f s -> String.concat """"
     (List.map (fun x -> String.make 1 (f x)) s))".
Extract Constant list_of_mlstring => "
(fun f s ->
  let rec explode_rec n =
    if n >= String.length s then
      []
    else
      f (String.get s n) :: explode_rec (succ n)
  in
  explode_rec 0)
".

Parameter mlstring_of_mlint : mlint -> mlstring.
Extract Constant mlstring_of_mlint => "string_of_int".


(* print to stdout *)
Parameter print_mlstring : mlstring -> mlunit.
Parameter println_mlstring : mlstring -> mlunit.
Parameter prerr_mlstring : mlstring -> mlunit.
Parameter prerrln_mlstring : mlstring -> mlunit.
Parameter semicolon_flipped : forall {A:Type}, A -> mlunit -> A.
Extract Constant semicolon_flipped => "(fun x f -> f; x)".
Extract Constant print_mlstring => "print_string".
Extract Constant println_mlstring => "print_endline".
Extract Constant prerr_mlstring => "print_string".
Extract Constant prerrln_mlstring => "print_endline".

CoInductive llist (A: Type) : Type :=
  LNil | LCons (x: A) (xs: llist A).

Implicit Arguments LNil [A].
Implicit Arguments LCons [A].

Parameter get_contents_mlchars : llist mlchar.
Extract Constant get_contents_mlchars => "
 let rec iter store =
   lazy
     begin
       try (LCons (input_char stdin, iter())) with
       | End_of_file -> LNil
     end
 in
 iter ()".
