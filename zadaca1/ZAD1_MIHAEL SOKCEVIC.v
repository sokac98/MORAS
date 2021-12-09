Set Implicit Arguments.
Require Import Omega.

Inductive B: Type :=
  | O : B
  | I : B.

Definition And(x y: B) : B :=
match x with
  | O => O
  | I => y
end.

Definition Or(x y: B) : B :=
match x with
  | I => I
  | O => y
end.

Definition Not(x : B) : B :=
match x with
  | O => I
  | I => O
end.

Goal forall (X Y: B),
  Or (Not (And X Y)) (Or (And (Not X) Y) (Or (Not X) (Not Y))) = Or (Not X) (Not Y).
Proof.
  induction X, Y; simpl; reflexivity.
Qed.

Goal forall (X Y Z: B),
   And (Not (And (Not X) (And Y (Not Z)))) (And (Not (And (And X Y) Z)) (And X (And (Not Y) (Not Z)))) = And X (And (Not Y) (Not Z)).
Proof.
  induction X, Y, Z; simpl; reflexivity.
Qed.