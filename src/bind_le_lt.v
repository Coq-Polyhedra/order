From mathcomp Require Import all_ssreflect all_algebra.

Section BindLeLt.

Variable (T : eqType).

Record lt_of_le (lt : rel T) :=
  LtOfLe { the_le : rel T;
           _ : (forall x y: T, the_le x y = (x == y) || (lt x y))}.

Record le_lt :=
  LeLt { the_lt : rel T;
         the_lt_of_le : lt_of_le the_lt }.

Notation "'the_le' x" := (the_le _ (the_lt_of_le x)) (at level 0).

Lemma le_is_lt_or_eq (F : le_lt) (x y : T) :
  (the_le F x y) = (x == y) || (the_lt F x y ).
Proof.
by case: F => the_lt [the_le' ?] /=.
Qed.

End BindLeLt.

Notation "'the_le' x" := (the_le _ _ (the_lt_of_le _ x)) (at level 0).
Notation "'the_lt' x" := (the_lt _ x) (at level 0).

Section UseCase.

Variable (T : eqType) (le lt : rel T).

Fact H : forall x y : T, le x y = (x == y) || (lt x y).
Admitted.

Definition le_to_lt := LtOfLe _ _ le H.
Definition le_and_lt := LeLt _ lt le_to_lt.
Canonical le_to_lt.
Canonical le_and_lt.

(* main use case *)
Goal forall x y : T, le x y = (x == y) || (lt x y).
move => x y.
by rewrite le_is_lt_or_eq.
Qed.

(* using the other direction *)
Goal forall x y : T, le x y = (x == y) || (lt x y).
move => x y.
by rewrite -le_is_lt_or_eq.
Qed.

(* binding le and lt using type unification *)
Definition bind_le_lt (F : le_lt T)
           (ph_le : phantom (rel T) (the_le F))
           (ph_lt : phantom (rel T) (the_lt F)) := F.
Eval simpl in (bind_le_lt _ (Phantom _ le) (Phantom _ _)).
Eval simpl in (bind_le_lt _ (Phantom _ _) (Phantom _ lt)).

End UseCase.

Section UseCaseRat.

Fact H_rat : forall x y : rat, ((x <= y) = (x == y) || (x < y))%R.
Admitted.

Definition le_to_lt_rat := LtOfLe _ _ _ H_rat.
Definition le_and_lt_rat := LeLt _ _ le_to_lt_rat.
Canonical le_to_lt_rat.
Canonical le_and_lt_rat.

(* main use case *)
Goal forall x y : rat, ((x <= y) = (x == y) || (x < y))%R.
move => x y.
by rewrite le_is_lt_or_eq.
Qed.

(* using the other direction *)
Goal forall x y : rat, ((x <= y) = (x == y) || (x < y))%R.
move => x y.
by rewrite -le_is_lt_or_eq.
Qed.

End UseCaseRat.

(*Section UseCaseNat.

Definition lt_nat x y := (x < y). (* we need to hide < behind a head symbol
                                  * distinct from <= *)

Fact H_nat : forall x y : nat, (x <= y) = (x == y) || lt_nat x y.
Admitted.

Definition le_to_lt_nat := LtOfLe _ _ _ H_nat.
Definition le_and_lt_nat := LeLt _ _ le_to_lt_nat.
Canonical le_to_lt_nat.
Canonical le_and_lt_nat.

(* main use case *)
Goal forall x y : nat, (x <= y) = (x == y) || (lt_nat x y).
move => x y.
by rewrite le_is_lt_or_eq.
Qed.

(* using the other direction *)
Goal forall x y : nat, (x <= y) = (x == y) || (lt_nat x y).
move => x y.
by rewrite -le_is_lt_or_eq.
Qed.

End UseCaseNat.*)

Section UseCaseNat2.

Fact H_nat' : forall x y : nat, (x <= y) = (x == y) || (x < y).
Admitted.

Definition le_to_lt_nat' : lt_of_le _ ltn := LtOfLe _ _ leq H_nat'.
Definition le_and_lt_nat' := LeLt _ _ le_to_lt_nat'.
Canonical le_to_lt_nat'.
Canonical le_and_lt_nat'.

(* main use case *)
Goal forall x y : nat, (x <= y) = (x == y) || (x < y).
Set Printing All.
move => x y.
Fail rewrite le_is_lt_or_eq. (* WARNING: infer le_and_lt_nat instead of le_and_lt_nat' *)
Abort.

(* using the other direction *)
Goal forall x y : nat, (x <= y) = (x == y) || (x < y).
move => x y.
Fail rewrite -le_is_lt_or_eq.
Abort.

End UseCaseNat2.
