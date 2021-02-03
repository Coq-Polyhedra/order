From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class expose (P : Prop) := Expose : P.

Hint Extern 0 (expose _) => (exact) : typeclass_instances.
Hint Extern 0 (expose (is_true _)) => (match goal with H : is_true _ |- _ => exact: H end) : typeclass_instances.

Section SubType.

Context (T : choiceType) (P : pred T) (x0 : T).

Record S := SubType { xval :> T; _ : P xval }.

Lemma xvalP (x : S) : P (xval x).
Proof. by case: x. Qed.

Context (f : T -> T -> T).

Hypothesis Hf : forall x y, P x -> P y -> P (f x y).
Canonical f' x y := SubType (Hf (xvalP x) (xvalP y)).

Canonical xinsub x (Hx : expose (P x)) := SubType Hx.

Definition my_insub (x' : S) & (phantom T (xval x')) := x'.

(*Context (x : T) (Hx : P x).
Check (@my_insub _ (Phantom _ x)).
 *)

(*Context (x y : T) (Hx : P x) (Hy : P y).
Check (@my_insub _ (Phantom _ (f x y))).*)

Context (r : rel T).
Hypothesis f'xx : forall x : S, r (f' x x) (f' x x).

Lemma fxx x : P x -> r (f x x) (f x x).
Proof. by move=> ?; rewrite f'xx. Qed.

Hypothesis f'C : forall x y, f' x y = f' y x.

Lemma fC x y : P x -> P y -> f x (f y x) = f x (f x y).
Proof. by move=> ??; rewrite [f y x](congr1 xval (f'C _ _)) /=. Qed.

End SubType.
