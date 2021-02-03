From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class expose (P : Prop) := Expose : P.

Hint Extern 0 (expose _) => (exact) : typeclass_instances.
Hint Extern 0 (expose (is_true _)) => (match goal with H : is_true _ |- _ => exact: H end) : typeclass_instances.

Section SubType.

Context (T : choiceType) (P : pred T) (x0 : T).
Hypothesis (Px0 : P x0).

Record S := SubType { xval :> T; _ : P xval }.

Lemma xvalP (x : S) : P (xval x).
Proof. by case: x. Qed.

Let x0' : S := SubType Px0.

Context (f : T -> T -> T). (*(f' : S -> S -> S).*)

Hypothesis Hf : forall x y, P x -> P y -> P (f x y).
Canonical f' x y := SubType (Hf (xvalP x) (xvalP y)).

(*Lemma Pf x y : P (f (xval x) (xval y)).
rewrite Hf; exact: xvalP. Defined.*)

Canonical foo x (Hx : expose (P x)) := SubType Hx.

Definition my_insub (x' : S) & (phantom T (xval x')) := x'.

(*Context (x : T) (Hx : P x).
Check (@my_insub _ (Phantom _ x)).
 *)

(*Canonical foo_f (x y : S) := @SubType (f x y) (Pf x y).*)

(*Context (x y : T) (Hx : P x) (Hy : P y).
Check (@my_insub _ (Phantom _ (f x y))).*)

Context (r : rel T).
(*Definition r' (x y : S) & (phantom T (xval x)) & (phantom T (xval y)) := r x y.

Notation rS x y := (@r' _ _ (Phantom _ x) (Phantom _ y)).*)

Hypothesis f'xx : forall x : S, r (f' x x) (f' x x).

(*Definition r' x y  := r (xval x) (xval y).

Hypothesis f'C : forall x y x' y', x' = xval (f' x y) -> y' = xval (f' y x) -> r x' y'. (f x' y') (xval (f' y x))*)

Lemma fxx x (_ : expose (P x)) : r (f x x) (f x x).
by rewrite f'xx.
Qed.

End SubType.
