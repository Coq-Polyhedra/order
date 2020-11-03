(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.

Section RelOrder.

Definition axioms {T: Type} (R : rel T) :=
    [/\ reflexive R, antisymmetric R & transitive R]. 

Record relOrder {T: Type} := Pack 
    {   
        relord :> rel T;
        _ : axioms relord
    }.

Variable (T:Type).

Lemma relorder_refl (R : relOrder) : @reflexive T R.
Proof.
by case: R => /= ? [? _ _].
Qed.

Lemma relorder_anti (R : relOrder) : @antisymmetric T R.
Proof.
by case: R => /= ? [_ ? _].
Qed.

Lemma relorder_trans (R : relOrder) : @transitive T R.
Proof.
by case: R => /= ? [_ _ ?].
Qed.

End RelOrder.
Section NatRelorder.

Lemma leq_relorder_axioms : axioms leq.
Proof.
split.
- by [].
- exact: anti_leq.
- exact: leq_trans.
Qed.

Canonical nat_relorder :=
    Pack nat leq leq_relorder_axioms.

Lemma refl0 : 0 <= 0.
Proof.
exact: relorder_refl.
Qed.

End NatRelorder.

Section MirrorOrder.

Variable (T: Type).

Definition mirror (R : rel T) : rel T := 
    fun x y : T => R y x.

Lemma mirror_axioms (R: relOrder):
axioms (mirror R).
Proof.
rewrite /mirror; split.
-   exact: relorder_refl.
-   move=> x y /andP [R_y_x R_x_y].
    by apply (relorder_anti T R); rewrite R_x_y R_y_x.
-   rewrite /mirror => y x z R_y_x R_z_y.
    exact: (relorder_trans T R y).
Qed.

Canonical rel_mirror (R: relOrder) :=
    Pack T (mirror R) (mirror_axioms R).


End MirrorOrder.

Notation "R %:C" := (mirror _ R) (at level 100).

Lemma refl_mirn: reflexive (leq %:C).
Proof.
exact: relorder_refl.
Qed.

Section SubOrder.

Variable (T:Type) (P: pred T) (sT: subType P).

Definition suborder (R: relOrder) :=
    fun x y : sT => R (val x) (val y).

Lemma suborder_axioms (R: relOrder) :
    axioms (suborder R).
Proof.
rewrite /suborder.
split.
- move=> ?; exact: relorder_refl.
- move=> x y /(relorder_anti T); exact: val_inj.
- move=> y x z; exact: relorder_trans.
Qed.

Canonical rel_suborder (R: relOrder) :=
    Pack sT (suborder R) (suborder_axioms R). 

End SubOrder.

Section PartialOrder.

Variable (T:Type) (p: pred T).

Definition partial_axiom (r: rel T) :=
    forall x y, ~~ (p x) || ~~ (p y) -> r x y == false.

Record PartOrder {T:Type} := PPack
    {
        partord :> relOrder;
        _ : partial_axiom partord
    }.

End PartialOrder.

Section NatPartialOrder.

Definition natT := fun (x:nat) => true.

Lemma leq_part_axiom : partial_axiom nat natT leq.
Proof.
by rewrite /partial_axiom /=.
Qed.

Canonical nat_totalorder := PPack nat natT nat nat_relorder leq_part_axiom.








