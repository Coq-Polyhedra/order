(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.


Section RelOrder.

Definition axioms {sort: Type} (R : rel sort) :=
    [/\ reflexive R, antisymmetric R & transitive R]. 

Record relOrder {sort: Type} := Pack 
    {   
        relord :> rel sort;
        _ : axioms relord
    }.

Variable (sort:Type).

Lemma relorder_refl (R : relOrder) : @reflexive sort R.
Proof.
by case: R => /= ? [? _ _].
Qed.

Lemma relorder_anti (R : relOrder) : @antisymmetric sort R.
Proof.
by case: R => /= ? [_ ? _].
Qed.

Lemma relorder_trans (R : relOrder) : @transitive sort R.
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


End NatRelorder.

Section MirrorOrder.

Variable (sort: Type).

Definition mirror (R : relOrder) : rel sort := 
    fun x y : sort => R y x.

Lemma mirror_axioms (R: relOrder):
axioms (mirror R).
Proof.
rewrite /mirror; split.
-   exact: relorder_refl.
-   move=> x y /andP [R_y_x R_x_y].
    by apply (relorder_anti sort R); rewrite R_x_y R_y_x.
-   rewrite /mirror => y x z R_y_x R_z_y.
    exact: (relorder_trans sort R y).
Qed.

Canonical rel_mirror (R: relOrder) :=
    Pack sort (mirror R) (mirror_axioms R).

End MirrorOrder.
Section SubOrder.

Variable (sort:Type) (P: pred sort) (sT: subType P).

Definition suborder (R: relOrder) :=
    fun x y : sT => R (val x) (val y).

Lemma suborder_axioms (R: relOrder) :
    axioms (suborder R).
Proof.
rewrite /suborder.
split.
- move=> ?; exact: relorder_refl.
- move=> x y /(relorder_anti sort); exact: val_inj.
- move=> y x z; exact: relorder_trans.
Qed.

Canonical rel_suborder (R: relOrder) :=
    Pack sT (suborder R) (suborder_axioms R). 

End SubOrder.







