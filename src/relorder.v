(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.

Module Order.

Section ClassDef.

Variable (T:Type).

Definition axiom (r : rel T) :=
  [/\ reflexive r, antisymmetric r & transitive r].

Structure map (phr : phant (rel T)) := Pack {apply; _ : axiom apply}.


End ClassDef.

Module Exports.
Notation order r := (axiom _ r).
Coercion apply : map >-> rel.
Notation Order r_prop := (Pack _ (Phant _) _ r_prop).
Notation "{ 'order' T }" := (map T (Phant (rel T)))
  (at level 0, format "{ 'order' T }").

End Exports.

End Order.
Include Order.Exports.

Module TotalOrder.
Section ClassDef.

Variables (T : Type).

Definition mixin_of (r : rel T) :=
    forall x y, r x y || r y x.

Record class_of r := Class {base : order r; mixin : mixin_of r}.

Structure map (phr : phant (rel T)) := Pack {apply; _ : class_of apply}.

Variables (r: rel T) (phr : phant (rel T)) (cF : map phr).

Definition class := let: Pack _ c as cF' := cF
  return class_of (apply phr cF') in c.


Let r_app := (apply phr cF). 
Canonical order := Order.Pack _ phr r_app (base r_app class).

End ClassDef.

Module Exports.
Notation total_prop r := (mixin_of _ r).
Notation total_order r := (class_of _ r).
Coercion base : total_order >-> Order.axiom.
Coercion mixin : total_order >-> total_prop.
Coercion apply : map >-> rel.
Notation TotalOrder rp := (Pack _ (Phant _) _ rp).
Notation "{ 'total_order' T }" := (map T (Phant (rel T)))
  (at level 0, format "{ 'total_order' T }").
Coercion order : map >-> Order.map.
Canonical order.
End Exports.

End TotalOrder.
Include TotalOrder.Exports.

Section OrderTheory.

Variables (T: Type) (ro : {order T}).

Lemma orderP : order ro.
Proof.
by case: ro.
Qed. 

Lemma refl_o : reflexive ro.
Proof.
by case: orderP.
Qed.

Lemma anti_o : antisymmetric ro.
Proof.
by case: orderP.
Qed.

Lemma trans_o : transitive ro.
Proof.
by case: orderP.
Qed.
End OrderTheory.

Section TotalOrderTheory.

Variables (T:Type) (ro : {total_order T}).

Lemma totalMP : total_prop ro.
Proof.
by case: ro => /= ? [].
Qed.

Lemma totalP : total_order ro.
Proof.
by case: ro.
Qed. 

End TotalOrderTheory.

Section natOrder.

Lemma nat_order: order leq.
Proof.
split => //; [exact : anti_leq | exact : leq_trans].
Qed.

Canonical natOrder := Order nat_order.

Lemma nat_total_order: total_order leq.
Proof.
split; [exact: nat_order | exact: leq_total].
Qed.

Canonical natTotalOrder := TotalOrder nat_total_order.
End natOrder.

Section Mirror.



(*Section RelOrder.

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
(*TODO : Notations*)
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

(*TODO notations with ^*)

Notation "R %:C" := (mirror _ R) (at level 100).

Lemma refl_mirn: reflexive (leq %:C).
Proof.
exact: relorder_refl.
Qed.

Section SubOrder.

(*TODO : Notations*)

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

Section TotalOrder.

Variable (T:Type). 

Record TotalOrder {T:Type} := PPack
    {
        ord :> (@relOrder T);
        _ : forall x y, ord x y || ord y x
    }.

End TotalOrder.

Section NatTotalOrder.

Definition natT := fun (x:nat) => true.

Lemma leq_part_axiom : partial_axiom nat natT leq.
Proof.
by rewrite /partial_axiom /=.
Qed.

Canonical nat_totalorder := PPack nat natT nat nat_relorder leq_part_axiom.*)








