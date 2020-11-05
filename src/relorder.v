(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.

Module Order.

Section ClassDef.

Variable (T:Type).

Definition axiom (r : rel T) :=
  [/\ reflexive r, antisymmetric r & transitive r].

Structure map (phr : phant (rel T)) := Pack {apply; _ : axiom apply}.

Variables (r:rel T) (phr: phant (rel T)) (rF : map phr).

Definition class := let: Pack _ a as rF' := rF
  return axiom (apply phr rF') in a. 

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
Coercion base: class_of >-> order.
Coercion mixin : class_of >-> mixin_of.
Coercion apply : map >-> rel.
Variables (r: rel T) (phr : phant (rel T)) (cF : map phr).

Definition class := let: Pack _ c as cF' := cF
  return class_of cF' in c.

Canonical order := Order.Pack _ phr _ class.

End ClassDef.

Module Exports.
Notation total_prop r := (mixin_of _ r).
Notation total_order r := (class_of _ r).
(*Coercion base : total_order >-> Order.axiom.*)
(*Coercion mixin : total_order >-> total_prop.*)
(*Coercion apply : map >-> rel.*)
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

Lemma OrderRefl : reflexive ro.
Proof.
by case: orderP.
Qed.

Lemma OrderAnti : antisymmetric ro.
Proof.
by case: orderP.
Qed.

Lemma OrderTrans : transitive ro.
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

Lemma nat_total: total_order leq.
Proof.
split; [exact: nat_order | exact: leq_total].
Qed.

Canonical natTotalOrder := TotalOrder nat_total.
End natOrder.

Section MirrorOrder.

Variable (T : Type).

Definition mirrorOrder (r: {order T}) := fun x y => r y x.
Notation "r '^~I'" := (mirrorOrder r) (at level 100).

Lemma mirrorOrderP (r:{order T}): (order (r^~I)).
Proof.
split; rewrite /mirrorOrder.
- exact: OrderRefl.
- by move=>x y r_anti; apply: (OrderAnti _ r); rewrite andbC.
- by move => y x z r_y_x r_z_y; apply: (OrderTrans _ r y).
Qed.

Canonical MirrorOrder (r: {order T}):= Order (mirrorOrderP r).

Lemma mirrorTotalOrderP (r : {total_order T}) : (total_order (r^~I)).
Proof.
split; first exact: mirrorOrderP; rewrite /mirrorOrder.
move=> x y; exact: totalMP.
Qed.

Canonical MirrorTotalOrder (r : {total_order T}) :=
    TotalOrder (mirrorTotalOrderP r).
End MirrorOrder.

Section SubOrder.


Variables (T:Type).
Definition subOrder (P: pred T) (sT: subType P) (r : {order T}) :=
    fun x y : sT => r (val x) (val y).
Notation "r '%_(' sT ')'" := (subOrder _ sT r) (at level 100).

Variables (P:pred T) (sT : subType P).

Lemma subOrderP (r: {order T}): order (r%_(sT)).
Proof.
split; rewrite /subOrder.
- move => x; exact: OrderRefl.
- move=> x y /(OrderAnti _ r); exact: val_inj.
- move => y x z; exact: OrderTrans.
Qed.

Canonical SubOrder (r : {order T}) := Order (subOrderP r).

Lemma subTotalOrderP (r : {total_order T}) : total_order (r %_(sT)).
Proof.
split; first exact: subOrderP; rewrite /subOrder.
move=> x y; exact : totalMP.
Qed.

Canonical SubTotalOrder (r : {total_order T}) :=
    TotalOrder (subTotalOrderP r).

End SubOrder.
