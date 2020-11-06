(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.

Module Order.

Section ClassDef.

Variable (T: eqType).

Definition axiom (r : rel T) :=
  [/\ reflexive r, antisymmetric r & transitive r].

Definition strict (le lt: rel T) :=
  forall x y, le x y = (x == y) || (lt x y).

Record class (lt : rel T) := Class
  {
    class_le : rel T;
    _ : axiom class_le;
    _ : strict class_le lt;
    _ : irreflexive lt
  }.

(*TODO : Confirm that the phantom is required*)
Structure map (phr : phant (rel T)) := Pack {map_lt; map_class : class map_lt}.


End ClassDef.

Module Exports.
Notation leo r := (class_le _ _ (map_class _ (Phant _) r)).
Notation lto r:= (@map_lt _ _ r).
Notation order r :=  (axiom _ r).
Notation strict r := (strict (leo r) (lto r)).
Notation OrderClass ax st ir:= (Class _ _ _ ax st ir).
Notation OrderPack cla := (Pack _ (Phant _) _ cla). 
Notation "{ 'order' T }" := (map T (Phant (_)))
  (at level 0, format "{ 'order' T }").
Infix "<=_[ r ]" := (leo r) (at level 0, format "x <=_[ r ] y").
Infix "<_[ r ]" := (lto r) (at level 0, format "x <_[ r ] y").

End Exports.
End Order.
Include Order.Exports.

Section OrderTheory.


Variables ( T: eqType ) (r: {order T}).
Local Notation "x <= y" := (x <=_[r] y).
Local Notation "x < y" := (x <_[r] y).
Local Notation "x <= y <= z" := ((x <= y) && (y <= z)).
Local Notation "x < y < z" := ((x < y) && (y < z)).
Local Notation "x < y <= z" := ((x < y) && (y <= z)).
Local Notation "x <= y < z" := ((x <= y) && (y < z)).

Lemma orderP : order (leo r).
Proof.
by case: r => lt [] le [refl anti trans] ?.
Qed.

Lemma orefl : reflexive (leo r).
Proof.
by case: orderP.
Qed.

Lemma oanti : antisymmetric (leo r).
Proof.
by case: orderP.
Qed.

Lemma otrans : transitive (leo r).
Proof.
by case: orderP.
Qed.

Lemma ostrict: forall (x y : T), (x <= y) = (x == y) || (x < y).
Proof.
by move => x y; case: r => lt [le] ? ?.
Qed.

Lemma ltostrict: forall x, x < x = false.
Proof.
by move => x; case : r => /= lt [le _ _] ->.
Qed.

Lemma lt_def x y: (x < y) = (y != x) && (x <= y).
Proof.
case eqyx: (y == x).
- by move/eqP: eqyx => ->; rewrite ltostrict orefl.
- by rewrite /= ostrict eq_sym eqyx orFb.
Qed.

Lemma lt_neqAle x y: (x < y) = (x != y) && (x <= y).
Proof.
by rewrite lt_def eq_sym.
Qed.

Lemma lt_eqF x y: x < y -> x == y = false.
Proof.
by rewrite lt_neqAle => /andP [/negbTE->].
Qed.

Lemma gt_eqF x y : y < x -> x == y = false.
Proof.
by apply: contraTF => /eqP ->; rewrite ltostrict. 
Qed.

Lemma eq_le x y: (x == y) = (x <= y <= x).
Proof.
by apply/eqP/idP => [->|/oanti]; rewrite ?orefl.
Qed.

Lemma ltW x y: x < y -> x <= y.
Proof.
by rewrite ostrict orbC => ->.
Qed.

Lemma lt_le_trans y x z: x < y -> y <= z -> x < z.
Proof.
rewrite !lt_neqAle => /andP [nexy lexy leyz];
  rewrite (otrans _ _ _ lexy) // andbT.
by apply: contraNneq nexy => eqxz; rewrite eqxz eq_le leyz andbT in lexy *.
Qed.

Lemma lt_trans: transitive (fun x y => (x < y)).
Proof.
by move => y x z ltxy /ltW leyz; apply (lt_le_trans y).
Qed.

Lemma le_lt_trans y x z: x <= y -> y < z -> x < z.
Proof.
by rewrite ostrict => /orP [/eqP ->|/lt_trans t /t].
Qed.

Lemma lt_nsym x y : x < y -> y < x -> False.
Proof.
by move=> xy /(lt_trans _ _ _ xy); rewrite ltostrict.
Qed.

Lemma lt_asym x y : x < y < x = false.
Proof.
by apply/negP => /andP []; apply: lt_nsym.
Qed.

Lemma le_gtF x y: x <= y -> y < x = false.
Proof.
by move=> le_xy; apply/negP => /lt_le_trans /(_ le_xy); rewrite ltostrict.
Qed.

Lemma lt_geF x y : (x < y) -> y <= x = false.
Proof.
by move=> le_xy; apply/negP => /le_lt_trans /(_ le_xy); rewrite ltostrict.
Qed.

Definition lt_gtF x y hxy := le_gtF _ _ (@ltW x y hxy).


Lemma lt_leAnge x y : (x < y) = (x <= y) && ~~ (y <= x).
Proof.
apply/idP/idP => [ltxy|/andP[lexy Nleyx]]; first by rewrite ltW // lt_geF.
rewrite lt_neqAle lexy andbT; apply: contraNneq Nleyx => ->; exact: orefl.
Qed.

Lemma lt_le_asym x y : x < y <= x = false.
Proof.
by rewrite lt_neqAle -andbA -eq_le eq_sym andNb.
Qed.

Lemma le_lt_asym x y : x <= y < x = false.
Proof.
by rewrite andbC lt_le_asym.
Qed.

End OrderTheory.

Section RatOrder.

Lemma order_rat : order le_rat.
Admitted.

Lemma strict_rat : forall (x y : rat), (le_rat x y) = (x == y) || lt_rat x y.
Admitted.

Lemma strict_lt_rat : irreflexive lt_rat.
Admitted.

Canonical class_rat := OrderClass order_rat strict_rat strict_lt_rat.
Canonical map_rat := OrderPack class_rat.

Lemma lt_rat_def (x y : rat) : (le_rat x y) = (lt_rat x y) || (x == y).
Proof.
by rewrite ostrict orbC.
Qed.

End RatOrder.

Module TotalOrder.
Section ClassDef.

Variables (T : eqType).

Definition mixin_of (r : rel T) :=
    forall x y, r x y || r y x.

Record class (lt : rel T) := Class
{
  base : Order.class _ lt;
  mixin : mixin_of (Order.class_le _ _ base)
}.
Structure map (phr : phant (rel T)) := Pack
{
  map_lt;
  map_class : class map_lt
}.


Variable (phr : phant (rel T)) (rT : map phr).

Definition class_of := let: Pack _ c as rT' := rT
  return class (map_lt phr rT') in c.    

Canonical order := OrderPack (base _ class_of).

End ClassDef.

Module Exports.
Notation total_prop r := (@mixin_of _ r).
Notation total_class r := (@class_of _ r).
Notation total_le r :=
  (Order.class_le _ _ (base _ _ (map_class _ (Phant _) r))).
Notation total_lt r := (map_lt _ (Phant _) r).
Notation "{ 'total_order' T }" := (map T (Phant (_)))
  (at level 0, format "{ 'total_order' T }").
Coercion order : map >-> Order.map.
Canonical order.
End Exports.

End TotalOrder.
Include TotalOrder.Exports.

Section TotalOrderTheory.

Variables (T:eqType) (r : {total_order T}).

Lemma totalMP : total_prop (total_le r).
Proof.
by case: r => /= ? [].
Qed.

Lemma totalP : order (leo r).
Proof.
by case: r => lt [[le ?]].
Qed. 

End TotalOrderTheory.

Section RatTotalOrder.
Lemma total_rat : forall x y, le_rat x y || le_rat y x.
Admitted.

Check TotalOrder.Class.
Definition totalclass_rat := TotalOrder.Class _ _ class_rat total_rat.
Canonical totalorder_rat := TotalOrder.Pack _ (Phant _) _ totalclass_rat.

Lemma order_rat_total : order (le_rat).
Proof.
exact: totalP.
Qed.

End RatTotalOrder.

(*Section MirrorOrder.

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

Lemma l : forall n : nat, n <= n.
Proof.
move=> n.
apply: (OrderTrans _ _ n) => /=; exact: OrderRefl.
Qed.
*)