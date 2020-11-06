(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.

Module Order.

Section ClassDef.

Variable (T: eqType).

Definition axiom (r : rel T) :=
  [/\ reflexive r, antisymmetric r & transitive r].

Definition strict (lt le: rel T) :=
  forall x y, lt x y = (x != y) && (le x y).

Record class (le : rel T) := Class
  {
    class_lt : rel T;
    _ : axiom le;
    _ : strict class_lt le;
  }.

(*TODO : Confirm that the phantom is required*)
Structure pack (phr : phant (rel T)) := Pack {pack_le; pack_class : class pack_le}.

End ClassDef.

Module Exports.
Notation lto r := (class_lt _ _ (pack_class _ (Phant _) r)).
Notation leo r:= (@pack_le _ _ r).
Notation order r :=  (axiom _ r).
Notation strict r := (strict (lto r) (leo r)).
Notation OrderClass ax st := (Class _ _ _ ax st).
Notation OrderPack cla := (Pack _ (Phant _) _ cla).
Notation "{ 'order' T }" := (pack T (Phant (_)))
  (at level 0, format "{ 'order'  T }").
Infix "<=_[ r ]" := (leo r) (at level 0, format "x  <=_[ r ]  y").
Infix "<_[ r ]" := (lto r) (at level 0, format "x  <_[ r ]  y").

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
by case: r => le [].
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

Lemma ostrict: forall (x y : T), (x < y) = (x != y) && (x <= y).
Proof.
by move=> x y; case: r => le [lt /= _ ->].
Qed.

Lemma ltostrict: forall x, x < x = false.
Proof.
by move=>x; rewrite ostrict eq_refl orefl.
Qed.

Lemma lt_def x y: (x < y) = (y != x) && (x <= y).
Proof.
rewrite eq_sym; exact: ostrict.
Qed.

Lemma le_eqVlt x y: (x <= y) = (x == y) || (x < y).
Proof.
by rewrite ostrict; case: eqP => //= ->; rewrite orefl.
Qed.

Lemma lt_eqF x y: x < y -> x == y = false.
Proof.
by rewrite ostrict => /andP [/negbTE->].
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
by rewrite le_eqVlt orbC => ->.
Qed.

Lemma lt_le_trans y x z: x < y -> y <= z -> x < z.
Proof.
rewrite !ostrict => /andP [nexy lexy leyz];
  rewrite (otrans _ _ _ lexy) // andbT.
by apply: contraNneq nexy => eqxz; rewrite eqxz eq_le leyz andbT in lexy *.
Qed.

Lemma lt_trans: transitive (fun x y => (x < y)).
Proof.
by move => y x z ltxy /ltW leyz; apply (lt_le_trans y).
Qed.

Lemma le_lt_trans y x z: x <= y -> y < z -> x < z.
Proof.
by rewrite le_eqVlt => /orP [/eqP ->|/lt_trans t /t].
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
rewrite ostrict lexy andbT; apply: contraNneq Nleyx => ->; exact: orefl.
Qed.

Lemma lt_le_asym x y : x < y <= x = false.
Proof.
by rewrite ostrict -andbA -eq_le eq_sym andNb.
Qed.

Lemma le_lt_asym x y : x <= y < x = false.
Proof.
by rewrite andbC lt_le_asym.
Qed.

End OrderTheory.

Section RatOrder.

Lemma order_rat : order le_rat.
Admitted.

Lemma strict_rat : forall (x y : rat), (lt_rat x y) = (x != y) && le_rat x y.
Admitted.

Canonical class_rat := OrderClass order_rat strict_rat.
Canonical pack_rat := OrderPack class_rat.

Lemma lt_rat_def (x y : rat) : (le_rat x y) = (lt_rat x y) || (x == y).
Proof.
by rewrite le_eqVlt orbC.
Qed.

End RatOrder.

Module TotalOrder.
Section ClassDef.

Variables (T : eqType).

Definition mixin_of (r : rel T) :=
    forall x y, r x y || r y x.

Record class (le : rel T) := Class
{
  base : Order.class _ le;
  mixin : mixin_of le
}.
Structure pack (phr : phant (rel T)) := Pack
{
  pack_le;
  pack_class : class pack_le
}.

Variable (phr : phant (rel T)) (rT : pack phr).

Definition class_of := let: Pack _ c as rT' := rT
  return class (pack_le phr rT') in c.    

Canonical order := OrderPack (base _ class_of).

End ClassDef.

Module Exports.
Notation total_prop r := (@mixin_of _ r).
Notation total_class r := (@class_of _ r).
Notation TotalClass ax st to := (Class _ _ (Order.Class _ _ _ ax st) to).
Notation TotalPack cla := (Pack _ (Phant _) _ cla).
Notation "{ 'total_order' T }" := (pack T (Phant _))
  (at level 0, format "{ 'total_order'  T }").
Coercion order : pack >-> Order.pack.
Canonical order.
End Exports.

End TotalOrder.
Include TotalOrder.Exports.

Section TotalOrderTheory.

Variables (T:eqType) (r : {total_order T}).

Lemma totalMP : total_prop (leo r).
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

Definition totalclass_rat := TotalClass order_rat strict_rat total_rat.
Canonical totalorder_rat := TotalPack totalclass_rat.

Lemma order_rat_total : order (le_rat).
Proof.
apply: totalP.
Qed.

End RatTotalOrder.

Module Meet.
Section ClassDef.
Variable (T: eqType).

Definition lower_bound (r:rel T) (m : T -> T -> T) :=
  forall x y, r (m x y) x && r (m x y) y.

Definition greatest (r : rel T) (m : T -> T -> T) :=
  forall x y w, r w x -> r w y -> r w (m x y).
  
Record class (r: {order T}) := Class
{
  meet : T -> T -> T;
  _ : lower_bound (leo r) meet;
  _ : greatest (leo r) meet
}.

Structure pack (phr : phant (rel T)) := Pack
{
  pack_order;
  pack_class : class pack_order
}.
Local Coercion pack_order: pack >-> Order.pack.

Variables (phr : phant (rel T)) (mr : pack phr).

Canonical order :=
  Order.Pack _ phr (Order.pack_le _ _ mr) (Order.pack_class _ _ mr).

End ClassDef.

Module Exports.
Notation lower_bound := (lower_bound _).
Notation greatest := (greatest _).
Notation meet r := (meet _ _ (pack_class _ (Phant _) r)).
Coercion order : pack >-> Order.pack.
Canonical order.

Notation "{ 'meet_order' T }" := (pack T (Phant _))
  (at level 0, format "{ 'meet_order'  T }").


End Exports.

End Meet.
Include Meet.Exports.

Section MeetTheory.

Variable (T: eqType) (r: {meet_order T}).

(*Order.axiom T
  (Order.pack_le T (Phant (rel (Equality.sort T)))
     (Meet.order T (Phant (rel (Equality.sort T))) r))*)

     Lemma meet_order_is_order : order (leo r).
Proof.
exact: orderP.
Qed.

Lemma lower_boundP : lower_bound (leo r) (meet r).
Proof.
by case: r => ? [].
Qed.

Lemma greatestP : greatest (leo r) (meet r).
Proof.
by case : r => ? [].
Qed.

Lemma infl (x y : T): (meet r x y) <=_[r] x.
Proof.
by case/andP: (lower_boundP x y).
Qed.

End MeetTheory.

Section RatMeet.

Variable (min : rat -> rat -> rat).

Lemma rat_min : lower_bound le_rat min.
Admitted.

Lemma rat_great : greatest le_rat min.
Admitted.

Definition rat_meet_class := Meet.Class _ pack_rat _ rat_min rat_great.
Canonical rat_meet_pack := Meet.Pack _ (Phant _) _ rat_meet_class.

Lemma lower_bound_rat (x y : rat) : le_rat (min x y) x.
Proof.
apply : infl.
Qed.


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