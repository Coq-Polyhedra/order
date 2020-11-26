


Section NumOrder.

Context (disp : unit) (R : porderType disp).

Lemma num_order : order (@Order.le _ R).
Proof.
split.
- by [].
- exact: Order.POrderTheory.le_anti.
- exact: Order.POrderTheory.le_trans.
Qed.

Lemma num_strict : forall (x y: R), ((x < y) = (x != y) && (x <= y))%O.
Proof.
exact: Order.POrderTheory.lt_neqAle.
Qed.

Canonical class_num := OrderClass num_order num_strict.
Canonical pack_num := OrderPack class_num.

End NumOrder.

Section OrderTest.
Goal forall x y : rat, (x < y)%O && (x <= y)%O -> x != y.
Proof.
by move=> x y /andP []; rewrite ostrict /=; case/andP.
Qed.

End OrderTest.

(*Section RatTotalOrder.
Lemma total_rat : forall x y, le_rat x y || le_rat y x.
Admitted.

Definition totalclass_rat := TotalClass order_rat strict_rat total_rat.
Canonical totalorder_rat := TotalPack totalclass_rat.

Lemma order_rat_total : order (le_rat).
Proof.
apply: totalP.
Qed.

End RatTotalOrder.
*)


Section NumMeet.

Context (disp : unit) (R : meetSemilatticeType disp).

Lemma num_minC : commutative (@Order.meet _ R).
Proof.
Admitted.

Lemma num_minA : associative (@Order.meet _ R).
Proof.
Admitted.

Lemma num_minxx : idempotent (@Order.meet _ R).
Proof.
Admitted.

Lemma num_leEmin :
  forall x y, (x <= y)%O = ((@Order.meet _ R) x y == x).
Proof.
Admitted.

Definition meet_class_num :=
  MeetClass num_minC num_minA num_minxx num_leEmin.
Canonical meet_pack_num := MeetPack meet_class_num.

Lemma lower_bound_rat (x y : R) : (((@Order.meet _ R) x y) <= x)%O.
Proof.
exact : leIl.
Qed.

End NumMeet.

Section Test.
Context (disp : unit) (R : meetSemilatticeType disp).
Variables (x y : R).

Goal ((meet [leo: <=%O] x y) <= x)%O.
Proof.
rewrite /(meet _) /=.
apply: leIl.
Qed.


End Test.

Section NumLattice.

Context (disp : unit) (R : latticeType disp).

Lemma num_joinC : commutative (@Order.join _ R).
Admitted.

Lemma num_joinA : associative (@Order.join _ R).
Admitted.

Lemma num_joinxx: idempotent (@Order.join _ R).
Admitted.

Lemma num_joinKI : forall y x, meet [leo: <=%O] x ((@Order.join _ R) x y) = x.
Admitted.

Lemma num_joinKU : forall y x, (@Order.join _ R) x (meet [leo: <=%O] x y) = x.
Admitted.

Lemma num_leEjoin : forall y x, (y <= x)%O = ((@Order.join _ R x y) == x).
Admitted.

Definition lattice_class_num :=
  LatticeClass num_joinC num_joinA num_joinxx num_joinKI num_joinKU num_leEjoin.
Canonical lattice_pack_num := LatticePack lattice_class_num.


End NumLattice.

Section Test.
Context (disp: unit) (R : latticeType disp).

Goal forall x : R, (join [lto: <%O] x x) = x.
move=> x.
exact: joinxx.
Qed.
End Test.


Section NumTBLattice.
Context (disp : unit) (L : tbLatticeType disp).

Lemma num_botEle : forall x:L, (0 <= x)%O.
Admitted.

Lemma num_topEle : forall x:L, (x <= 1)%O.
Admitted.

Definition tblattice_class_num := TBLatticeClass num_topEle num_botEle.
Canonical tblattice_pack_num := TBLatticePack tblattice_class_num.

Goal forall x:L, (bottom [leo: <=%O] <= x)%O.
Proof.
exact: botEle.
Qed.
End NumTBLattice.

(*
Section MirrorOrder.

Variable (T : eqType).

Definition symrel (r : rel T) := fun x y => r y x.

Notation "r ^~I" := (symrel r) (at level 2, format "r ^~I").

Lemma mirror_order (r : rel T) : order r -> order r^~I.
Proof.
case=> hr hs ht; split.
- by apply: hr.
- by move=> x y; rewrite andbC; apply: hs.
- by move=> y x z ? /ht; apply.
Qed.


Canonical class_rat := OrderClass order_rat strict_rat.
Canonical pack_rat := OrderPack class_rat.

Canonical MirrorOrder (r : {porder T}) :=
  Order (mirror_order r).



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
