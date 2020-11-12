(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.

Open Scope ring_scope.

Module Order.

Section ClassDef.

Variable (T: eqType).

Definition axiom (r : rel T) :=
  [/\ reflexive r, antisymmetric r & transitive r].

Definition strict (lt le: rel T) :=
  forall x y, lt x y = (x != y) && (le x y).

Record class (le lt: rel T) := Class
  {
    _ : axiom le;
    _ : strict lt le;
  }.

(*TODO : Confirm that the phantom is required*)
Structure pack (phr : phant (rel T)) := Pack
{
  pack_le;
  pack_lt;
  pack_class : class pack_le pack_lt
}.

Variable (phr : phant (rel T)) (r : pack phr).

Definition class_of := let: Pack _ _ c as r0 := r
  return (class (pack_le phr r0) (pack_lt phr r0)) in c.

Definition pack_of_le (r : rel T) :=
  fun (ro : pack phr) & phant_id (pack_le phr ro) r =>
  ro.

Definition pack_of_lt (r : rel T) :=
  fun (ro : pack phr) & phant_id (pack_lt phr ro) r =>
  ro.

End ClassDef.

Module Exports.
Notation lto r := (pack_lt _ _ r).
Notation leo r:= (pack_le _ _ r).
Notation order le :=  (axiom _ le).
Notation strict lt le := (strict _ lt le).
Notation OrderClass ax st := (Class _ _ _ ax st).
Notation OrderPack cla := (Pack _ (Phant _) _ _ cla).
Notation "{ 'order' T }" := (pack T (Phant (_)))
  (at level 0, format "{ 'order'  T }").
Infix "<=_[ r ]" := (leo r) (at level 0, format "x  <=_[ r ]  y").
Infix "<_[ r ]" := (lto r) (at level 0, format "x  <_[ r ]  y").
Notation "[ r ]^le" := (pack_of_le _ (Phant _) r _ id)
  (at level 0, format "[ r ]^le").
Notation "[ r ]^lt" := (pack_of_lt _ (Phant _) r _ id)
  (at level 0, format "[ r ]^lt").


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
by case: r => le lt [].
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
by move=> x y; case: r => le lt [].
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

(*Section RatOrder.

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

End RatOrder.*)

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
(*Check [<=%O]^O.*)
(*Check (otrans _ [<=%O]^O).*)
Goal forall x y : rat, (x < y)%O && (x <= y)%O -> x != y.
Proof.
by move=> x y /andP []; rewrite ostrict /=; case/andP.
Qed.

End OrderTest.

Module TotalOrder.
Section ClassDef.

Variables (T : eqType).

Definition mixin_of (r : rel T) :=
    forall x y, r x y || r y x.

Record class (le lt: rel T) := Class
{
  base : Order.class _ le lt;
  mixin : mixin_of le
}.

Structure pack (phr : phant (rel T)) := Pack
{
  pack_le;
  pack_lt;
  pack_class : class pack_le pack_lt
}.

Variable (phr : phant (rel T)) (rT : pack phr).

Definition class_of := let: Pack _ _ c as rT' := rT
  return class (pack_le phr rT') (pack_lt phr rT') in c.    

Canonical order := OrderPack (base _ _ class_of).

End ClassDef.

Module Exports.
Notation total r := (mixin_of _ r).
Notation TotalClass ax st to := (Class _ _ _ (Order.Class _ _ _ ax st) to).
Notation TotalPack cla := (Pack _ (Phant _) _ _ cla).
Notation "{ 'total_order' T }" := (pack T (Phant _))
  (at level 0, format "{ 'total_order'  T }").
Coercion order : pack >-> Order.pack.
Canonical order.
End Exports.

End TotalOrder.
Include TotalOrder.Exports.

Section TotalOrderTheory.

Variables (T:eqType) (r : {total_order T}).

Lemma totalMP : total (leo r).
Proof.
by case: r => ? ? [].
Qed.

Lemma totalP : order (leo r).
Proof.
by case: r => ? ? [[]].
Qed. 

End TotalOrderTheory.

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

Canonical order_of :=
  Order.Pack _ phr
    (Order.pack_le _ _ mr) (Order.pack_lt _ _ mr)
    (Order.pack_class _ _ mr).


Definition meet_of (r : {order T}) :=
  fun (pr : pack phr) & phant_id (pack_order _ pr) r =>
  meet (pack_order _ pr) (pack_class _ pr).

End ClassDef.

Module Exports.
Notation lower_bound := (lower_bound _).
Notation greatest := (greatest _).
Notation meet r := (meet_of _ (Phant _) r _ id).
Coercion pack_order : pack >-> Order.pack.
Canonical order_of.
Notation "{ 'meet_order' T }" := (pack T (Phant _))
  (at level 0, format "{ 'meet_order'  T }"). 
Notation MeetClass ro low great := (Class _ ro _ low great).
Notation MeetPack cla := (Pack _ (Phant _) _ cla).  


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

Section NumMeet.

Context (disp : unit) (R : meetSemilatticeType disp).

Lemma num_min : lower_bound (@Order.le _ R) (@Order.meet _ R).
Proof.
move=> x y.
by rewrite Order.MeetSemilatticeTheory.leIl Order.MeetSemilatticeTheory.leIr.
Qed.

Lemma num_great : greatest (@Order.le _ R) (@Order.meet _ R).
move=> x y w.
by rewrite Order.MeetSemilatticeTheory.lexI => -> ->.
Qed.

Definition meet_class_num := MeetClass (pack_num _ R) num_min num_great.
Canonical meet_pack_num := MeetPack meet_class_num.

Lemma lower_bound_rat (x y : R) : (((@Order.meet _ R) x y) <= x)%O.
Proof.
apply : infl.
Qed.

End NumMeet.

Section Test.
Context (disp : unit) (R : meetSemilatticeType disp).
Variables (x y : R).

Goal ((meet [<=%O]^le x y) <= x)%O.
Proof.
rewrite /(meet _) /=.
apply: infl.
Qed.


End Test.

Module Join.

Section ClassDef.

Variable (T: eqType).

Definition upper_bound (r:rel T) (m : T -> T -> T) :=
  forall x y, r x (m x y) && r y (m x y).

Definition lowest (r : rel T) (m : T -> T -> T) :=
  forall x y w, r x w -> r y w -> r (m x y) w.

Record class (r: {order T}) := Class
{
  join : T -> T -> T;
  _ : upper_bound (leo r) join;
  _ : lowest (leo r) join
}.

Structure pack (phr : phant (rel T)) := Pack
{
  pack_order;
  pack_class : class pack_order
}.
Local Coercion pack_order: pack >-> Order.pack.

Variables (phr : phant (rel T)) (mr : pack phr).

Canonical order_of :=
  Order.Pack _ phr
    (Order.pack_le _ _ mr) (Order.pack_lt _ _ mr)
    (Order.pack_class _ _ mr).

Definition join_of (r : {order T}) :=
  fun (pr : pack phr) & phant_id (pack_order _ pr) r =>
  join (pack_order _ pr) (pack_class _ pr).

End ClassDef.
Module Exports.
Notation upper_bound := (upper_bound _).
Notation lowest := (lowest _).
Notation join r := (join_of _ (Phant _) r _ id).
Coercion pack_order : pack >-> Order.pack.
Canonical order_of.
Notation "{ 'join_order' T }" := (pack T (Phant _))
  (at level 0, format "{ 'join_order'  T }").
Notation JoinClass ro up lowe := (Class _ ro _ up lowe).
Notation JoinPack cla := (Pack _ (Phant _) _ cla).

End Exports.

End Join.
Include Join.Exports.

Section JoinTheory.

Variable (T:eqType) (r :{join_order T}).

Lemma join_order_is_order : order (leo r).
Proof.
exact: orderP.
Qed.

Lemma upper_boundP : upper_bound (leo r) (join r).
Proof.
by case: r => ? [].
Qed.

Lemma lowestP : lowest (leo r) (join r).
Proof.
by case : r => ? [].
Qed.

Lemma joinC_ex : forall x y : T, (join r x y) <=_[r] (join r y x).
Proof.
move => x y.
case/andP : (upper_boundP y x) => y_leq_join.
move/(lowestP x y) => lowestxy.
by apply: lowestxy.
Qed.
End JoinTheory.

Section NumJoin.

Context (disp : unit) (R : meetSemilatticeType disp).

Lemma num_max : upper_bound (@Order.le _ R) (@Order.meet _ R).
Admitted.


Lemma num_low : lowest (@Order.le _ R) (@Order.meet _ R).
Admitted.

Definition join_class_num := JoinClass (pack_num _ R) num_max num_low.
Canonical join_pack_num := JoinPack join_class_num.

Lemma neq_join_irr : forall x y, ~~ ((join [<=%O]^le x y) < (join [<=%O]^le y x))%O.
Proof.
move => x y.
have ->: (join [<=%O]^le x y) = (join [<=%O]^le y x).
- apply/(oanti _ [<=%O]^le)/andP; rewrite /=.
  split; [exact : joinC_ex | exact : joinC_ex].
by rewrite ltostrict.
Qed.

End NumJoin.

Module Diamond.
Section ClassDef.

Variable (T : eqType).

Record class (r : {meet_order T}) := Class
{
  join_mixin : Join.class _ r
}.

Structure pack (phr : phant (rel T)) := Pack
{
  pack_order;
  pack_class : class pack_order
}.

Variables (phr : phant (rel T)) (mjr : pack phr).
Local Coercion pack_order : pack >-> Meet.pack.
Local Coercion pack_class : pack >-> class.

Canonical order_of := Order.Pack T (Phant (rel T)) (leo mjr) (lto mjr)
 (Order.class_of _ _ (Meet.pack_order _ _ mjr)).

Canonical join_of := Join.Pack _ (Phant _) _ (join_mixin _ mjr). 

End ClassDef.

Module Exports.
Coercion pack_order : pack >-> Meet.pack.
Coercion join_of : pack >-> Join.pack.
Canonical order_of.
Canonical join_of.
Notation "{ 'diamond' T }" := (pack T (Phant _))
  (at level 0, format "{ 'diamond'  T }").

End Exports.
End Diamond.
Include Diamond.Exports.

Section Test.
Variable (T : eqType) (r : {diamond T}).
Goal order (leo r).
exact: orderP.
Qed.

Goal forall x y, meet r x y = join r x y.
Admitted.
End Test.






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