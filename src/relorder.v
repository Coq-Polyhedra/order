(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra finmap.

Set Implicit Arguments.
Unset Strict Implicit.

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
  return (class (pack_le r0) (pack_lt r0)) in c.

Definition pack_of_le (r : rel T) :=
  fun (ro : pack phr) & phant_id (pack_le ro) r =>
  ro.

Definition pack_of_lt (r : rel T) :=
  fun (ro : pack phr) & phant_id (pack_lt ro) r =>
  ro.

End ClassDef.

Module Exports.
Notation lto r := (pack_lt r).
Notation leo r:= (pack_le r).
Notation order le :=  (axiom le).
Notation strict lt le := (strict lt le).
Notation OrderClass ax st := (Class ax st).
Notation OrderPack cla := (Pack (Phant _) cla).
Notation "{ 'porder' T }" := (pack (Phant (rel T)))
  (at level 0, format "{ 'porder'  T }").
Notation "<=: r" := (leo r) (at level 0, format "<=: r").
Notation "<: r" := (lto r) (at level 0, format "<: r").
Notation "x <=_ r y" := (<=:r x y) (at level 65, r at level 2, format "x  <=_ r  y").
Notation "x <_ r y" := (<:r x y) (at level 65, r at level 2, format "x  <_ r  y").
Notation "x <=_ r0 y <=_ r1 z" := ((x <=_r0 y) && (y <=_r1 z))
  (at level 70, r0 at level 2, r1 at level 2, format "x  <=_ r0  y  <=_ r1  z").
Notation "x <_ r0 y <_ r1 z" := ((x <_r0 y) && (y <_r1 z))
  (at level 70, r0 at level 2, r1 at level 2, format "x  <_ r0  y  <_ r1  z").
Notation "x <=_ r0 y <_ r1 z" := ((x <=_r0 y) && (y <_r1 z))
  (at level 70, r0 at level 2, r1 at level 2, format "x  <=_ r0  y  <_ r1  z").
Notation "x <_ r0 y <=_ r1 z" := ((x <_r0 y) && (y <=_r1 z))
  (at level 70, r0 at level 2, r1 at level 2, format "x  <_ r0  y  <=_ r1  z").
Notation "[ 'leo:' r ]" := (@pack_of_le _ (Phant _) r _ id)
  (at level 0, format "[ 'leo:'  r ]").
Notation "[ 'lto:' r ]" := (@pack_of_lt _ (Phant _) r _ id)
  (at level 0, format "[ 'lto:'  r ]").
(*TODO : Notations supplémentaires*)


End Exports.
End Order.
Include Order.Exports.

Section OrderTheory.

Variables ( T: eqType ) (r: {porder T}).
Local Notation "x <= y" := (x <=_r y).
Local Notation "x < y" := (x <_r y).
Local Notation "x <= y <= z" := ((x <= y) && (y <= z)).
Local Notation "x < y < z" := ((x < y) && (y < z)).
Local Notation "x < y <= z" := ((x < y) && (y <= z)).
Local Notation "x <= y < z" := ((x <= y) && (y < z)).

Lemma orderP : order (<=:r).
Proof.
by case: r => le lt [].
Qed.

Lemma orefl : reflexive (<=:r).
Proof.
by case: orderP.
Qed.

Lemma oanti : antisymmetric (<=:r).
Proof.
by case: orderP.
Qed.

Lemma otrans : transitive (<=:r).
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
  rewrite (otrans lexy) // andbT.
by apply: contraNneq nexy => eqxz; rewrite eqxz eq_le leyz andbT in lexy *.
Qed.

Lemma lt_trans: transitive (fun x y => (x < y)).
Proof.
by move => y x z ltxy /ltW leyz; apply: (lt_le_trans ltxy).
Qed.

Lemma le_lt_trans y x z: x <= y -> y < z -> x < z.
Proof.
by rewrite le_eqVlt => /orP [/eqP ->|/lt_trans t /t].
Qed.

Lemma lt_nsym x y : x < y -> y < x -> False.
Proof.
by move=> xy /(lt_trans xy); rewrite ltostrict.
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

Definition lt_gtF x y hxy := le_gtF (@ltW x y hxy).


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

Record class (le lt : rel T) := Class
{
  base : Order.class le lt;
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
  return class (pack_le rT') (pack_lt rT') in c.    

Canonical order := OrderPack (base class_of).

End ClassDef.

Module Exports.
Notation total r := (mixin_of r).
Notation TotalClass ax st to := (Class _ _ _ (Order.Class _ _ _ ax st) to).
Notation TotalPack cla := (Pack _ (Phant _) _ _ cla).
Notation "{ 'torder' T }" := (pack (Phant (rel T)))
  (at level 0, format "{ 'torder'  T }").
Coercion order : pack >-> Order.pack.
Canonical order.
End Exports.

End TotalOrder.
Include TotalOrder.Exports.

Section TotalOrderTheory.

Variables (T:eqType) (r : {torder T}).

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
(*TODO : Adapter la structure MeetSemilattice de order.v*)
Section ClassDef.
Variable (T : eqType).

Record class (r : {porder T}) := Class
{
  meet : T -> T -> T;
  _ : commutative meet;
  _ : associative meet;
  _ : idempotent meet;
  _ : forall x y, (x <=_r y) = (meet x y == x)
}.

Structure pack (phr : phant (rel T)) := Pack
{
  pack_order;
  pack_class : class pack_order
}.
Local Coercion pack_order: pack >-> Order.pack.

Variables (phr : phant (rel T)) (mr : pack phr).

Canonical porder_of :=
  Order.Pack phr (Order.pack_class mr).


Definition meet_of (r : {porder T}) :=
  fun (pr : pack phr) & phant_id (pack_order pr) r =>
  meet (pack_class pr).

End ClassDef.

Module Exports.
Coercion pack_order : pack >-> Order.pack.
Coercion pack_class : pack >-> class.
Canonical porder_of.
Notation meet r := (@meet_of _ (Phant _) r _ id).
Notation "{ 'meet_order' T }" := (pack (Phant (rel T)))
  (at level 0, format "{ 'meet_order'  T }").
Notation MeetClass meetC meetA meetxx leEmeet :=
  (Class meetC meetA meetxx leEmeet).
Notation MeetPack cla := (Pack (Phant _)cla). 


End Exports.

End Meet.
Include Meet.Exports.

Section MeetTheory.

Variable (T: eqType) (r: {meet_order T}).
Local Notation "x `&` y" := (meet r x y).
Local Notation "x <= y" := (x <=_r y).

(*Order.axiom T
  (Order.pack_le T (Phant (rel (Equality.sort T)))
     (Meet.order T (Phant (rel (Equality.sort T))) r))*)

Lemma meet_order_is_order : order (<=:r).
Proof.
exact: orderP.
Qed.

Lemma meetC : commutative (meet r).
Proof.
by case: r => ? [? ?].
Qed.

Lemma meetA : associative (meet r).
Proof.
by case: r => ? [? ? ?].
Qed.

Lemma meetxx : idempotent (meet r).
Proof.
by case: r => ? [? ? ? ?].
Qed.

Lemma leEmeet x y : (x <= y) = (x `&` y == x).
Proof.
by case: r => ? [? ? ? ? ?]. 
Qed.

Lemma meetAC : right_commutative (meet r).
Proof.
by move=> x y z; rewrite -!meetA [X in _ `&` X]meetC.
Qed.
Lemma meetCA : left_commutative (meet r).
Proof.
by move=> x y z; rewrite !meetA [X in X `&` _]meetC.
Qed.
Lemma meetACA : interchange (meet r) (meet r).
Proof.
by move=> x y z t; rewrite !meetA [X in X `&` _]meetAC.
Qed.

Lemma meetKI y x : x `&` (x `&` y) = x `&` y.
Proof.
by rewrite meetA meetxx.
Qed.
Lemma meetIK y x : (x `&` y) `&` y = x `&` y.
Proof.
by rewrite -meetA meetxx.
Qed.
Lemma meetKIC y x : x `&` (y `&` x) = x `&` y.
Proof.
by rewrite meetC meetIK meetC.
Qed.
Lemma meetIKC y x : y `&` x `&` y = x `&` y.
Proof.
by rewrite meetAC meetC meetxx.
Qed.

Lemma lexI x y z : (x <= y `&` z) = (x <= y) && (x <= z).
Proof.
rewrite !leEmeet; apply/eqP/andP => [<-|[/eqP<- /eqP<-]].
  by rewrite meetA meetIK eqxx -meetA meetACA meetxx meetAC eqxx.
by rewrite -[X in X `&` _]meetA meetIK meetA.
Qed.

Lemma leIxl x y z : y <= x -> y `&` z <= x.
Proof.
by rewrite !leEmeet meetAC => /eqP ->.
Qed.

Lemma leIxr x y z : z <= x -> y `&` z <= x.
Proof.
by rewrite !leEmeet -meetA => /eqP ->.
Qed.

Lemma leIx2 x y z : (y <= x) || (z <= x) -> y `&` z <= x.
Proof.
by case/orP => [/leIxl|/leIxr].
Qed.

Lemma leIr x y : y `&` x <= x.
Proof.
by rewrite leIx2 ?orefl ?orbT.
Qed.

Lemma leIl x y : x `&` y <= x.
Proof.
by rewrite leIx2 ?orefl ?orbT.
Qed.

Lemma meet_idPl {x y} : reflect (x `&` y = x) (x <= y).
Proof.
by rewrite leEmeet; apply/eqP.
Qed.
Lemma meet_idPr {x y} : reflect (y `&` x = x) (x <= y).
Proof.
by rewrite meetC; apply/meet_idPl.
Qed.

Lemma meet_l x y : x <= y -> x `&` y = x.
Proof.
exact/meet_idPl.
Qed.
Lemma meet_r x y : y <= x -> x `&` y = y.
Proof.
exact/meet_idPr.
Qed.

Lemma leIidl x y : (x <= x `&` y) = (x <= y).
Proof. by rewrite !leEmeet meetKI.
Qed.
Lemma leIidr x y : (x <= y `&` x) = (x <= y).
Proof.
by rewrite !leEmeet meetKIC.
Qed.

Lemma eq_meetl x y : (x `&` y == x) = (x <= y).
Proof.
by apply/esym/leEmeet.
Qed.

Lemma eq_meetr x y : (x `&` y == y) = (y <= x).
Proof.
by rewrite meetC eq_meetl.
Qed.

Lemma leI2 x y z t : x <= z -> y <= t -> x `&` y <= z `&` t.
Proof.
by move=> xz yt; rewrite lexI !leIx2 ?xz ?yt ?orbT //.
Qed.

End MeetTheory.

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

(*Module Join.

Section ClassDef.

Variable (T: eqType).

Definition upper_bound (r:rel T) (m : T -> T -> T) :=
  forall x y, r x (m x y) && r y (m x y).

Definition lowest (r : rel T) (m : T -> T -> T) :=
  forall x y w, r x w -> r y w -> r (m x y) w.

Record class (r: {porder T}) := Class
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

Definition join_of (r : {porder T}) :=
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

Lemma joinC_ex : forall x y : T, (join r x y) <=_r (join r y x).
Proof.
move => x y.
case/andP : (upper_boundP y x) => y_leq_join.
move/(lowestP x y) => lowestxy.
by apply: lowestxy.
Qed.

Lemma joinC : commutative (join r).
Admitted.
End JoinTheory.*)

(*Section NumJoin.

Context (disp : unit) (R : meetSemilatticeType disp).

Lemma num_max : upper_bound (@Order.le _ R) (@Order.meet _ R).
Admitted.


Lemma num_low : lowest (@Order.le _ R) (@Order.meet _ R).
Admitted.

Definition join_class_num := JoinClass (pack_num _ R) num_max num_low.
Canonical join_pack_num := JoinPack join_class_num.

Lemma neq_join_irr : forall x y, ~~ ((join [leo: <=%O] x y) < (join [leo: <=%O] y x))%O.
Proof.
move => x y.
have ->: (join [leo: <=%O] x y) = (join [leo: <=%O] y x).
- apply/(oanti _ [leo: <=%O])/andP; rewrite /=.
  split; [exact : joinC_ex | exact : joinC_ex].
by rewrite ltostrict.
Qed.

End NumJoin.*)

Module Lattice.
Section ClassDef.

Variable (T : eqType).

Record class (r : {meet_order T}) := Class
{
  join : T -> T -> T;
  _ : commutative join;
  _ : associative join;
  _ : idempotent join;
  _ : forall y x, meet r x (join x y) = x;
  _ : forall y x, join x (meet r x y) = x;
  _ : forall y x, (y <=_r x) = ((join x y) == x) 
}.

Structure pack (phr : phant (rel T)) := Pack
{
  pack_order;
  pack_class : class pack_order
}.

Variables (phr : phant (rel T)) (mjr : pack phr).
Local Coercion pack_order : pack >-> Meet.pack.
Local Coercion pack_class : pack >-> class.

Canonical porder_of := Order.Pack phr (Order.class_of (Meet.pack_order mjr)).

Definition join_of (r : {porder T}) :=
  fun (mr : {meet_order T}) & phant_id (Meet.pack_order mr) r =>
  fun (lr : pack phr) & phant_id (pack_order lr) mr =>
  join lr.    



End ClassDef.

Module Exports.
Coercion pack_order : pack >-> Meet.pack.
Coercion pack_class : pack >-> class.
Canonical porder_of.
Notation "{ 'lattice' T }" := (pack (Phant (rel T)))
  (at level 0, format "{ 'lattice'  T }").
Notation LatticeClass joinC joinA joinxx joinKI joinKU leEjoin:=
  (Class joinC joinA joinxx joinKI joinKU leEjoin).
Notation LatticePack cla := (Pack (Phant _) cla).
Notation join r := (@join_of _ (Phant _) r _ id _ id).

End Exports.
End Lattice.
Include Lattice.Exports.

Section LatticeTheory.
Variable (T : eqType) (r : {lattice T}).

Local Notation "x `&` y" := (meet r x y).
Local Notation "x `|` y" := (join r x y).
Local Notation "x <= y" := (x <=_r y).

Lemma joinC : commutative (join r).
Proof.
by case: r => ? [? ?].
Qed.
Lemma joinA : associative (join r).
Proof.
by case: r => ? [? ? ?].
Qed.
Lemma joinxx : idempotent (join r).
Proof.
by case: r => ? [? ? ? ?].
Qed.
Lemma joinKI y x : x `&` (x `|` y) = x.
Proof.
by case: r => ? [? ? ? ? ?].
Qed.
Lemma meetKU y x : x `|` (x `&` y) = x.
Proof.
by case: r => ? [? ? ? ? ? ?].
Qed.

Lemma joinKIC y x : x `&` (y `|` x) = x.
Proof.
by rewrite joinC joinKI.
Qed.
Lemma meetKUC y x : x `|` (y `&` x) = x.
Proof.
by rewrite meetC meetKU.
Qed.

Lemma meetUK x y : (x `&` y) `|` y = y.
Proof.
by rewrite joinC meetC meetKU.
Qed.
Lemma joinIK x y : (x `|` y) `&` y = y.
Proof.
by rewrite joinC meetC joinKI.
Qed.

Lemma meetUKC x y : (y `&` x) `|` y = y.
Proof.
by rewrite meetC meetUK.
Qed.
Lemma joinIKC x y : (y `|` x) `&` y = y.
Proof.
by rewrite joinC joinIK.
Qed.

Lemma leEjoin x y : (x <= y) = (x `|` y == y).
Proof.
by rewrite leEmeet; apply/eqP/eqP => <-; rewrite (joinKI, meetUK).
Qed.

End LatticeTheory.
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

Module TBLattice.
Section ClassDef.

Variable (T : eqType).

(*TODO : top element*)
Record class (L : {lattice T}) := Class
{
  bottom : T;
  top : T;
  _ : forall x, x <=_L top;
  _ : forall x, bottom <=_L x
}.

Structure pack (phr : phant (rel T)) := Pack
{
  pack_lattice;
  pack_class : class pack_lattice
}.

Local Coercion pack_lattice: pack >-> Lattice.pack.
Local Coercion pack_class: pack >-> class.

Variable (phr : phant (rel T)) (bl : pack phr).

Canonical porder_of := Lattice.porder_of bl.

Definition bottom_of (r: {porder T}) :=
  fun (mo : {meet_order T}) & phant_id (Meet.pack_order mo) r =>
  fun (l : {lattice T}) & phant_id (Lattice.pack_order l) mo =>
  fun (bl : pack phr) & phant_id (pack_lattice bl) l =>
  bottom bl.

Definition top_of (r: {porder T}) :=
  fun (mo : {meet_order T} ) & phant_id (Meet.pack_order mo) r =>
  fun (l : {lattice T} ) & phant_id (Lattice.pack_order l) mo =>
  fun (bl : pack phr) & phant_id (pack_lattice bl) l =>
  top bl.
  

End ClassDef.
Module Exports.

Coercion pack_lattice: pack >-> Lattice.pack.
Coercion pack_class: pack >-> class.
Canonical porder_of.
Notation bottom r := (@bottom_of _ (Phant _) r _ id _ id _ id).
Notation top r := (@top_of _ (Phant _) r _ id _ id _ id).
Notation "{ 'tblattice' T }" := (pack (Phant (rel T))) 
  (at level 0, format "{ 'tblattice'  T }").
Notation TBLatticeClass topEle botEle := (Class topEle botEle).
Notation TBLatticePack cla := (Pack (Phant _) cla). 
End Exports.

End TBLattice.
Include TBLattice.Exports.

Section TBLatticeTheory.
Variable (T: eqType) (L : { tblattice T }).

Lemma botEle : forall x, bottom L <=_L x.
Proof.
by case: L => ? [].
Qed.

Lemma topEle : forall x, x <=_L top L.
Proof.
by case: L => ? [].
Qed.

Lemma joinx0 : right_id (bottom L) (join L).
Proof.
by move=> x; apply/eqP; rewrite joinC -leEjoin botEle.
Qed.

Lemma join0x : left_id (bottom L) (join L).
Proof.
by move=> x; apply/eqP; rewrite -leEjoin botEle.
Qed.

Lemma meet0x : left_id (top L) (meet L).
Proof.
by move=> x; apply/eqP; rewrite meetC -leEmeet topEle.
Qed.

Lemma meetx0 : right_id (top L) (meet L).
Proof.
by move=> x; apply/eqP; rewrite -leEmeet topEle.
Qed.



End TBLatticeTheory.

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

(* ==================================================================== *)
Lemma andPP P Q b c :
  reflect P b -> reflect Q c -> reflect (P /\ Q) (b && c).
Proof.
by move=> /rwP Pb /rwP Qc; apply: (iffP andP); intuition.
Qed.

Notation "'and_[ view1 , view2 ]" := (@andPP _ _ _ _ view1 view2)
  (at level 4, right associativity, format "''and_[' view1 ,  view2 ]").

Lemma implyPP (P Q : Prop) (b c : bool) :
  reflect P b -> reflect Q c -> reflect (P -> Q) (b ==> c).
Proof. by move=> /rwP Pb /rwP Qc; apply: (iffP implyP); intuition. Qed.

Notation "'imply_[ view1 , view2 ]" := (@implyPP _ _ _ _ view1 view2)
  (at level 4, right associativity, format "''imply_[' view1 ,  view2 ]").

Section SubLattices.
(*TODO (T : choiceType)*)
Context {T : choiceType} (L : {lattice T}).

(*stable : {fset T} -> bool*)
Definition stable (E : {fset T}) :=
  [forall x : E, [forall y : E, (meet L (val x) (val y) \in E)]]
  && [forall x : E, [forall y : E, (join L (val x) (val y) \in E)]].

Lemma stableP (E : {fset T}) :
  reflect
    [/\ forall x y, x \in E -> y \in E -> (meet L x y) \in E
      & forall x y, x \in E -> y \in E -> (join L x y) \in E]
    (stable E).
Proof. apply/andPP; apply/(iffP idP).
- move/forallP => /= stableH x y.
  case : (in_fsetP) => u // _ _; case: (in_fsetP) => v // _ _.
  by move/forallP: (stableH u); apply.
- move=> stableH; apply/forallP => /= x; apply/forallP => /= y.
  apply: stableH; exact: fsvalP.
- move/forallP => /= stableH x y.
  case : (in_fsetP) => u // _ _; case: (in_fsetP) => v // _ _.
  by move/forallP: (stableH u); apply.
- move=> stableH; apply/forallP => /= x; apply/forallP => /= y.
  apply: stableH; exact: fsvalP.
Qed.

Record subLattice :=
  SubLattice { elements :> {fset T}; _ : stable elements }.

Canonical subLattice_subType := Eval hnf in [subType for elements].

Definition subLattice_eqMixin := Eval hnf in [eqMixin of subLattice by <:].
Canonical  subLattice_eqType  := Eval hnf in EqType subLattice subLattice_eqMixin.

Definition subLattice_choiceMixin := [choiceMixin of subLattice by <:].
Canonical  subLattice_choiceType  := Eval hnf in ChoiceType subLattice subLattice_choiceMixin.
(*TODO : MemPred with subLattice*)
End SubLattices.

(* ==================================================================== *)
Section SubLatticesTheory.
Context {T : choiceType} (L : { tblattice T}) (S : subLattice L).

Lemma stable_join : forall x y, x \in (S : {fset _}) -> y \in (S : {fset _}) ->
  join L x y \in (S : {fset _}).
Proof. by case: S => /= fS /stableP[]. Qed.

Lemma stable_meet : forall x y, x \in (S : {fset _}) -> y \in (S : {fset _}) ->
  meet L x y \in (S : {fset _}).
Proof. by case: S => /= fS /stableP[]. Qed.

Canonical join_monoid := Monoid.Law (joinA L) (join0x L) (joinx0 L).
Canonical join_comonoid := Monoid.ComLaw (joinC L).
Canonical meet_monoid := Monoid.Law (meetA L) (meet0x L) (meetx0 L).
Canonical meet_comonoid := Monoid.ComLaw (meetC L).

Definition subtop := \big [(join L)/ (bottom L)]_(i <- S) i.
Definition subbot := \big [(meet L)/ (top L)]_(i <- S) i.

Lemma subtop_leE : forall x, x \in (S : {fset _}) -> x <=_L subtop.
Proof.
move=> x /= x_in_S.
by rewrite /subtop (big_fsetD1 _ x_in_S) /= leEmeet joinKI.
Qed.

Lemma subbot_leE : forall x, x \in (S : {fset _})  -> subbot <=_L x.
Proof.
move => x x_in_S.
by rewrite /subbot (big_fsetD1 _ x_in_S) /= leIl.
Qed.

Lemma subtop_stable : ((S : {fset _}) != fset0) -> subtop \in (S : {fset _}).
Proof.
(*rewrite /big_join; case: S => /= elem /stableP /= [_ stable_join].
case/set0Pn => x; rewrite -mem_enum => x_in_elem; rewrite -mem_enum.
have: forall x y, x \in enum elem -> y \in enum elem -> join L x y \in enum elem.
- by move=> ? ? ? ?; rewrite mem_enum; apply: stable_join; rewrite -mem_enum.
move: x_in_elem; rewrite -big_enum.

Search _ "big".

elim: (enum elem) => /=.
- by rewrite in_nil.
- move=> a l; case: l.
  + by move=> _ _ _; rewrite big_cons big_nil mem_seq1 joinx0.
  + move => b l.
Qed.*)
Admitted.

Lemma subbot_stable : (S : {fset _}) != fset0 -> subbot \in (S : {fset _}).
Admitted.

Lemma subtop_empty : (S : {fset _}) == fset0 -> subtop = bottom L.
Proof.
by move/eqP; rewrite /subtop => ->; rewrite big_seq_fset0.
Qed.

Lemma subbot_empty : (S : {fset _}) == fset0 -> subbot = top L.
Proof.
by move/eqP; rewrite /subbot => ->; rewrite big_seq_fset0.
Qed.

Definition atom a := [&& (a \in (S : {fset _})), (subbot <_L a) &
  ~~[exists x : S, (subbot <_L val x) && (val x <_L a)]].

Definition coatom a := [&& (a \in (S : {fset _})), (a <_L subtop) &
~~[exists x : S, (val x <_L subtop ) && (a <_L val x)]].

Lemma atomP a: reflect
  ([/\ a \in (S : {fset _}), (subbot <_L a) &
  forall x, x \in (S:{fset _}) -> subbot <_L x -> ~~(x <_L a)])
  (atom a).
Proof.
apply/(iffP idP).
- case/andP => a_in_S /andP [bot_lt_a /existsPn atomic]; split => //.
  move=> y y_in_S bot_lt_y; move: (atomic [`y_in_S]%fset) => /=.
  by rewrite negb_and bot_lt_y /=.
- case; rewrite /atom => -> -> /= atomic; apply/existsPn.
  move=> x; rewrite negb_and -implybE; apply/implyP => ?.
  apply/atomic => //.
Qed.

Lemma coatomP a: reflect
  ([/\ a \in (S: {fset _}), (a <_L subtop) &
  forall x, x \in (S:{fset _}) -> x <_L subtop -> ~~(a <_L x)])
  (coatom a).
Proof.
apply/(iffP idP).
- case/andP => a_in_S /andP [bot_lt_a /existsPn coatomic]; split => //.
  move=> y y_in_S bot_lt_y; move: (coatomic [`y_in_S]%fset) => /=.
  by rewrite negb_and bot_lt_y /=.
- case; rewrite /coatom => -> -> /= coatomic; apply/existsPn.
  move=> x; rewrite negb_and -implybE; apply/implyP => ?.
  apply/coatomic => //.
Qed.

End SubLatticesTheory.

Section SubLatticeInd.

Context {T : choiceType} (L : { tblattice T}).

Definition interval (S : subLattice L) (a b : T) := 
  [fset x| x in (S : {fset _ }) & ((a <=_L x) && (x <=_L b))]%fset.

Lemma in_interval_S (S : subLattice L) (a b : T) :
  forall x, x \in interval S a b -> x \in (S : {fset _}).
Proof.
by move=> x; rewrite inE /= unfold_in /= => /and3P [? _ _].
Qed.

Lemma in_interval_ab S a b: forall x, x \in interval S a b ->
  a <=_L x /\ x <=_L b.
Proof.
by move=> x; rewrite in_fsetE /= unfold_in /= => /and3P [_ -> ->].
Qed.


Lemma stable_interval S a b:
  stable L (interval S a b).
Proof.
apply/stableP; split => x y x_in_ab y_in_ab; rewrite in_fsetE unfold_in /=;
  apply/and3P; split; rewrite ?unfold_in.
- apply: stable_meet.
Admitted.

Definition SubLatInterval S a b := SubLattice (stable_interval S a b).

Notation " S : [< a ; b >]" := (SubLatInterval S a b)
  (at level 0, format "S : [<  a  ;  b  >]").

Lemma in_intervalP (S: subLattice L) a b x:
  reflect (x \in (S : {fset _}) /\ a <=_L x /\ x <=_L b)
  (x \in (S:[<a;b>] : {fset _})).
Proof.
apply/(iffP idP).
- by rewrite in_fsetE unfold_in => /and3P [? ? ?].
- by case=> ? [? ?]; rewrite in_fsetE unfold_in /=; apply/and3P.
Qed.

Lemma intervalP : forall S: subLattice L, S = S:[<subbot S; subtop S>].
Proof.
move=> S; apply/eqP/fset_eqP => x; apply/(sameP idP)/(iffP idP).
- exact: in_interval_S.
- by move=> x_in_S; rewrite inE /= unfold_in /=; apply/and3P; split;
    rewrite // ?subtop_leE ?subbot_leE.
Qed.



Lemma sub_interval : forall S0 S : subLattice L, (S `<=` S0)%fset ->
  subbot S0 <=_L subbot S /\ subtop S <=_L subtop S0. 
move=> S0 S; rewrite {1}(intervalP S0).
move/fsubsetP => S_sub_S0; case S_empty: ((S : {fset _ }) == fset0).
- by rewrite (subtop_empty S_empty) (subbot_empty S_empty) topEle botEle.
- move/eqP/eqP: S_empty => S_empty.
  case/S_sub_S0/in_interval_ab: (subtop_stable S_empty).
  by case/S_sub_S0/in_interval_ab: (subbot_stable S_empty).
Qed.

Lemma interval_bot : forall S : subLattice L, forall a b,
  a \in (S : {fset _}) -> a <=_L b ->
  subbot (S: [<a; b>]) = a.
Proof.
move=> S a b a_in_S a_le_b.
have a_in_ab: a \in (S:[<a; b>] : {fset _})
  by rewrite inE unfold_in; apply/and3P; split => //; exact: orefl.
have bot_in_ab: subbot S:[< a ; b>] \in (S:[<a; b>] : {fset _})
  by apply/subbot_stable/fset0Pn; exists a.
apply: (@oanti _ L); rewrite (subbot_leE a_in_ab).
by case: (in_interval_ab bot_in_ab) => ->.
Qed.

Lemma interval_top : forall S : subLattice L, forall a b,
  b \in (S : {fset _}) -> a <=_L b ->
  subtop (S: [<a; b>]) = b.
Proof.
move=> S a b b_in_S a_le_b.
have b_in_ab: b \in (S:[<a; b>] : {fset _})
  by rewrite inE unfold_in; apply/and3P; split => //; exact: orefl.
have top_in_ab: subtop S:[< a ; b>] \in (S:[<a; b>] : {fset _})
  by apply/subtop_stable/fset0Pn; exists b.
apply: (@oanti _ L); rewrite (subtop_leE b_in_ab).
by case: (in_interval_ab top_in_ab) => _ ->.
Qed.

Lemma atom_set (S:subLattice L) a b : a \in (S : {fset _}) ->
  b \in (S : {fset _}) -> a <=_L b ->
  let I_Da := ((S:[<a; b>]) `\ a)%fset in
  ([fset x in (S:{fset _}) | atom S:[<a; b>] x])%fset ==
  ([fset x in I_Da | [forall y:I_Da, (fsval y <=_L x) ==> (fsval y == x)]])%fset.
Proof.
move=> a_in_S b_in_S a_le_b; apply/fset_eqP => x.
apply/(sameP idP)/(iffP idP).
- rewrite !inE /= !unfold_in. 
  case/andP => /and4P [x_neq_a x_in_S a_le_x x_le_b] /forallP mini.
  apply/andP; split => //; apply/atomP; rewrite interval_bot => //; split.
  + by apply/in_intervalP; split.
  + by rewrite ostrict eq_sym x_neq_a a_le_x.
  + move=> y /in_intervalP [y_in_S [a_le_y y_le_b]] a_lt_y.
    apply: contraT; rewrite negbK lt_def => /andP [x_neq_y].
    have y_in_IDa: y \in (S:[<a; b>] `\ a)%fset.
    - rewrite inE; apply/andP; split; last by apply/in_intervalP.
      by rewrite inE (gt_eqF a_lt_y).
    move/implyP: (mini [` y_in_IDa]%fset) => /= absurd /absurd x_eq_y.
    by move: x_neq_y; rewrite eq_sym x_eq_y.
- rewrite !inE /= !unfold_in => /andP [] x_in_S /atomP.
  case => /in_intervalP [_ [a_le_x x_le_b]]; rewrite interval_bot // => a_lt_x.
  move=> atomic; apply/andP; split; [apply/and3P; split |] => //.
  + by rewrite (gt_eqF a_lt_x).
  + by rewrite a_le_x x_le_b.
  + apply/forallP => /= y; apply/implyP/contraTT.
    rewrite le_eqVlt negb_or => -> /=.
    apply/atomic; move: (fsvalP y); rewrite !inE; case/andP => //.
    by rewrite ostrict eq_sym => -> /and3P [].
Qed.

Lemma sub_atomic_top : forall S : subLattice L,
  forall x, x \in (S : {fset _}) -> x <=_L subtop S -> subbot S <_L x ->
  exists a, atom S a /\ (S:[< x ; subtop S>] `<=` (S:[< a; subtop S >]))%fset.
Proof.

(*move=> S x x_in_S x_le_top bot_lt_x.
have x_in_bot_x: x \in (S:[<subbot S ; x >] : {fset _})
  by apply/in_intervalP; split => //; split; [ exact: ltW| exact: orefl].
have bot_in_bot_x: subbot S \in (S : [< subbot S; x>] : {fset _}).
- apply/in_intervalP; split; last split;
    [apply: subbot_stable|exact : orefl| exact: ltW].
  by apply/fset0Pn; exists x.
set I :=
  (S:[<subbot S; x>] `\` ([fset x; subbot S]))%fset.
case eq_I: (I == fset0).
- exists x; move: eq_I; rewrite fsetD_eq0 => /fsubsetP doubleton.
  split => //.
  rewrite /atom x_in_S bot_lt_x; split => //.
  move=> y y_in_S bot_lt_y.
  apply: contraT; rewrite negbK => y_lt_x.
  have/doubleton: y \in (S: [<subbot S ; x >] : {fset _})
    by apply/in_intervalP; split => //; split; [exact :ltW| exact: ltW].
  rewrite in_fsetE !in_fset1.
  by rewrite (lt_eqF y_lt_x) /= -(lt_eqF bot_lt_y) eq_sym.
- case/fset0Pn: eq_I => a; do 4 rewrite in_fsetE.
  case/andP; rewrite negb_or; case/andP => a_neq_x a_neq_bot.
  case/in_intervalP => a_in_S [bot_le_a a_le_x].
  exists a; split.
  + split => //; rewrite ?lt_def ?a_neq_bot ?bot_le_a //.
    move=> x0 x0_in_S bot_lt_.
    admit.
  + admit.*)
Admitted.


Variable (P : subLattice L -> Prop) (S0 : subLattice L).
Hypothesis (P_0 : P S0).
Hypothesis (P_incr : forall S, forall x, atom S x -> P S -> P S:[< x; subtop S>]).
Hypothesis (P_decr : forall S, forall x, coatom S x -> P S -> P S:[<subbot S; x>]).

Goal forall S : subLattice L, (S `<=` S0)%fset -> P S. (*forall x y, P S0:[<x; y>] ?*)
move=> S S_sub_S0.
Admitted.

(* P S0 est vrai            *)
(* étant donnés x, y \in L, '[< x; y>] est un subLattice S *)
(* forall S, forall x, atom S x -> P S -> P '[< x; top S >] *)
(* forall S, forall x, coatom S x -> P S -> P '[< bot S; x >] *)
(* Goal forall S, S \subset S0 -> P S *)


End SubLatticeInd.

Module GradedLattice.
Section ClassDef.
Variable (T: finType).


Record class (L : {tblattice T}) := Class
{
  rank : T -> nat;
  _ : rank (bottom L) = O%N;
  _ : forall x y, x <_L y -> (rank x < rank y)%N;
  _ : forall x y, x <=_L y -> ((rank x).+1 < rank y)%N -> exists z, (x <_L z) && (z <_L y)
}.

Structure pack (phr : phant (rel T)) := Pack
{
  pack_lattice;
  pack_class : class pack_lattice
}.

Local Coercion pack_lattice : pack >-> TBLattice.pack.
Local Coercion pack_class : pack >-> class.

Variable (phr : phant (rel T)) (gl : pack phr).

Canonical porder_of := TBLattice.porder_of gl. 

End ClassDef.
Module Exports.

Coercion pack_lattice : pack >-> TBLattice.pack.
Coercion pack_class : pack >-> class.
Canonical porder_of.
Notation rank L := (rank L).
Notation "{ 'glattice' T }" := (pack (Phant (rel T)))
  (at level 0, format "{ 'glattice'  T }").
Notation GLatticeClass rkbot rkinc rkdens := (Class rkbot rkinc rkdens).
Notation GLatticePack cla := (Pack (Phant _) cla).
End Exports.
End GradedLattice.
Include GradedLattice.Exports.

Section GLatticeTheory.
Variable (T : finType) (L : {glattice T}).

Lemma rk_bottom : rank L (bottom L) = 0%N.
Proof.
by case: L => ? [].
Qed.

Lemma rk_increasing : forall x y, x <_L y -> (rank L x < rank L y)%N.
Proof.
by case: L => ? [].
Qed.

Lemma rk_dense : forall x y,
  x <=_L y -> ((rank L x).+1 < rank L y)%N -> exists z, (x <_L z) && (z <_L y).
Proof.
by case: L => ? [].
Qed.
End GLatticeTheory.

Section SubsetLattice.
Variable (T : finType).

Definition subset (A B : {set T}) := A \subset B.
Definition ssubset (A B : {set T}) := (A != B) && subset A B.

Lemma subset_order : order subset.
Proof.
split.
- exact: subxx.
- move=> X Y /andP [] /subsetP subXY /subsetP subYX.
  apply/setP => x.
  by apply/(sameP idP)/(equivP idP); split; [move/subYX | move/subXY].
- move=> Y X Z /subsetP subXY /subsetP subYZ.
  by apply/subsetP => x; move/subXY/subYZ.
Qed.

Lemma subset_strict : strict ssubset subset.
Proof.
by [].
Qed.

Definition SOrderClass := OrderClass subset_order subset_strict.
Canonical SOrderPack := OrderPack SOrderClass.
Notation C := SOrderPack.

Definition Smeet (A B : {set T}) := A :&: B.

Lemma SmeetC : commutative Smeet.
Proof.
exact: setIC.
Qed.

Lemma SmeetA : associative Smeet.
Proof.
exact: setIA.
Qed.

Lemma Smeetxx : idempotent Smeet.
Proof.
exact: setIid.
Qed.

Lemma leESmeet : forall X Y, (X <=_C Y) = (Smeet X Y == X).
Proof.
move=> X Y; apply/(sameP idP)/(iffP idP).
- by move/eqP/setIidPl.
- by move/setIidPl/eqP.
Qed.

Definition SMeetClass := MeetClass SmeetC SmeetA Smeetxx leESmeet.
Canonical SMeetPack := MeetPack SMeetClass.

Definition Sjoin (X Y : {set T}) := (X :|: Y).

Lemma SjoinC : commutative Sjoin.
Proof.
exact : setUC.
Qed.

Lemma SjoinA : associative Sjoin.
Proof.
exact: setUA.
Qed.

Lemma Sjoinxx : idempotent Sjoin.
Proof.
exact: setUid.
Qed.

Lemma SjoinKI : forall Y X, meet C X (Sjoin X Y) = X.
Proof.
move=> X Y; rewrite SjoinC.
exact:setKU.
Qed.

Lemma SjoinKU : forall Y X, Sjoin X (meet C X Y) = X.
Proof.
move=> X Y; rewrite SjoinC.
exact: setIK.
Qed.

Lemma leESjoin : forall Y X, (Y <=_C X) = ((Sjoin X Y) == X).
Proof.
move=> Y X; apply/(sameP idP)/(iffP idP).
- by move/eqP/setUidPl.
- by move/setUidPl/eqP.
Qed.

Definition SLatticeClass :=
  LatticeClass SjoinC SjoinA Sjoinxx SjoinKI SjoinKU leESjoin.
Canonical SLatticePack := LatticePack SLatticeClass.

Lemma SbotEle : forall A, set0 <=_C A.
Proof.
exact: sub0set.
Qed.

Lemma StopEle : forall A, A <=_C [set: T].
Proof.
exact: subsetT.
Qed.

Definition STBLatticeClass := TBLatticeClass StopEle SbotEle.
Canonical STBLatticePack := TBLatticePack STBLatticeClass.

End SubsetLattice.

