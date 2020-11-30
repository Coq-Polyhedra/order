(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope fset_scope.
Local Open Scope ring_scope.

(* ==================================================================== *)
Section FSetRect.
Context (T : choiceType) (P : {fset T} -> Type).

Hypothesis P0 : P fset0.
Hypothesis PS : forall x S, x \notin S -> P S -> P (x |` S).

Lemma fset_rect S : P S.
Proof.
move: {2}#|`S| (@leqnn #|`S|) => n; elim: n S => [|n ih] S.
- by rewrite leqn0 cardfs_eq0 => /eqP->.
rewrite leq_eqVlt ltnS orbC; case: leqP => /= [/ih //|_ nz_S].
have: S != fset0 by rewrite -cardfs_gt0 (eqP nz_S).
move/fset0Pn => x; have: xchoose x \in S by apply: xchooseP.
move/fsetD1K => <-; apply: PS; first by rewrite !in_fsetE eqxx.
apply: ih; move: nz_S; rewrite (cardfsD1 (xchoose x)).
by rewrite (xchooseP x) add1n => /eqP[] <-.
Qed.
End FSetRect.

Definition fset_ind (T : choiceType) (P : {fset T} -> Prop) :=
  @fset_rect T P.

(* ==================================================================== *)

(*
(*Test HB*)

HB.mixin Record EQType_of_Type T :=
  {
    op : rel T;
    eq_ax : Equality.axiom op
  }.
HB.structure Definition EQType := {T of EQType_of_Type T}.

HB.mixin Record porder_of_EQType T of (EQType T) :=
  {
    le : rel T;
    lt : rel T;
    lexx : reflexive le;
    le_anti : antisymmetric le;
    le_trans : transitive le;
    ostrict : forall x y : T, lt x y = (~~ op x y) && (le x y)
  }.
HB.structure Definition POrder := {T of porder_of_EQType T &}.
Notation "x <=_ r y" := (@le r x y) (at level 65, r at level 2).
Check @le.
Check forall (r: POrder.type) (x:r), x <=_r x.

(*End of test HB*)
*)
Module Order.
Section ClassDef.

Context {T: eqType}.

Definition axiom (r : rel T) :=
  [/\ reflexive r, antisymmetric r & transitive r].

Definition strict (lt le: rel T) :=
  forall x y, lt x y = (x != y) && (le x y).

Record class (le lt dle: rel T) := Class {
  _ : axiom le;
  _ : strict lt le;
  _ : forall x y, dle x y = le y x;
}.

(*TODO : Confirm that the phantom is required*)
Structure pack (phr : phant (rel T)) := Pack {
  pack_le; pack_lt; pack_dle;
  pack_class : class pack_le pack_lt pack_dle
}.

Variable (phr : phant (rel T)) (r : pack phr).

Definition class_of := let: Pack _ _ _ c as r0 := r
  return (class (pack_le r0) (pack_lt r0)) (pack_dle r0) in c.

Definition pack_of_le (r : rel T) :=
  fun (ro : pack phr) & phant_id (pack_le ro) r =>
  ro.

Definition pack_of_lt (r : rel T) :=
  fun (ro : pack phr) & phant_id (pack_lt ro) r =>
  ro.
End ClassDef.

(* -------------------------------------------------------------------- *)
Module Exports.
Notation lto r := (pack_lt r).
Notation leo r := (pack_le r).
Notation dleo r := (pack_dle r).
Notation axiom le := (axiom le).
Notation strict lt le := (strict lt le).
Notation OrderClass ax st du := (Class ax st du).
Notation OrderPack cla := (Pack (Phant _) cla).
Notation "{ 'porder' T }" := (pack (Phant (rel T)))
  (at level 0, format "{ 'porder'  T }").
Notation "<=: r" := (leo r) (at level 2, r at level 1, format "<=: r").
Notation "<: r" := (lto r) (at level 2, r at level 1, format "<: r").
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

(* ==================================================================== *)
Section OrderTheory.

Variables ( T: eqType ) (r: {porder T}).

Local Notation "x <= y"      := (x <=_r y).
Local Notation "x < y"       := (x <_r y).
Local Notation "x <= y <= z" := ((x <= y) && (y <= z)).
Local Notation "x < y < z"   := ((x < y) && (y < z)).
Local Notation "x < y <= z"  := ((x < y) && (y <= z)).
Local Notation "x <= y < z"  := ((x <= y) && (y < z)).


Lemma orderP : axiom (<=:r).
Proof. by case: r => le ? ? []. Qed.

Lemma lexx : reflexive (<=:r).
Proof. by case: orderP. Qed.

Lemma le_anti : antisymmetric (<=:r).
Proof.
by case: orderP.
Qed.

Lemma le_trans : transitive (<=:r).
Proof.
by case: orderP.
Qed.

Lemma ostrict: forall (x y : T), (x < y) = (x != y) && (x <= y).
Proof.
by move=> x y; case: r => le lt ? [].
Qed.

Lemma ltxx x : x < x = false.
Proof. by rewrite ostrict eq_refl lexx. Qed.

Lemma lt_neqAle x y: (x < y) = (y != x) && (x <= y).
Proof.
rewrite eq_sym; exact: ostrict.
Qed.

Lemma le_eqVlt x y: (x <= y) = (x == y) || (x < y).
Proof.
by rewrite ostrict; case: eqP => //= ->; rewrite lexx.
Qed.

Lemma lt_eqF x y: x < y -> x == y = false.
Proof.
by rewrite ostrict => /andP [/negbTE->].
Qed.

Lemma gt_eqF x y: y < x -> x == y = false.
Proof.
by apply: contraTF => /eqP ->; rewrite ltxx. 
Qed.

Lemma eq_le x y: (x == y) = (x <= y <= x).
Proof.
by apply/eqP/idP => [->|/le_anti]; rewrite ?lexx.
Qed.

Lemma ltW x y: x < y -> x <= y.
Proof.
by rewrite le_eqVlt orbC => ->.
Qed.

Lemma lt_le_trans y x z: x < y -> y <= z -> x < z.
Proof.
rewrite !ostrict => /andP [nexy lexy leyz].
rewrite (le_trans lexy) // andbT; apply: contraNneq nexy.
by move=> eqxz; rewrite eqxz eq_le leyz andbT in lexy *.
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
by move=> xy /(lt_trans xy); rewrite ltxx.
Qed.

Lemma lt_asym x y : x < y < x = false.
Proof.
by apply/negP => /andP []; apply: lt_nsym.
Qed.

Lemma le_gtF x y: x <= y -> y < x = false.
Proof.
by move=> le_xy; apply/negP => /lt_le_trans /(_ le_xy); rewrite ltxx.
Qed.

Lemma lt_geF x y : (x < y) -> y <= x = false.
Proof.
by move=> le_xy; apply/negP => /le_lt_trans /(_ le_xy); rewrite ltxx.
Qed.

Definition lt_gtF x y hxy := le_gtF (@ltW x y hxy).

Lemma lt_leAnge x y : (x < y) = (x <= y) && ~~ (y <= x).
Proof.
apply/idP/idP => [ltxy|/andP[lexy Nleyx]]; first by rewrite ltW // lt_geF.
rewrite ostrict lexy andbT; apply: contraNneq Nleyx => ->; exact: lexx.
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

(* ==================================================================== *)
Section FsetOrderTheory.

Context {T : choiceType} (L : {porder T}).

Implicit Types (K : {fset T}).

Lemma ex_min_elt K : K != fset0 ->
  exists2 m, m \in K & forall x, x \in K -> ~~ (x <_L m).
Proof.
elim/fset_ind: K => //= [x S _ _ _]; elim/fset_ind: S => /= [|y S _ ih].
- exists x; first by rewrite !in_fsetE eqxx.
  by move=> y; rewrite !in_fsetE orbF => /eqP->; rewrite ltxx.
case: ih => m m_in_xS min_m; exists (if y <_L m then y else m).
- case: ifP => _; first by rewrite !in_fsetE eqxx !Monoid.simpm.
  by rewrite fsetUCA in_fsetU m_in_xS orbT.
move=> z; rewrite fsetUCA in_fsetU in_fset1 => /orP[].
- by move/eqP=> ->; case: ifP =>[|/negbT//]; rewrite ltxx.
move=> z_in_xS; case: ifPn => [le_ym|leN_ym].
- by apply: contra (min_m _ z_in_xS) => /lt_trans; apply.
- by apply: min_m.
Qed.

Definition minset K :=
  [fset x in K | [forall y : K, ~~(fsval y <_L x)]].

Lemma mem_minsetP K x : x \in K ->
  reflect
    (forall y, y \in K -> ~~ (y <_L x))
    (x \in minset K).
Proof.
move=> xK; apply: (iffP idP).
- rewrite !inE /= => /andP[_ /forall_inP /= h].
  by move=> y yK; apply/negP => /(h [`yK]).
- by move=> h; rewrite !inE /= xK /=; apply/forallP => z; apply/h.
Qed.

Lemma mem_minsetE K x :
  x \in minset K -> x \in K /\ (forall y, y \in K -> ~~ (y <_L x)).
Proof.
move=> min_x; have xK: x \in K by move: min_x; rewrite !inE => /andP[].
by split=> //; apply/mem_minsetP.
Qed.

Lemma minset_neq0 (K : {fset T}) : K != fset0 -> minset K != fset0.
Proof.
case/ex_min_elt => x x_in_K min_x.
by apply/fset0Pn; exists x; apply/mem_minsetP.
Qed.
End FsetOrderTheory.

(* ==================================================================== *)

Section DualOrder.

Context (T: eqType).
Variable (r : {porder T}).

Definition dlto x y := (x != y) && (dleo r x y).

Lemma leEdual x y : dleo r x y = y <=_r x.
Proof.
by case: r => ? ? ? [].
Qed.

Lemma dual_lexx : reflexive (dleo r).
Proof.
move=> x; rewrite leEdual; exact: lexx.
Qed.

Lemma dual_le_anti : antisymmetric (dleo r).
Proof.
by move=> x y; rewrite !leEdual; move/le_anti => ->.
Qed.

Lemma dual_le_trans : transitive (dleo r).
move=> y x z; rewrite !leEdual => le_yx le_zy.
exact: (le_trans le_zy).
Qed.

Lemma dual_order : axiom (dleo r).
Proof.
split;
  [exact : dual_lexx | exact: dual_le_anti | exact: dual_le_trans].
Qed.

Lemma dual_strict : strict dlto (dleo r).
Proof.
by move=> x y; rewrite /dlto.
Qed.

Lemma dualleE x y : x <=_r y = (dleo r) y x.
Proof.
by rewrite leEdual.
Qed. 

Definition DualOrderClass := OrderClass dual_order dual_strict dualleE.
Canonical DualOrderPack := OrderPack DualOrderClass.

Lemma dual_le x y: (x <=_(DualOrderPack) y) = y <=_r x.
Proof. by rewrite /= leEdual. Qed.

Lemma dual_lt x y: (x <_(DualOrderPack) y) = y <_r x.
Proof. by rewrite /= dual_strict leEdual ostrict eq_sym. Qed.

End DualOrder.

Notation "r ^~" := (DualOrderPack r) (at level 8, format "r ^~").

Section DualOrderTheory.
Context {T: eqType}.
Variable (r : {porder T}).

Lemma le_dual_inv x y: x <=_((r^~)^~) y = x <=_r y.
Proof. by []. Qed.

Lemma lt_dual_inv x y: x <_((r^~)^~) y = x <_r y.
Proof. by rewrite /= ostrict /dlto. Qed.

Check (r = (r^~)^~).

End DualOrderTheory.



(* ==================================================================== *)
Module TotalOrder.
Section ClassDef.

Context {T : eqType}.

Definition mixin_of (r : rel T) :=
  forall x y, r x y || r y x.

Record class (le lt : rel T) := Class {
  base : Order.class le lt;
  mixin : mixin_of le
}.

Structure pack (phr : phant (rel T)) := Pack {
  pack_le;
  pack_lt;
  pack_class : class pack_le pack_lt
}.

Variable (phr : phant (rel T)) (rT : pack phr).

Definition class_of := let: Pack _ _ c as rT' := rT
  return class (pack_le rT') (pack_lt rT') in c.    

Canonical order := OrderPack (base class_of).
End ClassDef.

(* -------------------------------------------------------------------- *)
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
Proof. by case: r => ?? []. Qed.

Lemma totalP : order (leo r).
Proof. by case: r => ? ? [[]]. Qed. 
End TotalOrderTheory.

(* ==================================================================== *)
Module Meet.
(*TODO : Adapter la structure MeetSemilattice de order.v*)
Section ClassDef.
Context {T : eqType}.

Record class (r : {porder T}) := Class {
  meet : T -> T -> T;
  _ : commutative meet;
  _ : associative meet;
  _ : idempotent meet;
  _ : forall x y, (x <=_r y) = (meet x y == x)
}.

Structure pack (phr : phant (rel T)) := Pack {
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

(* -------------------------------------------------------------------- *)
Module Exports.
Coercion pack_order : pack >-> Order.pack.
Coercion pack_class : pack >-> class.
Canonical porder_of.
Notation meet r := (@meet_of _ (Phant _) r _ id).
Notation "{ 'meetSemiLattice' T }" := (pack (Phant (rel T)))
  (at level 0, format "{ 'meetSemiLattice'  T }").
Notation MeetClass meetC meetA meetxx leEmeet :=
  (Class meetC meetA meetxx leEmeet).
Notation MeetPack cla := (Pack (Phant _)cla). 
End Exports.
End Meet.

Include Meet.Exports.

(* ==================================================================== *)
Section MeetTheory.
Context {T: eqType} (r: {meetSemiLattice T}).

Local Notation "x `&` y" := (meet r x y).
Local Notation "x <= y" := (x <=_r y).

Lemma meetC : commutative (meet r).
Proof. by case: r => ? []. Qed.

Lemma meetA : associative (meet r).
Proof. by case: r => ? []. Qed.

Lemma meetxx : idempotent (meet r).
Proof. by case: r => ? []. Qed.

Lemma leEmeet x y : (x <= y) = (x `&` y == x).
Proof. by case: r => ? []. Qed.

Lemma meetAC : right_commutative (meet r).
Proof. by move=> x y z; rewrite -!meetA [X in _ `&` X]meetC. Qed.

Lemma meetCA : left_commutative (meet r).
Proof. by move=> x y z; rewrite !meetA [X in X `&` _]meetC. Qed.

Lemma meetACA : interchange (meet r) (meet r).
Proof. by move=> x y z t; rewrite !meetA [X in X `&` _]meetAC. Qed.

Lemma meetKI y x : x `&` (x `&` y) = x `&` y.
Proof. by rewrite meetA meetxx. Qed.

Lemma meetIK y x : (x `&` y) `&` y = x `&` y.
Proof. by rewrite -meetA meetxx. Qed.

Lemma meetKIC y x : x `&` (y `&` x) = x `&` y.
Proof. by rewrite meetC meetIK meetC. Qed.

Lemma meetIKC y x : y `&` x `&` y = x `&` y.
Proof. by rewrite meetAC meetC meetxx. Qed.

Lemma lexI x y z : (x <= y `&` z) = (x <= y) && (x <= z).
Proof.
rewrite !leEmeet; apply/eqP/andP => [<-|[/eqP<- /eqP<-]].
  by rewrite meetA meetIK eqxx -meetA meetACA meetxx meetAC eqxx.
by rewrite -[X in X `&` _]meetA meetIK meetA.
Qed.

Lemma leIxl x y z : y <= x -> y `&` z <= x.
Proof. by rewrite !leEmeet meetAC => /eqP ->. Qed.

Lemma leIxr x y z : z <= x -> y `&` z <= x.
Proof. by rewrite !leEmeet -meetA => /eqP ->. Qed.

Lemma leIx2 x y z : (y <= x) || (z <= x) -> y `&` z <= x.
Proof. by case/orP => [/leIxl|/leIxr]. Qed.

Lemma leIr x y : y `&` x <= x.
Proof. by rewrite leIx2 ?lexx ?orbT. Qed.

Lemma leIl x y : x `&` y <= x.
Proof. by rewrite leIx2 ?lexx ?orbT. Qed.

Lemma meet_idPl {x y} : reflect (x `&` y = x) (x <= y).
Proof. by rewrite leEmeet; apply/eqP. Qed.

Lemma meet_idPr {x y} : reflect (y `&` x = x) (x <= y).
Proof. by rewrite meetC; apply/meet_idPl. Qed.

Lemma meet_l x y : x <= y -> x `&` y = x.
Proof. exact/meet_idPl. Qed.

Lemma meet_r x y : y <= x -> x `&` y = y.
Proof. exact/meet_idPr. Qed.

Lemma leIidl x y : (x <= x `&` y) = (x <= y).
Proof. by rewrite !leEmeet meetKI. Qed.

Lemma leIidr x y : (x <= y `&` x) = (x <= y).
Proof. by rewrite !leEmeet meetKIC. Qed.

Lemma eq_meetl x y : (x `&` y == x) = (x <= y).
Proof. by apply/esym/leEmeet. Qed.

Lemma eq_meetr x y : (x `&` y == y) = (y <= x).
Proof. by rewrite meetC eq_meetl. Qed.

Lemma leI2 x y z t : x <= z -> y <= t -> x `&` y <= z `&` t.
Proof. by move=> xz yt; rewrite lexI !leIx2 ?xz ?yt ?orbT. Qed.
End MeetTheory.

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
- apply/(le_anti _ [leo: <=%O])/andP; rewrite /=.
  split; [exact : joinC_ex | exact : joinC_ex].
by rewrite ltxx.
Qed.

End NumJoin.*)

(* ==================================================================== *)
Module Lattice.
Section ClassDef.

Context {T : eqType}.

Record class (r : {meetSemiLattice T}) := Class {
  join : T -> T -> T;
  _ : commutative join;
  _ : associative join;
  _ : idempotent join;
  _ : forall y x, meet r x (join x y) = x;
  _ : forall y x, join x (meet r x y) = x;
  _ : forall y x, (y <=_r x) = ((join x y) == x) 
}.

Structure pack (phr : phant (rel T)) := Pack {
  pack_order;
  pack_class : class pack_order
}.

Variables (phr : phant (rel T)) (mjr : pack phr).
Local Coercion pack_order : pack >-> Meet.pack.
Local Coercion pack_class : pack >-> class.

Canonical porder_of := Order.Pack phr (Order.class_of (Meet.pack_order mjr)).

Definition join_of (r : {porder T}) :=
  fun (mr : {meetSemiLattice T}) & phant_id (Meet.pack_order mr) r =>
  fun (lr : pack phr) & phant_id (pack_order lr) mr =>
  join lr.    

Definition lattice_of (r : {porder T}) :=
  fun (mr : {meetSemiLattice T}) & phant_id (Meet.pack_order mr) r =>
  fun (lr : pack phr) & phant_id (pack_order lr) mr =>
  lr.

End ClassDef.

(* -------------------------------------------------------------------- *)
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
Notation "[ 'lattice' 'of' r ]" := (@lattice_of _ (Phant _) r _ id _ id)
  (at level 0, format "[ 'lattice'  'of'  r ]").

End Exports.
End Lattice.
Include Lattice.Exports.

Section LatticeTheory.
Context {T : eqType} (r : {lattice T}).

Local Notation "x `&` y" := (meet r x y).
Local Notation "x `|` y" := (join r x y).
Local Notation "x <= y" := (x <=_r y).

Lemma joinC : commutative (join r).
Proof. by case: r => ? []. Qed.

Lemma joinA : associative (join r).
Proof. by case: r => ? []. Qed.

Lemma joinxx : idempotent (join r).
Proof. by case: r => ? []. Qed.

Lemma joinKI y x : x `&` (x `|` y) = x.
Proof. by case: r => ? []. Qed.

Lemma meetKU y x : x `|` (x `&` y) = x.
Proof. by case: r => ? []. Qed.

Lemma joinKIC y x : x `&` (y `|` x) = x.
Proof. by rewrite joinC joinKI. Qed.

Lemma meetKUC y x : x `|` (y `&` x) = x.
Proof. by rewrite meetC meetKU. Qed.

Lemma meetUK x y : (x `&` y) `|` y = y.
Proof. by rewrite joinC meetC meetKU. Qed.

Lemma joinIK x y : (x `|` y) `&` y = y.
Proof. by rewrite joinC meetC joinKI. Qed.

Lemma meetUKC x y : (y `&` x) `|` y = y.
Proof. by rewrite meetC meetUK. Qed.

Lemma joinIKC x y : (y `|` x) `&` y = y.
Proof. by rewrite joinC joinIK. Qed.

Lemma leEjoin x y : (x <= y) = (x `|` y == y).
Proof.
by rewrite leEmeet; apply/eqP/eqP => <-; rewrite (joinKI, meetUK).
Qed.

Lemma joinAC : right_commutative (join r).
Proof. by move=> x y z; rewrite -!joinA [X in _ `|` X]joinC. Qed.

Lemma joinCA : left_commutative (join r).
Proof. by move=> x y z; rewrite !joinA [X in X `|` _]joinC. Qed.

Lemma joinACA : interchange (join r) (join r).
Proof. by move=> x y z t; rewrite !joinA [X in X `|` _]joinAC. Qed.

Lemma leUx x y z : (x `|` y <= z) = (x <= z) && (y <= z).
Proof.
rewrite !leEjoin; apply/eqP/andP => [<-|[/eqP<- /eqP<-]].
- by rewrite !joinA joinxx eqxx [_ `|` y]joinAC joinxx [_ `|` x]joinC eqxx.
- by rewrite [y `|` _]joinCA [x `|` (_ `|` _)]joinA joinA joinxx.
Qed.

Lemma lexUl x y z : x <= y -> x <= y `|` z.
Proof. by rewrite !leEjoin joinA => /eqP->. Qed.

Lemma lexUr x y z : x <= z -> x <= y `|` z.
Proof. by rewrite !leEjoin joinCA => /eqP->. Qed.

Lemma lexU2 x y z : (x <= y) || (x <= z) -> x <= y `|` z.
Proof. by case/orP => [/lexUl|/lexUr]. Qed.

Lemma leUr x y : x <= y `|` x.
Proof. by apply/lexUr/lexx. Qed.

Lemma leUl x y : x <= x `|` y.
Proof. by apply/lexUl/lexx. Qed.

Lemma join_idPl x y : reflect (x `|` y = y) (x <= y).
Proof. rewrite leEjoin; apply/eqP. Qed.

Lemma join_idPr x y : reflect (y `|` x = y) (x <= y).
Proof. by rewrite joinC; apply/join_idPl. Qed.
End LatticeTheory.

(* ==================================================================== *)

Section DualLattice.

Context (T: eqType) (r : {lattice T}).

Lemma dual_leEmeet: forall x y, (x <=_(r^~) y) = ((join r x y) == x).
Proof.
by move=> x y /=; rewrite leEjoin joinC.
Qed.

Definition DualMeetClass :=
  MeetClass (joinC r) (joinA r) (joinxx r) dual_leEmeet.
Canonical DualMeetPack := MeetPack DualMeetClass.

Lemma dual_joinKI : forall y x, meet (r^~) x (meet r x y) = x.
Proof.
by move=> y x /=; rewrite /(meet r^~) /= meetKU.
Qed.

Lemma dual_joinKU : forall y x, meet r x (meet r^~ x y) = x.
by move=> y x; rewrite /(meet r^~) /= joinKI.
Qed.

Lemma dual_leEjoin : forall y x, (y <=_(r^~) x) = ((meet r x y) == x).
Proof.
by move=> y x /=; rewrite leEmeet.
Qed.

Definition DualLatticeClass := LatticeClass (meetC r) (meetA r) (meetxx r)
    dual_joinKI dual_joinKU dual_leEjoin.
Canonical DualLatticePack := LatticePack DualLatticeClass.

Lemma dual_meet: meet r^~ = join r.
Proof.
by [].
Qed.

Lemma dual_join: join r^~ = meet r.
Proof.
by [].
Qed.




End DualLattice.

(* ==================================================================== *)
Module TBLattice.
Section ClassDef.

Context {T : eqType}.

Record class (L : {lattice T}) := Class {
  bottom : T;
  top : T;
  _ : forall x, x <=_L top;
  _ : forall x, bottom <=_L x
}.

Structure pack (phr : phant (rel T)) := Pack {
  pack_lattice;
  pack_class : class pack_lattice
}.

Local Coercion pack_lattice: pack >-> Lattice.pack.
Local Coercion pack_class: pack >-> class.

Variable (phr : phant (rel T)) (bl : pack phr).

Canonical porder_of := Lattice.porder_of bl.

Definition bottom_of (r: {porder T}) :=
  fun (mo : {meetSemiLattice T}) & phant_id (Meet.pack_order mo) r =>
  fun (l : {lattice T}) & phant_id (Lattice.pack_order l) mo =>
  fun (bl : pack phr) & phant_id (pack_lattice bl) l =>
  bottom bl.

Definition top_of (r: {porder T}) :=
  fun (mo : {meetSemiLattice T} ) & phant_id (Meet.pack_order mo) r =>
  fun (l : {lattice T} ) & phant_id (Lattice.pack_order l) mo =>
  fun (bl : pack phr) & phant_id (pack_lattice bl) l =>
  top bl.

Definition tblattice_of (r: {porder T}) :=
  fun (mo : {meetSemiLattice T} ) & phant_id (Meet.pack_order mo) r =>
  fun (l : {lattice T} ) & phant_id (Lattice.pack_order l) mo =>
  fun (bl : pack phr) & phant_id (pack_lattice bl) l =>
  bl.
End ClassDef.

(* -------------------------------------------------------------------- *)
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
Notation "[ 'tblattice' 'of' r ]" :=
  (@tblattice_of _ (Phant _) r _ id _ id _ id)
  (at level 0, format "[ 'tblattice'  'of'  r ]").
End Exports.

End TBLattice.
Include TBLattice.Exports.

(* -------------------------------------------------------------------- *)
Section TBLatticeTheory.
Context {T : eqType} (L : {tblattice T}).

Lemma le0x : forall x, bottom L <=_L x.
Proof.
by case: L => ? [].
Qed.

Lemma lex1 : forall x, x <=_L top L.
Proof.
by case: L => ? [].
Qed.

Lemma joinx0 : right_id (bottom L) (join L).
Proof.
by move=> x; apply/eqP; rewrite joinC -leEjoin le0x.
Qed.

Lemma join0x : left_id (bottom L) (join L).
Proof.
by move=> x; apply/eqP; rewrite -leEjoin le0x.
Qed.

Lemma meet1x : left_id (top L) (meet L).
Proof.
by move=> x; apply/eqP; rewrite meetC -leEmeet lex1.
Qed.

Lemma meetx1 : right_id (top L) (meet L).
Proof.
by move=> x; apply/eqP; rewrite -leEmeet lex1.
Qed.
End TBLatticeTheory.

(* ==================================================================== *)

Section DualTBLattice.

Context {T: eqType} (L : {tblattice T}).

Lemma dual_lex1 : forall x : T, (top L) <=_(L^~) x.
Proof.
exact: lex1.
Qed.

Lemma dual_le0x : forall x: T, x <=_(L^~) (bottom L).
Proof.
exact: le0x.
Qed.

Definition DualTBLatticeClass := TBLatticeClass dual_le0x dual_lex1.
Canonical DualTBLatticePack := TBLatticePack DualTBLatticeClass.

Lemma dual_top : top (L^~) = bottom L.
Proof.
by [].
Qed.

Lemma dual_bot : bottom (L^~) = top L.
Proof.
by [].
Qed.



End DualTBLattice.

(* ==================================================================== *)
Section BigOps.
Context {T : eqType} (L : {tblattice T}).

Canonical join_monoid := Monoid.Law (joinA L) (join0x L) (joinx0 L).
Canonical join_comonoid := Monoid.ComLaw (joinC L).
Canonical meet_monoid := Monoid.Law (meetA L) (meet1x L) (meetx1 L).
Canonical meet_comonoid := Monoid.ComLaw (meetC L).

Lemma meet_max_seq {I : eqType} (r : seq I) (P : pred I) (F : I -> T) (x : I) :
  x \in r -> P x -> \big[meet L/top L]_(i <- r | P i) F i <=_L F x.
Proof.
move=> xr Px; rewrite (perm_big _ (perm_to_rem xr)) /=.
by rewrite big_cons /= Px; apply/leIl.
Qed.

Lemma meetsP_seq {I : eqType}  (r : seq I) (P : pred I) (F : I -> T) (x : T) :
  reflect
    (forall i, i \in r -> P i -> x <=_L F i)
    (x <=_L \big[meet L/top L]_(i <- r | P i) F i).
Proof.
have ->:
  x <=_L \big[meet L/top L]_(i <- r | P i) F i
    = \big[andb/true]_(i <- r | P i) (x <=_L F i).
- by elim/big_rec2: _ => [|i b y Pi <-]; rewrite 1?(lex1, lexI).
by rewrite big_all_cond; apply: (iffP allP) => h i ir; apply/implyP/h.
Qed.

Lemma join_min_seq {I : eqType} (r : seq I) (P : pred I) (F : I -> T) (x : I) :
  x \in r -> P x -> F x <=_L \big[join L/bottom L]_(i <- r | P i) F i.
Proof.
move=> xr Px; rewrite (perm_big _ (perm_to_rem xr)) /=.
by rewrite big_cons /= Px; rewrite leUl.
Qed.

Lemma joinsP_seq {I : eqType}  (r : seq I) (P : pred I) (F : I -> T) (x : T) :
  reflect
    (forall i, i \in r -> P i -> F i <=_L x)
    (\big[join L/bottom L]_(i <- r | P i) F i <=_L x).
Proof.
have ->:
  \big[join L/bottom L]_(i <- r | P i) F i <=_L x
    = \big[andb/true]_(i <- r | P i) (F i <=_L x).
- by elim/big_rec2: _ => [|i b y Pi <-]; rewrite 1?(le0x, leUx).
by rewrite big_all_cond; apply: (iffP allP) => h i ir; apply/implyP/h.
Qed.
End BigOps.

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
Context {T : choiceType} (L : {lattice T}).

Definition stable (E : {fset T}) :=
     [forall x : E, [forall y : E, meet L (val x) (val y) \in E]]
  && [forall x : E, [forall y : E, join L (val x) (val y) \in E]].

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

Coercion mem_subLattice (S: subLattice) : {pred T} :=
  fun x : T => (x \in (elements S)).
Canonical subLattice_predType := PredType mem_subLattice.

Lemma in_subLatticeE (S: subLattice) x : (x \in S) = (x \in elements S).
Proof. by []. Qed.

Definition inE := (in_subLatticeE, inE).

End SubLattices.

(* ==================================================================== *)
Section SubLatticesTheory.
Context {T : choiceType} (L : {lattice T}) (S : subLattice L).

Lemma mem_join x y:
  x \in S -> y \in S -> join L x y \in S.
Proof.
by rewrite !inE; case: S => fS /= /stableP[] => _; apply.
Qed.

Lemma mem_meet x y:
  x \in S -> y \in S -> meet L x y \in (S : {fset _}).
Proof. by rewrite !inE; case: S => /= fS /stableP[] => H _; exact: H. Qed.

End SubLatticesTheory.

(* ================================================================== *)

Section DualSubLattices.

Context {T: choiceType} (L : {lattice T}) (S : subLattice L).

Lemma dual_stable: stable ([lattice of L^~]) S.
(*TODO : why [lattice of ] is mandatory*)
Proof.
apply/stableP; rewrite /= dual_meet dual_join; split.
- exact: mem_join.
- exact: mem_meet.
Qed.

Canonical DualSubLattice := SubLattice dual_stable. 

End DualSubLattices.

Notation "S '^~s'" := (DualSubLattice S) (at level 0).


(* =================================================================== *)

Section SubTBLatticesTheory.

Context {T: choiceType}.
Implicit Type (L: {tblattice T}).

Definition subtop L (S: subLattice L) := \big [join L/bottom L]_(i <- S) i.
Definition subbot L (S: subLattice L) := \big [meet L/top L]_(i <- S) i.

Lemma dual_subbot L (S: subLattice L) : subbot S^~s = subtop S.
Proof. by []. Qed.

Lemma dual_subtop L (S: subLattice L) : subtop S^~s = subbot S.
Proof. by []. Qed.

Lemma subtop_leE L (S : subLattice L) : forall x, x \in S -> x <=_L subtop S.
Proof.
move=> x /= x_in_S.
by rewrite /subtop (big_fsetD1 _ x_in_S) /= leEmeet joinKI.
Qed.

Lemma subbot_leE L (S : subLattice L): forall x, x \in S -> subbot S <=_L x.
Proof.
move=> x x_in_S; rewrite -dual_le -dual_subtop; exact: subtop_leE.
Qed.


Lemma subtop_stable L (S : subLattice L):
  S != fset0 :> {fset _ } -> subtop S \in S.
Proof.
case/fset0Pn=> x xS; rewrite /subtop (perm_big _ (perm_to_rem xS)).
rewrite big_cons; have /= := @mem_rem _ x (val S).
elim: (rem _ _) => [|y s ih] leS; first by rewrite big_nil joinx0.
rewrite big_cons joinCA; apply/mem_join/ih.
- by apply/leS; rewrite !inE eqxx.
- by move=> z z_in_s; apply/leS; rewrite !inE z_in_s orbT.
Qed.

Lemma subbot_stable L (S: subLattice L):
  S != fset0 :> {fset _} -> subbot S \in S.
Proof.
move=> Sprop0; rewrite -dual_subtop; exact: subtop_stable.
Qed.

Lemma subtop0E L (S : subLattice L):
  (S : {fset _}) == fset0 -> subtop S = bottom L.
Proof. by move/eqP; rewrite /subtop => ->; rewrite big_seq_fset0. Qed.

Lemma subbot0E L (S: subLattice L):
  (S : {fset _}) == fset0 -> subbot S = top L.
Proof. move=> ?; rewrite -dual_bot -dual_subtop; exact: subtop0E. Qed.

Lemma gtF_subtop L (S: subLattice L) x : x \in S -> subtop S <_L x = false.
Proof. by move=> xS; apply/negP => /lt_geF; rewrite subtop_leE. Qed.

Lemma ltF_subbot L (S: subLattice L) x : x \in S -> x <_L subbot S = false.
Proof. move=> ?; rewrite -dual_lt -dual_subtop; exact: gtF_subtop. Qed.

Lemma top_spec L (S: subLattice L) a : a \in S
  -> (forall x, x \in (S : {fset _}) -> x <=_L a)
  -> subtop S = a.
Proof.
move=> aS le_Sa; rewrite /subtop (perm_big _ (perm_to_rem aS)) /=.
by rewrite big_cons; apply/join_idPr/joinsP_seq => i /mem_rem /le_Sa.
Qed.

Lemma bot_spec L (S: subLattice L) a : a \in S
  -> (forall x, x \in (S : {fset _}) -> a <=_L x)
  -> subbot S = a.
Proof. move=> ? ?; rewrite -dual_subtop; exact: top_spec. Qed.



End SubTBLatticesTheory.

Notation "''top_' S" := (subtop S) (at level 8, S at level 2, format "''top_' S").
Notation "''bot_' S" := (subbot S) (at level 8, S at level 2, format "''bot_' S").

(* ==================================================================== *)
Section Atom.
Context {T : choiceType}.
Implicit Type (L : {tblattice T}).

Definition atom L (S : subLattice L) a := [&& a \in S, ('bot_S <_L a) &
  ~~[exists x : S, ('bot_S <_L val x) && (val x <_L a)]].

Definition coatom L (S : subLattice L) a := [&& a \in S, (a <_L 'top_S) &
  ~~[exists x : S, (val x <_L 'top_S) && (a <_L val x)]].

Lemma atomP L (S : subLattice L) a: reflect
  ([/\ a \in S, ('bot_S <_L a) &
  forall x, x \in S -> 'bot_S <_L x -> ~~(x <_L a)])
  (atom S a).
Proof.
apply/(iffP idP).
- case/and3P; rewrite !inE => /= a_in_S bot_lt_a /existsPn atomic.
  split => //; move=> y y_in_S bot_lt_y; move: (atomic [`y_in_S]%fset) => /=.
  by rewrite negb_and bot_lt_y /=.
- case; rewrite /atom => -> -> /= atomic; apply/existsPn.
  move=> x; rewrite negb_and -implybE; apply/implyP => ?.
  apply/atomic => //; exact: fsvalP. 
Qed.

Lemma dual_atom L (S : subLattice L) a : atom S^~s a = coatom S a.
Proof.
by rewrite /atom /coatom /= !inE dual_subbot.
Qed.

Lemma dual_coatom L (S : subLattice L) a : coatom S^~s a = atom S a.
Proof.
by rewrite /atom /coatom /= !inE dual_subtop.
Qed.

Lemma coatomP L (S : subLattice L) a: reflect
  ([/\ a \in S, (a <_L 'top_S) &
  forall x, x \in (S:{fset _}) -> x <_L 'top_S -> ~~(a <_L x)])
  (coatom S a).
Proof.
apply/(iffP idP); rewrite -dual_atom.
- by case/atomP => /=; rewrite !inE dual_subbot => -> -> atomic; split.
- case => ? ? ?; apply/atomP; split => //.
Qed.

End Atom.

(* ==================================================================== *)
Section SubLatticeInd.

Context {T : choiceType}.
Implicit Type (L:{tblattice T}).

Definition interval L (S : subLattice L) (a b : T) := 
  [fset x | x in S & (a <=_L x) && (x <=_L b)].

Lemma intervalE L (S : subLattice L) a b (x : T) :
  x \in interval S a b = (x \in S) && ((a <=_L x) && (x <=_L b)).
Proof. by rewrite /interval in_fsetE /= inE. Qed.

Lemma intervalP L (S : subLattice L) a b (x : T) :
  reflect
    [/\ x \in S, a <=_L x & x <=_L b]
    (x \in interval S a b).
Proof. by rewrite intervalE; apply/and3P. Qed.

Lemma in_intv_support L (S : subLattice L) (a b : T) x :
  x \in interval S a b -> x \in S.
Proof. by case/intervalP. Qed.

Lemma in_intv_range L (S : subLattice L) a b x:
  x \in interval S a b -> a <=_L x /\ x <=_L b.
Proof. by case/intervalP. Qed.

Lemma stable_interval L (S:subLattice L) a b: stable L (interval S a b).
Proof.
apply/stableP; split=> x y /intervalP[xS le_ax le_xb] /intervalP[yS le_ay le_yb].
- apply/intervalP; split; first by apply/mem_meet.
  - by rewrite lexI -(rwP andP). - by rewrite leIxl.
- apply/intervalP; split; first by apply/mem_join.
  - by rewrite lexUl. - by rewrite leUx -(rwP andP).
Qed.

Definition SubLatInterval L (S: subLattice L) a b :=
  SubLattice (stable_interval S a b).

Notation " [< a ; b >]_ S " := (@SubLatInterval _ S a b)
  (at level 0, S at level 8, format "[<  a ;  b  >]_ S").

Lemma in_intervalP L (S: subLattice L) a b x:
  reflect
   [/\ x \in S, a <=_L x & x <=_L b]
    (x \in [< a ; b >]_S).
Proof.
apply/(iffP idP).
- by rewrite in_fsetE unfold_in => /and3P [? ? ?].
- by case=> ? ? ?; rewrite in_fsetE unfold_in /=; apply/and3P.
Qed.

Lemma intv_id L (S: subLattice L) : [<'bot_S; 'top_S>]_S = S.
Proof.
apply/eqP/fset_eqP => x; apply/(sameP idP)/(iffP idP).
- by move=> x_in_S; rewrite inE /= unfold_in /=; apply/and3P; split;
    rewrite // ?subtop_leE ?subbot_leE.
- exact: in_intv_support.
Qed.

Lemma mono_interval L (S : subLattice L) (x y x' y' : T) :
  x'<=_L x -> y <=_L y' -> [< x; y >]_[< x'; y' >]_S = [< x; y >]_S.
Proof.
move=> lex ley; apply/val_eqP/eqP/fsetP => z /=.
apply/in_intervalP/in_intervalP; first by case=> /in_intv_support.
case=> zS le_xz le_zy; split=> //; apply/in_intervalP.
by split=> //; [apply: (le_trans lex) | apply: (le_trans le_zy)].
Qed.

Lemma sub_interval L: forall (S : subLattice L) a b c d,
  a \in (S : {fset _}) -> b \in (S : {fset _}) ->
  a <=_L b -> c <=_L d ->
  ([<a;b>]_S `<=` [<c;d>]_S)%fset <-> c <=_L a /\ b <=_L d.
Proof.
move=> S a b c d a_in_S b_in_S a_le_b c_le_d; split.
- move/fsubsetP => sub.
  have/in_intervalP[]: a \in ([<c;d>]_S : {fset _}) by
    apply/sub/in_intervalP; rewrite a_in_S lexx a_le_b.
  have/in_intervalP[]: b \in ([<c;d>]_S : {fset _}) by
    apply/sub/in_intervalP; rewrite b_in_S lexx a_le_b.
  done.
- case=> c_le_a b_le_d; apply/fsubsetP =>
    x /in_intervalP [x_in_S a_le_x x_le_b].
  apply/in_intervalP; rewrite x_in_S; split=> //;
    [exact:(le_trans c_le_a) | exact: (le_trans x_le_b)].
Qed.
    
Lemma inL_intv L (S : subLattice L) (x y : T) :
  x \in S -> x <=_L y -> x \in [< x; y >]_S.
Proof. by move=> ??; apply/in_intervalP; split=> //; rewrite lexx. Qed.

Lemma inR_intv L (S : subLattice L) (x y : T) :
  y \in S -> x <=_L y -> y \in [< x; y >]_S.
Proof. by move=> ??; apply/in_intervalP; split=> //; rewrite lexx. Qed.

Lemma in0L_intv L (S : subLattice L) (y : T) :
  y \in S -> 'bot_S \in [< 'bot_S; y >]_S.
Proof.
move=> nz_S; rewrite inL_intv // ?(subbot_stable, subbot_leE) //.
by apply/fset0Pn; exists y.
Qed.

Lemma in01R_intv L (S : subLattice L) (x : T) :
  x \in S -> 'top_S \in [< x; 'top_S >]_S.
Proof.
move=> nz_S; rewrite inR_intv // ?(subtop_stable, subtop_leE) //.
by apply/fset0Pn; exists x.
Qed.

Lemma intv0E L (S : subLattice L) (a b : T) :
  a \in S -> a <=_L b -> 'bot_[<a; b>]_S = a.
Proof.
by move=> aS le_ab; apply/bot_spec;
  [apply: inL_intv | move=> x /in_intervalP[]].
Qed.

Lemma intv1E L (S : subLattice L) (a b : T) :
  b \in (S : {fset _}) -> a <=_L b -> 'top_[<a; b>]_S = b.
Proof.
by move=> bS le_ab; apply/top_spec;
  [apply: inR_intv | move=> x /in_intervalP[]].
Qed.

Lemma dual_intv L (S: subLattice L) (a b: T):
  [<a; b>]_(S^~s) =i [<b; a>]_S.
Proof.
by move => x; rewrite !inE /= [X in _ && X]andbC.
Qed.

(*
(* -------------------------------------------------------------------- *)
Lemma atom_minset L (S:subLattice L) a b :
     a \in (S : {fset _}) -> b \in (S : {fset _}) -> a <=_L b
  -> atom [<a; b>]_S =i minset L ([<a; b>]_S `\ a).
Proof.
move=> aS bS le_ab x; apply/atomP/idP.
- case; rewrite intv0E // => x_ab lt_ax min_x.
  have in_x: x \in [< a; b >]_S `\ a.
  - by rewrite 2!in_fsetE x_ab andbT; apply/negbT/(gt_eqF lt_ax).
  apply/mem_minsetP => // y; rewrite 2!in_fsetE => /andP[ne_ya in_y].
  by apply: min_x => //; rewrite lt_neqAle ne_ya /=; case/in_intervalP: in_y.
- case/mem_minsetE; rewrite 2!in_fsetE => /andP[nz_xa in_x] min_x; split=> //.
  - by rewrite intv0E // lt_neqAle nz_xa /=; case/intervalP: in_x.
  - move=> y in_y; rewrite intv0E // => lt_ay; apply: min_x.
    by rewrite 2!in_fsetE in_y andbT (gt_eqF lt_ay).
Qed.

(* -------------------------------------------------------------------- *)
Lemma sub_atomic_top L (S : subLattice L) (x : T) :
  x \in S -> 'bot_S <_L x ->
    exists2 a, atom S a & ([< x ; subtop S>]_S `<=` ([< a; subtop S >]_S))%fset.
Proof.
move=> xS lt0x; have nz_S: S != fset0 :> {fset _} by apply/fset0Pn; exists x.
have [a]: exists y, atom [< 'bot_S; x >]_S y.
- have: minset L ([<'bot_S; x>]_S `\ 'bot_S) != fset0.
  - apply/minset_neq0/fset0Pn; exists x; rewrite in_fsetD1.
    by rewrite (gt_eqF lt0x) /= intervalE xS lexx ltW.
  case/fset0Pn=> a ha; exists a; rewrite -atom_minset // in ha *.
  - by apply: subbot_stable. - by apply: ltW.
case/atomP; rewrite intv0E ?(subbot_leE, subbot_stable) //.
case/in_intervalP=> aS le0a le_ax lt0a min_a; exists a; last first.
- by apply/sub_interval => //;  rewrite ?(subtop_leE, subtop_stable).
- apply/atomP; split=> // y yS lt0y; case/boolP: (_ <_L _) => //= lt_ya.
  have: y \in ([<subbot S; x>]_S : {fset _}).
  - apply/in_intervalP; split=> //; first by apply: subbot_leE.
    by apply/ltW/(lt_le_trans lt_ya).  
  by move/min_a => /(_ lt0y) /negbTE <-.
Qed.
*)

Lemma sub_atomic L (S: subLattice L) x:
  x \in S -> 'bot_S <_L x ->
  exists y, atom S y /\ y <=_L x.
Proof.
set S' := ([< 'bot_S; x >]_S `\` [fset 'bot_S; x])%fset.
move=> x_in_S bot_lt_x.
case/boolP: (S' == fset0).
- rewrite fsetD_eq0 => /fsubsetP intv_sub.
  exists x; split; rewrite ?lexx //.
  apply/atomP; split => // y y_in_S; apply: contraTN => y_lt_x.
  rewrite lt_neqAle (subbot_leE y_in_S) andbT negbK.
  have/intv_sub: (y \in [<'bot_S; x>]_S) by
    apply/in_intervalP; split; [by []| exact: subbot_leE |exact:ltW].
  by rewrite !inE (lt_eqF y_lt_x) orbF.
- case/(minset_neq0 L)/fset0Pn => y /mem_minsetE.
  rewrite !inE negb_or.
  case => /and4P [/andP [yNbot y_neq_x] y_in_S bot_le_y y_le_x mini_y].
  exists y; split => //; apply/atomP; split => //.
    by rewrite lt_neqAle yNbot bot_le_y.
  move=> x0 x0_in_S bot_lt_x0; apply: contraT; rewrite negbK => x0_lt_y.
  have/mini_y: x0 \in S'.
    rewrite !inE x0_in_S eq_sym (lt_eqF bot_lt_x0) (ltW bot_lt_x0) /=.
    rewrite -ostrict; exact: (lt_le_trans x0_lt_y).
  by rewrite x0_lt_y.
Qed.

Lemma sub_coatomic L (S: subLattice L) x:
  x \in S -> x <_L 'top_S -> exists y, coatom S y /\ x <=_L y.
Proof.
move=> x_in_S; have x_in_Ss : x \in S^~s by [].
rewrite -dual_lt -dual_subbot; case/(sub_atomic x_in_Ss) => y.
by rewrite dual_atom; case => coatom_y /= x_le_y; exists y.
Qed.


(* -------------------------------------------------------------------- *)
Section IndIncr.
Context (L : {tblattice T}).
Variable (P : subLattice L -> Prop).

Hypothesis (P_incr : forall S, forall x,
  atom S x -> P S -> P [<x; 'top_S>]_S).

Lemma ind_incr (S : subLattice L) (x : T) :
  x \in S -> P S -> P [<x; 'top_S>]_S.
Proof.
move=> xS PS; move: {2}#|`_| (leqnn #|`[< 'bot_S; x >]_S|) => n.
elim: n S xS PS => [|n ih] S xS PS.
- rewrite leqn0 => /eqP /cardfs0_eq /(congr1 (fun S => x \in S)).
  rewrite in_fset0 => /in_intervalP; case; split=> //.
  - by rewrite subbot_leE. - by rewrite lexx.
case/boolP: (atom S x) => [atom_Sx|atomN_Sx]; first by move=> _; apply: P_incr.
case: (x =P 'bot_S) => [-> _|/eqP neq0_x]; first by rewrite intv_id.
have bot_lt_x: 'bot_S <_L x by rewrite ostrict eq_sym neq0_x (subbot_leE xS).
move=> sz; case: (sub_atomic xS bot_lt_x) => y [atom_Sy y_le_x].
have yS: y \in S by case/atomP: atom_Sy.
have nz_S: S != fset0 :> {fset _} by apply/fset0Pn; exists x.
have ne_xy: x != y by apply: contraNneq atomN_Sx => ->.
have: x \in ([< y; 'top_S >]_S : {fset _}).
- by apply/in_intervalP; rewrite xS y_le_x subtop_leE.
move/ih => /(_ (P_incr atom_Sy PS)).
rewrite !(intv0E, intv1E) 1?(subtop_stable, subtop_leE) //.
rewrite !mono_interval ?(lexx, subtop_leE) //.
apply; rewrite -ltnS; pose X := 'bot_S |` [< 'bot_S; x >]_S `\ 'bot_S.
apply: (@leq_trans #|`X|); last by rewrite /X fsetD1K // in0L_intv.
apply: fproper_ltn_card; rewrite {}/X.
rewrite fsetD1K ?in0L_intv //.
apply: (@fsub_proper_trans _ ([< 'bot_S; x >]_S `\ 'bot_S)); last first.
- by apply/fproperD1; rewrite in0L_intv.
apply/fsubsetD1P; split.
- by apply/sub_interval; rewrite ?(subbot_leE, lexx) //; apply/ltW.
apply: contraL atom_Sy => /in_intervalP[_].
rewrite le_eqVlt ltF_subbot // orbF => /eqP-> _.
by apply/negP => /atomP; rewrite ltxx; case.
Qed.
End IndIncr.

(* -------------------------------------------------------------------- *)
Section IndDecr.
Context (L : {tblattice T}).
Variable (P : subLattice L -> Prop).

Hypothesis (P_decr : forall S, forall x,
  coatom S x -> P S -> P [<'bot_S; x>]_S).

Definition mirror := (fun r : rel nat => fun (x y : nat) => r y x).

Lemma ind_decr (S : subLattice L) (x : T) :
  x \in S -> P S -> P [<'bot_S; x>]_S.
Proof.
move=> x_in_S PS.
have f: rel nat by admit.
have : (mirror (mirror f)) = f.
reflexivity. 
Admitted.
(* From ind_incr, using the dual ordering *)
End IndDecr.

(* -------------------------------------------------------------------- *)
Section Ind.
Context (L : {tblattice T}).
Variable (P : subLattice L -> Prop).

Hypothesis (P_incr : forall (S: subLattice L), forall x,
  atom S x -> P S -> P [<x; 'top_S>]_S).
Hypothesis (P_decr : forall (S:subLattice L), forall x,
  coatom S x -> P S -> P [<'bot_S; x>]_S).

Lemma ind_id (S : subLattice L) (x y : T) :
  x \in S -> y \in S -> x <=_L y -> P S -> P [<x; y>]_S.
Proof.
move=> xS yS le_xy PS; have h: P [< x; 'top_S >]_S by apply: ind_incr.
suff: P [< 'bot_[< x; 'top_S >]_S; y >]_[< x; 'top_S >]_S.
- by rewrite intv0E ?subtop_leE // mono_interval // (lexx, subtop_leE).
apply: ind_decr => //; apply/in_intervalP; split=> //.
by rewrite subtop_leE.
Qed.
End Ind.

End SubLatticeInd.

(* ==================================================================== *)
Module GradedLattice.
Section ClassDef.
Context {T: eqType}.

Record class (L : {tblattice T}) := Class {
  rank : T -> nat;
  _ : rank (bottom L) = O%N;
  _ : forall x y, x <_L y -> (rank x < rank y)%N;
  _ : forall x y, x <=_L y -> ((rank x).+1 < rank y)%N -> exists z, (x <_L z) && (z <_L y)
}.

Structure pack (phr : phant (rel T)) := Pack {
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

(* ==================================================================== *)
Section GLatticeTheory.
Variable (T : finType) (L : {glattice T}).

Lemma rk_bottom : rank L (bottom L) = 0%N.
Proof. by case: L => ? []. Qed.

Lemma rk_increasing : forall x y, x <_L y -> (rank L x < rank L y)%N.
Proof. by case: L => ? []. Qed.

Lemma rk_dense : forall x y,
  x <=_L y -> ((rank L x).+1 < rank L y)%N -> exists z, (x <_L z) && (z <_L y).
Proof.
by case: L => ? [].
Qed.
End GLatticeTheory.

(*==================================================================== *)
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