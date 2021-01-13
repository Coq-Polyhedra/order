From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import xbigop extra_misc relorder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope fset_scope.
Local Open Scope ring_scope.

Import RelOrder.
Import RelOrder.Theory.

Module PreLattice.
Section ClassDef.

Context {T : choiceType}.

Set Primitive Projections.

Record class (r : {pOrder T}) := Class
{
  witness : T;
  premeet : {fset T} -> T -> T -> T;
  prejoin : {fset T} -> T -> T -> T;
  premeet_min : forall S x y, x \in S -> y \in S ->
    premeet S x y <=_r x /\ premeet S x y <=_r y;
  premeet_inf : forall S x y z, x \in S -> y \in S -> z \in S ->
    z <=_r x -> z <=_r y ->
    z <=_r premeet S x y;
  premeet_incr : forall S S' x y, S `<=` S' -> x \in S -> y \in S ->
    premeet S x y <=_r premeet S' x y;
  prejoin_max : forall S x y, x \in S -> y \in S ->
    prejoin S x y <=_(r^~) x /\ prejoin S x y <=_(r^~) y;
  prejoin_sup : forall S x y z, x \in S -> y \in S -> z \in S ->
    z <=_(r^~) x -> z <=_(r^~) y ->
    z <=_(r^~) prejoin S x y;
  prejoin_decr : forall S S' x y, S `<=` S' -> x \in S -> y \in S ->
    prejoin S x y <=_(r^~) prejoin S' x y
}.

Structure pack (phr : phant T) := Pack
{
  pack_order : {pOrder T};
  pack_class : class pack_order
}.

Unset Primitive Projections.

Local Coercion pack_order : pack >-> POrder.order.

Variable (phr : phant T) (m : pack phr).

Definition order_of := POrder.Pack phr (POrder.class_ m).
Definition clone (r : {pOrder T}) :=
  fun (pl : pack phr) & phant_id (pack_order pl) r =>
  pl.

End ClassDef.


(* ---------------------------------------------------------------------- *)

Module Exports.

Canonical order_of.
Coercion pack_order : pack >-> POrder.order.
Coercion pack_class : pack >-> class.
Notation "{ 'preLattice' T }" := (pack (Phant T))
  (at level 0, format "{ 'preLattice'  T }").
Notation "[ 'preLattice' 'of' r ]" := (@clone _ (Phant _) r _ id)
  (at level 0, format "[ 'preLattice'  'of'  r ]").
Notation premeet := premeet.
Notation prejoin := prejoin.



End Exports.

End PreLattice.
Include PreLattice.Exports.

Section DualPreLattice.

Context {T: choiceType}.
Variable (L : {preLattice T}).

Definition DualPreLatticeClass := PreLattice.Class
    (PreLattice.witness L)
    (PreLattice.prejoin_max L) (PreLattice.prejoin_sup L)
    (PreLattice.prejoin_decr L)
    (PreLattice.premeet_min L) (PreLattice.premeet_inf L)
    (PreLattice.premeet_incr L).

Canonical DualPreLatticePack :=
  PreLattice.Pack (Phant T) DualPreLatticeClass.

End DualPreLattice.

(*Section PreLatticeDualTest.

Context (T: choiceType) (L : {preLattice T}).
Check erefl L : [preLattice of L^~^~] = L.
End PreLatticeDualTest.*)

Section PreLatticeTheory.

Context {T: choiceType}.
Implicit Type L: {preLattice T}.

Lemma premeet_min L S:
  {in S &, forall x y, premeet L S x y <=_L x /\ premeet L S x y <=_L y}.
Proof. exact: PreLattice.premeet_min. Qed.

Lemma premeet_minl L S:
  {in S &, forall x y, premeet L S x y <=_L x}.
Proof. by move=> x y xS yS; case: (premeet_min L xS yS). Qed.

Lemma premeet_minr L S:
  {in S &, forall x y, premeet L S x y <=_L y}.
Proof. by move=> x y xS yS; case: (premeet_min L xS yS). Qed.

Lemma premeet_inf L S:
  {in S & &, forall x y z, z <=_L x -> z <=_L y -> z <=_L premeet L S x y}.
Proof. exact: PreLattice.premeet_inf. Qed.

Lemma premeet_incr L S S': S `<=` S' ->
  {in S &, forall x y, premeet L S x y <=_L premeet L S' x y}.
Proof. move=> ?????; exact: PreLattice.premeet_incr. Qed.

Lemma prejoin_max L S:
  {in S &, forall x y, prejoin L S x y <=_(L^~) x /\ prejoin L S x y <=_(L^~) y}.
Proof. exact: PreLattice.prejoin_max. Qed.

Lemma prejoin_maxl L S:
  {in S &, forall x y, prejoin L S x y <=_(L^~) x}.
Proof. by move=> x y xS yS; case: (prejoin_max L xS yS). Qed.

Lemma prejoin_maxr L S:
  {in S &, forall x y, prejoin L S x y <=_(L^~) y}.
Proof. by move=> x y xS yS; case: (prejoin_max L xS yS). Qed.

Lemma prejoin_sup L S:
  {in S & &, forall x y z, z <=_(L^~) x -> z <=_(L^~) y -> z <=_(L^~) prejoin L S x y}.
Proof. exact: PreLattice.prejoin_sup. Qed.

Lemma prejoin_decr L S S': S `<=` S' ->
  {in S &, forall x y, prejoin L S x y <=_(L^~) prejoin L S' x y}.
Proof. move=> ?????; exact: PreLattice.prejoin_decr. Qed.

Lemma dual_premeet L S x y:
  premeet [preLattice of L^~] S x y = prejoin L S x y.
Proof. by []. Qed.

Lemma dual_prejoin L S x y:
  prejoin [preLattice of L^~] S x y = premeet L S x y.
Proof. by []. Qed.

End PreLatticeTheory.

(* ================================================================== *)

Section MeetToPreLattice.

Context {T: choiceType} (M : {tMeetOrder T}).
Definition Mmeet (S: {fset T}) := meet M.
Definition Mjoin (S:{fset T}) x y :=
  \big[ (meet M) / (top M) ]_(i <- S | (x <=_M i) && (y <=_M i)) i.

Lemma Mmeet_min S x y : x \in S -> y \in S ->
  Mmeet S x y <=_M x /\ Mmeet S x y <=_M y.
Proof. by move=> xS yS; rewrite leIl leIr. Qed.

Lemma Mmeet_inf S x y z :
  x \in S -> y \in S -> z \in S ->
  z <=_M x -> z <=_M y ->
  z <=_M Mmeet S x y.
Proof. by move=> xS yS zS; rewrite lexI => -> ->. Qed.

Lemma Mmeet_incr S S' x y :
  S `<=` S' -> x \in S -> y \in S ->
  Mmeet S x y <=_M Mmeet S' x y.
Proof. by []. Qed.

Lemma Mjoin_max S x y :
  x \in S -> y \in S ->
  Mjoin S x y <=_(M^~) x /\ Mjoin S x y <=_(M^~) y.
Proof. by move=> xS yS; split; apply/meetsP_seq => ?? /andP []. Qed.

Lemma Mjoin_sup S x y z :
  x \in S -> y \in S -> z \in S ->
  z <=_(M^~) x -> z <=_(M^~) y ->
  z <=_(M^~) Mjoin S x y.
Proof. by move=> xS yS zS xlez ylez; apply: meet_inf_seq => //; apply/andP. Qed.

Lemma Mjoin_decr S S' x y :
  S `<=` S' -> x \in S -> y \in S ->
  Mjoin S x y <=_(M^~) Mjoin S' x y.
Proof.
move=> /fsubsetP Ssub xS yS; apply/meetsP_seq => z zS /andP [xlez ylez].
apply: meet_inf_seq; rewrite ?xlez ?ylez //.
exact: Ssub.
Qed.

Definition MeetPreLatticeClass := PreLattice.Class
  (top M) (Mmeet_min) (Mmeet_inf) (Mmeet_incr)
  (Mjoin_max) (Mjoin_sup) (Mjoin_decr).

Canonical MeetPreLatticePack :=
  PreLattice.Pack (Phant T) MeetPreLatticeClass.

End MeetToPreLattice.

Section JoinToPreLattice.

Context {T: choiceType} (J : {bJoinOrder T}).

Canonical JoinPreLatticePack :=
  PreLattice.Pack (Phant T) (MeetPreLatticeClass [tMeetOrder of (<=:(J^~))]).

End JoinToPreLattice.

Section FinLattice.

Context {T : choiceType}.

Definition stable (L: {preLattice T}) (S : {fset T}) :=
  [forall x : S, [forall y : S, premeet L S (fsval x) (fsval y) \in S]].

Lemma stableP (L: {preLattice T}) (S : {fset T}) :
  reflect (forall x y, x \in S -> y \in S ->
    premeet L S x y \in S)
    (stable L S).
Proof.
apply/(iffP idP).
- by move => + x y xS yS; move/forallP/(_ [`xS])/forallP/(_ [`yS]).
- move=> stableH; apply/forallP => x; apply/forallP => y.
  apply: stableH; exact: fsvalP.
Qed.

Variable (L: {preLattice T}).

Record finLattice :=
  FinLattice { elements :> {fset T};
  _ : stable L elements && stable ([preLattice of L^~]) elements }.

Canonical finLattice_subType := Eval hnf in [subType for elements].

Definition finLattice_eqMixin := Eval hnf in [eqMixin of finLattice by <:].
Canonical  finLattice_eqType  := Eval hnf in EqType finLattice finLattice_eqMixin.

Definition finLattice_choiceMixin := [choiceMixin of finLattice by <:].
Canonical  finLattice_choiceType  :=
  Eval hnf in ChoiceType finLattice finLattice_choiceMixin.

(*TODO : finType*)

Coercion mem_finLattice (S: finLattice) : {pred T} :=
  fun x : T => (x \in (elements S)).
Canonical finLattice_predType := PredType mem_finLattice.

Lemma in_finLatticeE (S: finLattice) x : (x \in S) = (x \in elements S).
Proof. by []. Qed.

Definition inE := (in_finLatticeE, inE).

Definition fmeet (S: finLattice) := premeet L S.
Definition fjoin (S: finLattice) := prejoin L S.

End FinLattice.

Notation "{ 'finLattice' L }" := (finLattice L) (at level 0, format "{ 'finLattice'  L }").
Notation "'\fmeet_' S" := (@fmeet _ _ S) (at level 8, format "'\fmeet_' S").
Notation "'\fjoin_' S" := (@fjoin _ _ S) (at level 8, format "'\fjoin_' S").

Section FinLatticeDual.

Context {T : choiceType} (L : {preLattice T}) (S : {finLattice L}).

Lemma stableDual : (stable [preLattice of L^~] S) && (stable L S).
Proof. by case: S => S0 stableS0; rewrite andbC. Defined.

Canonical FinLatticeDual := FinLattice stableDual.

(*Variable (x : T).
Check (x \in FinLatticeDual).
Check (FinLatticeDual).*)

Lemma dual_fjoinE:
  \fjoin_(FinLatticeDual)= \fmeet_S.
Proof. by []. Qed.

Lemma dual_fmeetE: \fmeet_(FinLatticeDual) = \fjoin_S.
Proof. by []. Qed.

End FinLatticeDual.

Notation "S ^~s" := (FinLatticeDual S)
  (at level 8, format "S ^~s").

Section FinLatticeDualTest.

Context {T : choiceType} (L : {preLattice T}) (S : {finLattice L}).
Goal ((S^~s)^~s) = S.
Proof. by apply/val_inj. Qed.

End FinLatticeDualTest.

Section FinLatticeStructure.

Context {T : choiceType}.
Lemma stable_fun (L : {preLattice T}) (S : {finLattice L}) (x y : S) :
  (\fmeet_S (fsval x) (fsval y) \in S).
Proof.
rewrite /fmeet inE; move: S x y; case => /= S + x y.
by case/andP => /stableP /(_ _ _ (fsvalP x) (fsvalP y)).
Qed.

Context (L : {preLattice T}) (S : {finLattice L}).

Definition Sle : rel S := fun x y => (fsval x) <=_L (fsval y).
Definition Slt : rel S := fun x y => (fsval x) <_L (fsval y).

Lemma Slexx : reflexive Sle.
Proof. by move=> x; rewrite /Sle. Qed.

Lemma Sle_anti : forall (x y : S), Sle x y -> Sle y x -> x = y.
Proof.
move=> x y; rewrite /Sle => le1 le2; apply/val_inj/(@le_anti _ L).
by rewrite le1 le2.
Qed.

Lemma Sle_trans : transitive Sle.
Proof. move=> y x z; rewrite /Sle; exact: le_trans. Qed.

Lemma Slt_def : forall (x y : S), Slt x y = (x != y) && Sle x y.
Proof. move=> x y; rewrite /Slt /Sle lt_def; congr (_ && _). Qed.

Lemma dSlt_def : forall (x y : S), Slt y x = (x != y) && Sle y x.
Proof. move=> x y; rewrite /Slt /Sle lt_def eq_sym; congr (_ && _). Qed.

Definition Sle_mixin :=
  POrder.Mixin Slexx Sle_anti Sle_trans Slt_def dSlt_def.


Definition Smeet : S -> S -> S := fun x y : S => [`stable_fun x y].
Definition Sjoin : S -> S -> S := fun x y : S => [` @stable_fun _ S^~s x y].


Lemma SmeetC : commutative Smeet.
Proof.
move=> x y; apply/val_inj/(@le_anti _ L).
by rewrite !premeet_inf // ?premeet_minl ?premeet_minr ?fsvalP.
Qed.

Lemma SmeetAl : forall (x y z t : S), t \in [fset x; y; z] ->
  val (Smeet x (Smeet y z)) <=_L val t.
Proof.
move=> x y z t; rewrite !in_fsetE; case/orP => [/orP []|] /eqP ->  /=.
+ by rewrite premeet_minl ?fsvalP ?stable_fun.
+ apply:(le_trans _ (premeet_minl L (fsvalP y) (fsvalP z))).
  by rewrite premeet_minr ?fsvalP ?stable_fun.
+ apply:(le_trans _ (premeet_minr L (fsvalP y) (fsvalP z))).
  by rewrite premeet_minr ?fsvalP ?stable_fun.
Qed.

Lemma SmeetAr : forall (x y z t : S), t \in [fset x; y; z] ->
  val (Smeet (Smeet x y) z) <=_L val t.
Proof.
move=> x y z t; rewrite !in_fsetE; case/orP => [/orP []|] /eqP -> /=.
+ apply:(le_trans _ (premeet_minl L (fsvalP x) (fsvalP y))).
  by rewrite premeet_minl ?fsvalP ?stable_fun.
+ apply:(le_trans _ (premeet_minr L (fsvalP x) (fsvalP y))).
  by rewrite premeet_minl ?fsvalP ?stable_fun.
+ by rewrite premeet_minr ?fsvalP ?stable_fun.
Qed.

Lemma SmeetA : associative Smeet.
Proof.
move=> x y z; apply/val_inj/(@le_anti _ L).
by rewrite !premeet_inf ?fsvalP ?SmeetAl ?SmeetAr //
  !in_fsetE eq_refl ?orbT.
Qed.

Lemma leSmeet : forall x y : S, Sle x y = (Smeet x y == x).
Proof.
move=> x y; apply/(sameP idP)/(iffP idP).
- by move/eqP => <-; rewrite /Sle premeet_minr ?fsvalP.
- rewrite /Sle => xley; apply/eqP/val_inj/(@le_anti _ L).
  by rewrite premeet_minl ?premeet_inf ?fsvalP.
Qed.

Definition Smeet_mixin := Meet.Mixin SmeetC SmeetA leSmeet.
Definition Smeet_class := Meet.Class Sle_mixin Smeet_mixin.

Lemma SjoinC : commutative Sjoin.
Proof.
move=> x y; apply/val_inj/(@le_anti _ L^~)=> /=.
by rewrite !prejoin_sup ?prejoin_maxl ?prejoin_maxr ?stable_fun ?fsvalP.
Qed.

Lemma SjoinAl : forall (x y z t : S), t \in [fset x; y; z] ->
  val (Sjoin x (Sjoin y z)) <=_(L^~) val t.
Proof.
move=> x y z t; rewrite !in_fsetE; case/orP => [/orP []|] /eqP ->.
- by rewrite prejoin_maxl ?fsvalP.
- apply:(le_trans _ (prejoin_maxl L (fsvalP y) (fsvalP z))).
  by rewrite prejoin_maxr ?fsvalP.
- apply:(le_trans _ (prejoin_maxr L (fsvalP y) (fsvalP z))).
  by rewrite prejoin_maxr ?fsvalP.
Qed.

Lemma SjoinAr : forall (x y z t : S), t \in [fset x; y; z] ->
  val (Sjoin (Sjoin x y) z) <=_(L^~) val t.
Proof.
move=> x y z t; rewrite !in_fsetE; case/orP => [/orP []|] /eqP ->.
- apply: (le_trans _ (prejoin_maxl L (fsvalP x) (fsvalP y))).
  by rewrite prejoin_maxl ?fsvalP.
- apply: (le_trans _ (prejoin_maxr L (fsvalP x) (fsvalP y))).
  by rewrite prejoin_maxl ?fsvalP.
- by rewrite prejoin_maxr ?fsvalP.
Qed.

Lemma SjoinA : associative Sjoin.
Proof.
move=> x y z; apply/val_inj/(@le_anti _ L^~).
by rewrite !prejoin_sup ?fsvalP ?SjoinAl ?SjoinAr //
  !in_fsetE eq_refl ?orbT.
Qed.

Lemma leSjoin : forall x y : S, dual_rel Sle x y = (Sjoin x y == x).
Proof.
move=> x y; apply/(sameP idP)/(iffP idP).
- move/eqP => <-; rewrite /Sle /dual_rel.
  exact:(prejoin_maxr L (fsvalP x) (fsvalP y)).
- rewrite /dual_rel /Sle => ylex; apply/eqP/val_inj/(@le_anti _ L^~).
  by rewrite prejoin_maxl ?prejoin_sup ?fsvalP.
Qed.

Definition Sjoin_mixin := Meet.Mixin SjoinC SjoinA leSjoin.
Definition SLattice_class := Lattice.Class Smeet_class Sjoin_mixin.
Canonical SLattice_pack := Lattice.Pack (Phant _) SLattice_class.


End FinLatticeStructure.

Coercion SLattice_pack : finLattice >-> Lattice.order.

(* ========================================================================= *)

Section FinLatticeTheory.

Context {T: choiceType}.
Implicit Type L : {preLattice T}.

Lemma foo1 (K : {fset T}) (P : T -> Prop) :
  (forall x : K, P (fsval x)) -> {in K, forall x, P x}.
Proof. move=> Pval x xK; exact: (Pval [`xK]). Qed.

Lemma foo2 (K : {fset T}) (P : T -> T -> Prop) :
  (forall x y : K, P (fsval x) (fsval y)) -> {in K &, forall x y, P x y}.
Proof. move=> Pval x y xS yS; exact: (Pval [`xS] [`yS]). Qed.

Lemma foo3 (K : {fset T}) (P : T -> T -> T -> Prop) :
  (forall x y z: K, P (fsval x) (fsval y) (fsval z)) ->
  {in K & &, forall x y z, P x y z}.
Proof. move=> Pval x y z xS yS zS; exact: (Pval [`xS] [`yS] [`zS]). Qed.



Lemma mem_fjoin L (S: {finLattice L}): {in S &, forall x y, \fjoin_S x y \in S}.
Proof.
move=> x y; rewrite !inE /fjoin /=; case: S => /= elts + xS yS.
by case/andP => _ /stableP/(_ x y xS yS).
Qed.

Lemma mem_fmeet L (S : {finLattice L}) : {in S &, forall x y, \fmeet_S x y \in S}.
Proof. exact: (@mem_fjoin _ S^~s). Qed.

Lemma leIfl L (S : {finLattice L}) : {in S &, forall x y, \fmeet_S x y <=_L x}.
Proof. apply: foo2; exact: (@leIl _ S). Qed.


Lemma leIfr L (S : {finLattice L}) : {in S &, forall x y, \fmeet_S y x <=_L x}.
Proof. apply: foo2; exact: (@leIr _ S). Qed.

Lemma lefI L (S : {finLattice L}) :
  {in S & &, forall x y z, (x <=_L \fmeet_S y z) = (x <=_L y) && (x <=_L z)}.
Proof. apply: foo3; exact (@lexI _ S). Qed.

Lemma fmeetC L (S : {finLattice L}) : {in S &, commutative (\fmeet_S)}.
Proof. 
apply: foo2=> x y; move: (@meetC _ S x y).
exact: (@congr1 _ _ (@fsval _ S)).
Qed.

Lemma lefIl L (S : {finLattice L}) :
  {in S & &, forall x y z, y <=_L x -> \fmeet_S y z <=_L x}.
Proof. apply: foo3; exact: (@leIxl _ S). Qed.

Lemma lefIr L (S : {finLattice L}) :
  {in S & &, forall x y z, z <=_L x -> \fmeet_S y z <=_L x}.
Proof. move=> x y z xS yS zS zlex; rewrite fmeetC //; exact: lefIl. Qed.

Lemma fmeetA L (S : {finLattice L}) : {in S & &, associative (\fmeet_S) }.
Proof.
apply: foo3=> x y z; move:(@meetA _ S x y z).
exact: (@congr1 _ _ (@fsval _ S)).
Qed.

Lemma fmeetxx L (S : {finLattice L}) : {in S, idempotent (\fmeet_S)}.
Proof.
apply: foo1=> x; move:(@meetxx _ S x).
exact: (@congr1 _ _ (@fsval _ S)).
Qed.

Lemma leEfmeet L (S : {finLattice L}) :
  {in S &, forall x y, (x <=_L y) = (\fmeet_S x y == x)}.
Proof. apply: foo2; exact:(@leEmeet _ S). Qed.

Lemma fmeetAC L (S : {finLattice L}) :
  {in S & &, right_commutative (\fmeet_S)}.
Proof. 
apply: foo3=> x y z; move:(@meetAC _ S x y z).
exact: (@congr1 _ _ (@fsval _ S)).
Qed.

Lemma fmeetCA L (S : {finLattice L}) :
  {in S & &, left_commutative (\fmeet_S)}.
Proof.
apply: foo3=> x y z; move:(@meetCA _ S x y z).
exact: (@congr1 _ _ (@fsval _ S)).
Qed.


Lemma fmeetACA L (S : {finLattice L}) x y z t:
  x \in S -> y \in S -> z \in S -> t \in S ->
  \fmeet_S (\fmeet_S x y) (\fmeet_S z t) =
  \fmeet_S (\fmeet_S x z) (\fmeet_S y t).
Proof.
move=> xS yS zS tS; move:(@meetACA _ S [`xS] [`yS] [`zS] [`tS]).
exact: (@congr1 _ _ (@fsval _ S)).
Qed.

Lemma fmeetKI L (S : {finLattice L}) :
  {in S &, forall x y, \fmeet_S x (\fmeet_S x y) = \fmeet_S x y}.
Proof. by move=> x y xS yS; rewrite fmeetA ?fmeetxx. Qed.

Lemma fmeetIK L (S : {finLattice L}) :
  {in S &, forall x y, \fmeet_S (\fmeet_S x y) y = \fmeet_S x y}.
Proof. by move=> x y xS yS; rewrite -fmeetA ?fmeetxx. Qed.

Lemma fmeetKIC L (S : {finLattice L}) :
  {in S &, forall x y, \fmeet_S x (\fmeet_S y x) = \fmeet_S x y}.
Proof. by move=> ? ? ? ?; rewrite fmeetC ?mem_fmeet ?fmeetIK // fmeetC. Qed.

Lemma fmeetIKC L (S : {finLattice L}) :
  {in S &, forall x y, \fmeet_S (\fmeet_S y x) y = \fmeet_S x y}.
Proof. by move=> ? ? ? ?; rewrite fmeetC ?mem_fmeet ?fmeetKI // fmeetC. Qed.

Lemma leIf2 L (S : {finLattice L}) :
  {in S & &, forall x y z, (y <=_L x) || (z <=_L x) ->
  \fmeet_S y z <=_L x}.
Proof.
move=> x y z xS yS zS /orP [ylex | zlex]; [exact: lefIl | exact: lefIr].
Qed.


Lemma fmeet_idPl L (S : {finLattice L}) {x y} : x \in S -> y \in S ->
  reflect (\fmeet_S x y = x) (x <=_L y).
Proof. move=> xS yS; rewrite (leEfmeet xS yS) //; exact: eqP. Qed.

Lemma fmeet_idPr L (S : {finLattice L}) {x y} : x \in S -> y \in S ->
  reflect (\fmeet_S y x = x) (x <=_L y).
Proof. by move=> xS yS; rewrite fmeetC //; apply/fmeet_idPl. Qed.

Lemma fmeet_l L (S : {finLattice L}) :
  {in S &, forall x y, x <=_L y -> \fmeet_S x y = x}.
Proof. move=> x y xS yS; exact/fmeet_idPl. Qed.

Lemma fmeet_r L (S : {finLattice L}) :
  {in S &, forall x y, y <=_L x -> \fmeet_S x y = y}.
Proof. move=> x y xS yS; exact/fmeet_idPr. Qed.

Lemma lefIidl L (S : {finLattice L}) :
  {in S &, forall x y, (x <=_L \fmeet_S x y) = (x <=_L y)}.
Proof. by move=> x y xS yS; rewrite !(leEfmeet xS) ?mem_fmeet ?fmeetKI. Qed.

Lemma lefIidr L (S : {finLattice L}) :
  {in S &, forall x y, (x <=_L \fmeet_S y x) = (x <=_L y)}.
Proof. by move=> x y xS yS; rewrite !(leEfmeet xS) ?mem_fmeet ?fmeetKIC. Qed.

Lemma eq_fmeetl L (S : {finLattice L}) :
  {in S &, forall x y, (\fmeet_S x y == x) = (x <=_L y)}.
Proof. by move=> ????; apply/esym/leEfmeet. Qed.

Lemma eq_fmeetr L (S: {finLattice L}) :
  {in S &, forall x y, (\fmeet_S x y == y) = (y <=_L x)}.
Proof. by move=> ????; rewrite fmeetC ?eq_fmeetl. Qed.

Lemma lefI2 L (S : {finLattice L}) x y z t :
  x \in S -> y \in S -> z \in S -> t \in S ->
  x <=_L z -> y <=_L t -> \fmeet_S x y <=_L \fmeet_S z t.
Proof. move=> xS yS zS tS; exact:(@leI2 _ S [`xS] [`yS] [`zS] [`tS]). Qed.

(* -------------------------------------------------------------------- *)

Lemma fjoinC L (S : {finLattice L}) : {in S &, commutative (\fjoin_S)}.
Proof. exact: (@fmeetC _ S^~s). Qed.

Lemma lefUr L (S: {finLattice L}) : {in S &, forall x y, x <=_L \fjoin_S y x}.
Proof.
move=> ????; exact: (@leIfr _ S^~s).
Qed.

Lemma lefUl L (S : {finLattice L}) : {in S &, forall x y, x <=_L \fjoin_S x y}.
Proof.
move=> ????; exact: (@leIfl _ S^~s).
Qed.

Lemma leUf L (S : {finLattice L}) : {in S & &, forall x y z,
  (\fjoin_S y z <=_L x) = (y <=_L x) && (z <=_L x)}.
Proof.
move=> ????; exact: (@lefI _ S^~s).
Qed.

Lemma fjoinA L (S : {finLattice L}) : {in S & &, associative (\fjoin_S)}.
Proof. exact: (@fmeetA _ S^~s). Qed.

Lemma fjoinxx L (S : {finLattice L}) : {in S, idempotent (\fjoin_S)}.
Proof. exact: (@fmeetxx _ S^~s). Qed.

Lemma leEfjoin L (S : {finLattice L}) :
  {in S &, forall x y, (x <=_L y) = (\fjoin_S y x == y)}.
Proof.
move=> ????; exact: (@leEfmeet _ S^~s).
Qed.

Lemma fjoinAC L (S : {finLattice L}) :
  {in S & &, right_commutative (\fjoin_S)}.
Proof. exact: (@fmeetAC _ S^~s). Qed.

Lemma fjoinCA L (S : {finLattice L}) :
  {in S & &, left_commutative (\fjoin_S)}.
Proof. exact: (@fmeetCA _ S^~s). Qed.

Lemma fjoinACA L (S : {finLattice L}) x y z t :
  x \in S -> y \in S -> z \in S -> t \in S ->
  \fjoin_S (\fjoin_S x y) (\fjoin_S z t) =
  \fjoin_S (\fjoin_S x z) (\fjoin_S y t).
Proof. exact: (@fmeetACA _ S^~s). Qed.

Lemma fjoinKI L (S: {finLattice L}) :
  {in S &, forall x y, \fjoin_S x (\fjoin_S x y) = \fjoin_S x y}.
Proof. exact: (@fmeetKI _ S^~s). Qed.

Lemma fjoinIK L (S : {finLattice L}) :
  {in S &, forall x y, \fjoin_S (\fjoin_S x y) y = \fjoin_S x y}.
Proof. exact: (@fmeetIK _ S^~s). Qed.

Lemma fjoinKIC L (S : {finLattice L}) :
  {in S &, forall x y, \fjoin_S x (\fjoin_S y x) = \fjoin_S x y}.
Proof. exact: (@fmeetKIC _ S^~s). Qed.

Lemma fjoinIKC L (S : {finLattice L}) :
  {in S &, forall x y, \fjoin_S (\fjoin_S y x) y = \fjoin_S x y}.
Proof. exact: (@fmeetIKC _ S^~s). Qed.

Lemma leUfl L (S: {finLattice L}) :
  {in S & &, forall x y z, x <=_L y -> x <=_L \fjoin_S y z}.
Proof.
move=> ??????; exact: (@lefIl _ S^~s).
Qed.

Lemma leUfr L (S : {finLattice L}) :
  {in S & &, forall x y z, x <=_L z -> x <=_L \fjoin_S y z}.
Proof.
move=> ??????; exact: (@lefIr _ S^~s).
Qed.

(*Lemma lefU2 L (S : {finLattice L}) :
  {in S & &, forall x y z, (x <=_L y) || (x <=_L z) ->
  Proof.
  x <=_L \fjoin_S y z}.
move=> ??????; exact: (@leIf2 _ S^~s).
Qed.*)

Lemma fjoin_idPr L (S : {finLattice L}) {x y}: x \in S -> y \in S ->
  reflect (\fjoin_S y x = x) (y <=_L x).
Proof.
move=> ??; exact: (@fmeet_idPr _ S^~s).
Qed.


Lemma fjoin_idPl L (S: {finLattice L}) {x y} : x \in S -> y \in S ->
  reflect (\fjoin_S x y = x) (y <=_L x).
Proof.
move=> ??; exact: (@fmeet_idPl _ S^~s).
Qed.

Lemma fjoin_l L (S : {finLattice L}) :
  {in S &, forall x y, y <=_L x -> \fjoin_S x y = x}.
Proof.
move=> ????; exact: (@fmeet_l _ S^~s).
Qed.

Lemma fjoin_r L (S : {finLattice L}) :
  {in S &, forall x y, x <=_L y -> \fjoin_S x y = y}.
Proof.
move=> ????; exact: (@fmeet_r _ S^~s).
Qed.

Lemma leUfidl L (S: {finLattice L}) :
  {in S &, forall x y, (\fjoin_S x y <=_L x) = (y <=_L x)}.
Proof.
move=> ????; exact: (@lefIidl _ S^~s).
Qed.

Lemma leUfidr L (S : {finLattice L}) :
  {in S &, forall x y, (\fjoin_S y x <=_L x) = (y <=_L x)}.
Proof.
move=> ????; exact: (@lefIidr _ S^~s).
Qed.

Lemma eq_fjoinl L (S : {finLattice L}) :
  {in S &, forall x y, (\fjoin_S x y == x) = (y <=_L x)}.
Proof.
move=> ????; exact: (@eq_fmeetl _ S^~s).
Qed.

Lemma eq_fjoinr L (S : {finLattice L}) :
  {in S &, forall x y, (\fjoin_S x y == y) = (x <=_L y)}.
Proof.
move=> ????; exact: (@eq_fmeetr _ S^~s).
Qed.

Lemma leUf2 L (S: {finLattice L}) x y z t :
  x \in S -> y \in S -> z \in S -> t \in S ->
  x <=_L z -> y <=_L t -> \fjoin_S x y <=_L \fjoin_S z t.
Proof.
move=> ????; exact: (@lefI2 _ S^~s).
Qed.

(* -------------------------------------------------------------------- *)
Lemma mem_bigfmeet L (S: {finLattice L}) (P : pred T) (F : T -> T) x :
  x \in S -> {in S, forall y, F y \in S} ->
     \big[\fmeet_S / x]_(i <- S | P i) F i \in S.
Admitted.

Lemma mem_bigfjoin L (S: {finLattice L}) (P : pred T) (F : T -> T) x :
  x \in S -> {in S, forall y, F y \in S} ->
     \big[\fjoin_S / x]_(i <- S | P i) F i \in S.
Admitted.

Definition fpick (S : {fset T}) :=
  omap val (@pick [finType of S] xpredT).

Variant fpick_spec (S : {fset T}) : option T -> Type :=
| FPick0 of S = fset0 : fpick_spec S None
| FPickS (x0 : T) of x0 \in S : fpick_spec S (Some x0).

Lemma fpickP S : fpick_spec S (fpick S).
Proof.
rewrite /fpick; case: pickP => /= [x _|]; first by apply: (FPickS (valP x)).
case: (S =P fset0) => [-> _|]; first by constructor.
by move/eqP/fset0Pn=> h -/(_ [` xchooseP h]).
Qed.

Lemma fpick0 : fpick fset0 = None.
Proof. by case: fpickP. Qed.

Lemma fpickS (S : {fset T}) :
  S != fset0 -> exists2 x0, x0 \in S & fpick S = Some x0.
Proof. by case: fpickP => [->|] // x0 x0_in_S _; exists x0. Qed.

Definition fbot L (S : {finLattice L}) :=
  if fpick S is Some x0 then
    \big[\fmeet_S/x0]_(x <- S) x
  else
    PreLattice.witness L.

Notation "\fbot_ S" := (fbot S) (at level 2, S at next level, format "\fbot_ S").

Definition ftop L (S : {finLattice L}) := \fbot_(S^~s).

Notation "\ftop_ S" := (ftop S) (at level 2, S at next level, format "\ftop_ S").

Lemma foo L (S : {finLattice L}) x0 :
  x0 \in S -> \fbot_S = \big[\fmeet_S/x0]_(x <- S) x.
Proof.
rewrite inE /fbot; case: fpickP => [->//|y0 y0_in_S x0_in_S].
rewrite -(fsetD1K x0_in_S).
Admitted.

Lemma mem_fbot L (S : {finLattice L}) x0 :
  x0 \in S -> \fbot_S \in S.
Proof.
move => x0S; rewrite (foo x0S) big_seq.
by apply/big_stable => //; apply/mem_fmeet.
Qed.

Lemma le0f L (S : {finLattice L}) : {in S, forall x, \fbot_S <=_L x}.
Proof.
move => x xS; rewrite (foo xS) big_seq.
rewrite (big_mem_sub _ _ _ _ xS _ x) ?leIfl //.
apply/big_stable => //; apply/mem_fmeet.
- exact: fmeetC.
- exact: fmeetA.
- exact: mem_fmeet.
Qed.

Lemma fjoinf0 L (S : {finLattice L}) : {in S, right_id \fbot_S (\fjoin_S)}.
Proof. by move=> x xS; apply/eqP; rewrite eq_fjoinl ?le0f ?(mem_fbot xS). Qed.

Lemma fjoin0f L (S : {finLattice L}): {in S, left_id \fbot_S (\fjoin_S)}.
Proof. by move=> x xS; apply/eqP; rewrite eq_fjoinr ?le0f ?(mem_fbot xS). Qed.

Lemma mem_ftop L (S : {finLattice L}) x0 :
  x0 \in S -> \ftop_S \in S.
Proof. exact: (@mem_fbot _ S^~s). Qed.

Lemma lef1 L (S : {finLattice L}) : {in S, forall x, x <=_L \ftop_S}.
Proof. move=> ??; exact: (@le0f _ S^~s). Qed.

Lemma fmeetf1 L (S : {finLattice L}) : {in S, right_id \ftop_S (\fmeet_S)}.
Proof. exact: (@fjoinf0 _ S^~s). Qed.

Lemma fmeet1f L (S : {finLattice L}) : {in S, left_id \ftop_S (\fmeet_S)}.
Proof. exact: (@fjoin0f _ S^~s). Qed.

(* ---------------------------------------------------------------------- *)

Lemma ftop_id L (S: {finLattice L}) :
  {in S, forall t, (forall x, x \in S -> x <=_L t) -> \ftop_S = t}.
Proof.
move=> t tS ttop; apply/(@le_anti _ L).
by rewrite lef1 //= andbT; apply/ttop; rewrite (mem_ftop tS).
Qed.

Lemma ftopE L (S: {finLattice L}) : S != fset0 :> {fset _} ->
  \ftop_S = \big[\fjoin_S / \fbot_S]_(i <- S) i.
Proof.
by case/fset0Pn => x /(@mem_ftop _ S^~s) /foo.
Qed.

Lemma fbot_id L (S: {finLattice L}) :
  {in S, forall t, (forall x, x \in S -> x >=_L t) -> \fbot_S = t}.
Proof. exact: (@ftop_id _ S^~s). Qed.

Lemma fbotE L (S: {finLattice L}) : S != fset0 :> {fset _} ->
\fbot_S = \big[\fmeet_S / \ftop_S]_(i <- S) i.
Proof. exact: (@ftopE _ S^~s). Qed.

End FinLatticeTheory.

Notation "\fbot_ S" := (@fbot _ _ S) (at level 2, S at next level, format "\fbot_ S").
Notation "\ftop_ S" := (@ftop _ _ S) (at level 2, S at next level, format "\ftop_ S").


(* ==================================================================== *)
Section Atom.
Context {T : choiceType}.
Implicit Type (L : {preLattice T}).

Definition atom L (S : {finLattice L}) a := [&& a \in S, (\fbot_S <_L a) &
  ~~[exists x : S, (\fbot_S <_L val x) && (val x <_L a)]].

Definition coatom L (S : {finLattice L}) a := @atom _ S^~s a.

Lemma atomP L (S : {finLattice L}) a: reflect
  ([/\ a \in S, (\fbot_S <_L a) &
  forall x, x \in S -> \fbot_S <_L x -> ~~(x <_L a)])
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

Lemma coatomP L (S : {finLattice L}) a: reflect
  ([/\ a \in S, (a <_L \ftop_S) &
  forall x, x \in S -> x <_L \ftop_S -> ~~(a <_L x)])
  (coatom S a).
Proof. apply/(iffP idP).
- by move/atomP.
- move=> ?; exact/atomP.
Qed.

End Atom.

(* ==================================================================== *)
Module Interval.
Section Interval.

Context {T : choiceType}.
Implicit Type (L : {preLattice T}).

Lemma meet_foo L (S: {finLattice L}) (P : pred T) (F : T -> T) x :
  {in S, forall y, F y \in S} -> x \in S -> P x ->
     \big[\fmeet_S / \ftop_S]_(i <- S | P i) F i <=_L F x.
Admitted.

Lemma join_foo L (S: {finLattice L}) (P : pred T) (F : T -> T) x :
  {in S, forall y, F y \in S} -> x \in S -> P x ->
     F x <=_L \big[\fjoin_S / \fbot_S]_(i <- S | P i) F i.
Admitted.

Definition interval L (S : {finLattice L}) (a b : T) :=
  [fset x | x in S & (\big[\fmeet_S / \ftop_S]_(i <- S | i >=_L a) i <=_L
                     x <=_L \big[\fjoin_S / \fbot_S]_(i <- S | i <=_L b) i)].

Lemma in_interval L (S : {finLattice L}) a b x :
  x \in S -> a <=_L x -> x <=_L b -> x \in interval S a b.
Admitted.

Lemma intervalE L (S : {finLattice L}) a b x :
  a \in S -> b \in S -> x \in interval S a b = (x \in S) && (a <=_L x <=_L b).
Proof.
Admitted.
(*by rewrite /interval in_fsetE /= inE. Qed.*)

Lemma intervalP L (S : {finLattice L}) a b x :
  a \in S -> b \in S ->
  reflect
    (x \in S /\ a <=_L x <=_L b)
    (x \in interval S a b).
Proof. by move=> aS bS; rewrite intervalE //; apply/andP. Qed.

Lemma in_intv_support L (S : {finLattice L}) a b x :
  x \in interval S a b -> x \in S.
Proof. by rewrite in_fsetE; case/and3P. Qed.

Lemma in_intv_range L (S : {finLattice L}) a b x:
  a \in S -> b \in S -> x \in interval S a b -> a <=_L x <=_L b.
Proof. move => aS bS; by case/intervalP. Qed.

Lemma dual_intv_fset_eq L (S: {finLattice L}) a b:
  interval S a b = interval S^~s b a :> {fset _}.
Proof. by apply/eqP/fset_eqP=> x; rewrite !in_fsetE !inE [X in _ && X]andbC. Qed.

Lemma premeet_intv_stable L (S : {finLattice L}) x y a b:
  x \in interval S a b -> y \in interval S a b ->
  premeet L S x y \in interval S a b.
Proof.
rewrite !in_fsetE => /and3P[xS alex xleb] /and3P[yS aley yleb].
apply/and3P; split.
- exact: mem_fmeet.
- by apply/premeet_inf=> //; apply/mem_bigfmeet; rewrite ?(mem_ftop xS).
- by apply:(le_trans _ xleb); case: (premeet_min L xS yS).
Qed.

Lemma premeet_intvE L (S : {finLattice L}) a b x y:
  x \in interval S a b -> y \in interval S a b ->
  premeet L S x y = premeet L (interval S a b) x y.
Proof.
move=> x_in y_in.
move: (x_in); rewrite in_fsetE // => /and3P[xS alex xleb].
move: (y_in); rewrite in_fsetE // => /and3P[yS aley yleb].
apply/(@le_anti _ L)/andP; split.
- by apply: premeet_inf=> //; first exact: premeet_intv_stable;
     case: (premeet_min L xS yS).
- apply: premeet_incr=> //; apply/fsubsetP=> ?; exact: in_intv_support.
Qed.

Lemma prejoin_intv_stable L (S : {finLattice L}) x y a b:
  x \in interval S a b -> y \in interval S a b ->
  prejoin L S x y \in interval S a b.
Proof.
rewrite dual_intv_fset_eq -dual_premeet; exact: premeet_intv_stable. Qed.

Lemma prejoin_intvE L (S: {finLattice L}) a b x y:
  x \in interval S a b -> y \in interval S a b ->
  prejoin L S x y = prejoin L (interval S a b) x y.
Proof.
rewrite dual_intv_fset_eq -dual_premeet; exact: premeet_intvE.
Qed.

Lemma stable_interval L (S:{finLattice L}) a b:
  stable L (interval S a b) && stable ([preLattice of L^~]) (interval S a b).
Proof.
apply/andP; split; apply/stableP.
- by move=> ????;rewrite -premeet_intvE // premeet_intv_stable.
- by move=> ????; rewrite /= -prejoin_intvE // prejoin_intv_stable.
Qed.

Definition FinLatInterval L (S: {finLattice L}) a b :=
  FinLattice (@stable_interval L S a b).

End Interval.
End Interval.

Notation " [< a ; b >]_ S " := (@Interval.FinLatInterval _ _ S a b)
  (at level 0, S at level 8, format "[<  a ;  b  >]_ S").

Section IntervalTheory.

Context {T : choiceType}.
Implicit Type (L : {preLattice T}).

Lemma in_interval L (S : {finLattice L}) a b x :
  x \in S -> a <=_L x -> x <=_L b -> x \in [< a ; b >]_S.
Admitted.

Lemma intervalE L (S : {finLattice L}) a b x :
  a \in S -> b \in S -> x \in [< a ; b >]_S = (x \in S) && (a <=_L x <=_L b).
Proof.
Admitted.

Lemma intervalP L (S: {finLattice L}) a b x:
  a \in S -> b \in S ->
  reflect
   (x \in S /\ a <=_L x <=_L b)
    (x \in [< a ; b >]_S).
Proof. move=> aS bS; rewrite Interval.intervalE //; exact:andP. Qed.

Lemma intv_id L (S: {finLattice L}) : [<\fbot_S; \ftop_S>]_S = S.
Proof.
case/boolP: (S == fset0 :> {fset _}).
- move/eqP => Seq0; apply/eqP/fset_eqP => x.
  by rewrite !inE Seq0 in_fset0.
- move=> Sprop0; apply/eqP/fset_eqP => x.
  rewrite !inE; apply: andb_idr => xS.
  by rewrite Interval.meet_foo ?le0f ?Interval.join_foo ?lef1.
Qed.

Lemma mono_interval L (S : {finLattice L}) (x y x' y' : T) :
  x \in S -> x' \in S -> y \in S -> y' \in S ->
    x'<=_L x -> y <=_L y' -> [< x; y >]_[< x'; y' >]_S = [< x; y >]_S.
Proof.
Admitted.
(*  move=> lex ley; apply/eqP/fset_eqP => z.
apply/(sameP idP)/(iffP idP).
- move=> z_xyS.
Admitted.*)

Lemma sub_interval L (S : {finLattice L}) a b c d:
  a \in S -> b \in S -> c \in S -> d \in S ->
  a <=_L b -> c <=_L d ->
  ([<a;b>]_S `<=` [<c;d>]_S)%fset = (c <=_L a) && (b <=_L d).
Proof.
Admitted.
(*
  move=> a b aS bS aleb cled; apply/(sameP idP)/(iffP idP).
- case/andP => c_le_a b_le_d; apply/fsubsetP => x /in_intervalP
  [x_in_S a_le_x x_le_b].
apply/in_intervalP; rewrite x_in_S; split=> //;
[exact:(le_trans c_le_a) | exact: (le_trans x_le_b)].
- move/fsubsetP => sub.
  have/in_intervalP[]: a \in [<c;d>]_S by
    apply/sub/in_intervalP; rewrite aS lexx aleb.
  have/in_intervalP[]: b \in [<c;d>]_S by
    apply/sub/in_intervalP; rewrite bS lexx aleb.
  by move=> _ _ -> _ ->.
Qed.*)

Lemma dual_intv_r L (S : {finLattice L}) a b :
  ([<a; b>]_S)^~s = [< b ; a>]_(S^~s).
Proof.  by apply/val_inj/Interval.dual_intv_fset_eq.  Qed.

Definition dual_intv := (@dual_intv_r, fun L => @dual_intv_r [preLattice of L^~]).

Lemma inL_intv L (S : {finLattice L}) (x y : T) :
  x \in S -> x <=_L y -> x \in [< x; y >]_S.
Proof.
by move=> xS xy; apply/Interval.in_interval. Qed.

Lemma inR_intv L (S : {finLattice L}) (x y : T) :
  y \in S -> x <=_L y -> y \in [< x; y >]_S.
Admitted.

Lemma in0L_intv L (S : {finLattice L}) (y : T) :
  y \in S -> \fbot_S \in [< \fbot_S; y >]_S.
Proof.
Admitted.
(*by move=> nz_S; rewrite inL_intv ?mem_fbot ?le0f //; apply/fset0Pn; exists y.
Qed.*)

Lemma in0R_intv L (S : {finLattice L}) (x : T) :
  x \in S -> \ftop_S \in [< x; \ftop_S >]_S.
Proof.
Admitted.
(*move=> ?; rewrite -mem_intv_dual.
have <-: \fbot_(S^~s) = \ftop_S by [].
exact:in0L_intv.
Qed.*)

Lemma intv0E L (S : {finLattice L}) (a b : T) :
  a \in S -> a <=_L b -> \fbot_([<a; b>]_S) = a.
Proof.
Admitted.
(*move=> aS ab; apply:fbot_id.
- by apply/fset0Pn; exists a; rewrite !inE aS ab lexx.
- by rewrite !inE aS ab lexx.
- by move=> x; rewrite !inE => /and3P [].
Qed.*)

Lemma intv1E L (S : {finLattice L}) (a b : T) :
  b \in S -> a <=_L b -> \ftop_[<a; b>]_S = b.
Proof.
Admitted.
(*by move: (@intv0E _ S^~s b a); rewrite -dual_intv.
Qed.*)

Lemma sub_atomic L (S: {finLattice L}) x:
  x \in S -> \fbot_S <_L x ->
  exists2 y, atom S y & y <=_L x.
Proof.
set S' := ([< \fbot_S; x >]_S `\` [fset \fbot_S; x])%fset.
move=> x_in_S bot_lt_x.
have Sprop0: S != fset0 :> {fset _} by apply/fset0Pn; exists x.
case/boolP: (S' == fset0).
- rewrite fsetD_eq0 => /fsubsetP intv_sub.
  exists x => //.
  apply/atomP; split => // y y_in_S; apply: contraTN => y_lt_x.
  rewrite lt_neqAle le0f ?andbT //.
  have/intv_sub: (y \in [<\fbot_S; x>]_S)
    by apply/in_interval=> //; rewrite (le0f, ltW).
  by rewrite !inE (lt_eqF y_lt_x) orbF => /eqP ->; rewrite eq_refl.
- case/(minset_neq0 L)/fset0Pn => y /mem_minsetE.
  rewrite in_fsetD intervalE ?(mem_fbot x_in_S) // !inE negb_or.
  case => /and4P [/andP [yNbot y_neq_x] y_in_S bot_le_y y_le_x mini_y].
  exists y => //. apply/atomP; split => //.
    by rewrite lt_neqAle eq_sym yNbot bot_le_y.
  move=> x0 x0_in_S bot_lt_x0; apply: contraT; rewrite negbK => x0_lt_y.
  have/mini_y: x0 \in S'.
  + rewrite in_fsetD intervalE ?(mem_fbot x_in_S) //.
    admit.
(*  x0_in_S eq_sym. (lt_eqF bot_lt_x0) (ltW bot_lt_x0) /=.
    rewrite -lt_def; exact: (lt_le_trans x0_lt_y).
  by rewrite x0_lt_y.*)
Admitted.

Lemma sub_coatomic L (S: {finLattice L}) x:
  x \in S -> x <_L \ftop_S -> exists2 y, coatom S y & x <=_L y.
Proof. exact: (@sub_atomic _ S^~s). Qed.


(* -------------------------------------------------------------------- *)
Section IndIncr.
Context (L : {preLattice T}).
Variable (P : {finLattice L} -> Prop).

Hypothesis (P_incr : forall S, forall x,
  atom S x -> P S -> P [<x; \ftop_S>]_S).

Lemma ind_incr (S : {finLattice L}) (x : T) :
  x \in S -> P S -> P [<x; \ftop_S>]_S.
Proof.
Admitted.
(*
move=> xS PS.
have Sprop0 : S != fset0 :> {fset _} by apply/fset0Pn; exists x.
move: {2}#|`_| (leqnn #|`[< \fbot_S; x >]_S|) => n.
elim: n S xS PS Sprop0 => [|n ih] S xS PS Sprop0.
- rewrite leqn0 => /eqP /cardfs0_eq /(congr1 (fun S => x \in S)).
  rewrite in_fset0 => /in_intervalP; case; split=> //.
  - by rewrite le0f.
  - by rewrite lexx.
case/boolP: (atom S x) => [atom_Sx|atomN_Sx]; first by move=> _; apply: P_incr.
case: (x =P \fbot_S) => [-> _|/eqP neq0_x]; first by rewrite intv_id.
have bot_lt_x: \fbot_S <_L x by rewrite lt_def eq_sym neq0_x le0f.
move=> sz; case: (sub_atomic xS bot_lt_x) => y [atom_Sy y_le_x].
have yS: y \in S by case/atomP: atom_Sy.
have nz_S: S != fset0 :> {fset _} by apply/fset0Pn; exists x.
have ne_xy: x != y by apply: contraNneq atomN_Sx => ->.
have: x \in [< y; \ftop_S >]_S.
- by apply/in_intervalP; rewrite xS y_le_x lef1.
move/ih => /(_ (P_incr atom_Sy PS)).
rewrite !(intv0E, intv1E) ?mem_ftop ?lef1 //.
rewrite !mono_interval ?lexx ?lef1 //.
apply.
  by apply/fset0Pn; exists y; rewrite inL_intv ?lef1.
rewrite -ltnS; pose X := \fbot_S |` [< \fbot_S; x >]_S `\ \fbot_S.
apply: (@leq_trans #|`X|); last by rewrite /X fsetD1K // in0L_intv.
apply: fproper_ltn_card; rewrite {}/X.
rewrite fsetD1K ?in0L_intv //.
apply: (@fsub_proper_trans _ ([< \fbot_S; x >]_S `\ \fbot_S)); last first.
- by apply/fproperD1; rewrite in0L_intv.
apply/fsubsetD1P; split.
- by rewrite sub_interval ?le0f ?lexx.
apply: contraL atom_Sy => /in_intervalP[_].
rewrite le_eqVlt (le_gtF (le0f nz_S yS))  // orbF => /eqP-> _.
by apply/negP => /atomP; rewrite ltxx; case.
Qed.*)
End IndIncr.



(* -------------------------------------------------------------------- *)
Section IndDecr.
Lemma dualK (L : {preLattice T}) (S : {finLattice L}) : (S^~s)^~s = S.
Proof. by exact/val_inj. Qed.

Lemma fbot_dual_r (L : {preLattice T}) (S : {finLattice L}) :
  \fbot_(S^~s) = \ftop_S.

Notation dualize := (fun f => (@f, fun L => @f [preLattice of L^~])).
  Proof. by []. Qed.

Definition fbot_dual := dualize fbot_dual_r.

Context (L : {preLattice T}).
Variable (P : {finLattice L} -> Prop).

Hypothesis (P_decr : forall S, forall x,
  coatom S x -> P S -> P [<\fbot_S; x>]_S).

Lemma ind_decr (S : {finLattice L}) (x : T) :
  x \in S -> P S -> P [<\fbot_S; x>]_S.
Proof.
move=> x_in_S PS.
rewrite -[S]dualK -dual_intv fbot_dual.
apply: (ind_incr (P := fun S' : finLattice [preLattice of L^~] => P S'^~s)) => //.
- by move=> S' x' ??; rewrite dual_intv; apply: P_decr.
- by rewrite dualK.
Qed.

End IndDecr.

(* -------------------------------------------------------------------- *)
Section Ind.
Context (L : {preLattice T}).
Variable (P : {finLattice L} -> Prop).

Hypothesis (P_incr : forall (S: {finLattice L}), forall x,
  atom S x -> P S -> P [<x; \ftop_S>]_S).
Hypothesis (P_decr : forall (S:{finLattice L}), forall x,
  coatom S x -> P S -> P [<\fbot_S; x>]_S).

Lemma ind_id (S : {finLattice L}) (x y : T) :
  x \in S -> y \in S -> x <=_L y -> P S -> P [<x; y>]_S.
Proof.
Admitted.
(*move=> xS yS le_xy PS; have h: P [< x; \ftop_S >]_S by apply: ind_incr.
have Sprop0 : S != fset0 :> {fset _} by apply/fset0Pn; exists x.
suff: P [< \fbot_[< x; \ftop_S >]_S; y >]_[< x; \ftop_S >]_S.
- by rewrite intv0E ?lef1 // mono_interval // ?lexx ?lef1.
apply: ind_decr => //; apply/in_intervalP; split=> //.
by rewrite lef1.
Qed.*)
End Ind.

End IntervalTheory.