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

(* -------------------------------------------------------------------- *)
(* TODO: move this section to relorder.v                                *)
Section POrderMonotonyTheory.
Context (T T' : choiceType) (r : {pOrder T}) (r' : {pOrder T'}).
Context (D D' : pred T) (f : T -> T').

Hint Resolve lt_neqAle le_anti : core.

Lemma ltW_homo :
     {homo f : x y / x <_r  y >-> x <_r'  y}
  -> {homo f : x y / x <=_r y >-> x <=_r' y}.
Proof. by apply: homoW. Qed.

Lemma inj_homo_lt :
     injective f
  -> {homo f : x y / x <=_r y >-> x <=_r' y}
  -> {homo f : x y / x <_r  y >-> x <_r'  y}.
Proof. exact: inj_homo. Qed.

Lemma inc_inj : {mono f : x y / x <=_r y >-> x <=_r' y} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma leW_mono :
     {mono f : x y / x <=_r y >-> x <=_r' y}
  -> {mono f : x y / x <_r  y >-> x <_r'  y}.
Proof. exact: anti_mono. Qed.

Lemma ltW_homo_in :
     {in D & D', {homo f : x y / x <_r  y >-> x <_r'  y}}
  -> {in D & D', {homo f : x y / x <=_r y >-> x <=_r' y}}.
Proof. exact: homoW_in. Qed.

Lemma inj_homo_lt_in :
     {in D & D', injective f}
  -> {in D & D', {homo f : x y / x <=_r y >-> x <=_r' y}}
  -> {in D & D', {homo f : x y / x <_r  y >-> x <_r'  y}}.
Proof. exact: inj_homo_in. Qed.

Lemma inc_inj_in :
      {in D &, {mono f : x y / x <=_r y >-> x <=_r' y}}
   -> {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma leW_mono_in :
     {in D &, {mono f : x y / x <=_r y >-> x <=_r' y}}
  -> {in D &, {mono f : x y / x <_r  y >-> x <_r'  y}}.
Proof. exact: anti_mono_in. Qed.
End POrderMonotonyTheory.

(* -------------------------------------------------------------------- *)
(* TODO: move this section to relorder.v                                *)
Section POrderMonotonyTheoryCodom.
Context (d : unit) (T : choiceType) (T' : porderType d) (r : {pOrder T}).
Context (D D' : pred T) (f : T -> T').

Hint Resolve lt_neqAle le_anti : core.
Hint Resolve Order.POrderTheory.lt_neqAle Order.POrderTheory.le_anti : core.

Lemma ltW_homo_as :
     {homo f : x y / x <_r  y >-> (x <  y)%O}
  -> {homo f : x y / x <=_r y >-> (x <= y)%O}.
Proof. by apply: homoW. Qed.

Lemma inj_homo_lt_as :
     injective f
  -> {homo f : x y / x <=_r y >-> (x <= y)%O}
  -> {homo f : x y / x <_r  y >-> (x <  y)%O}.
Proof. exact: inj_homo. Qed.

Lemma inc_inj_as : {mono f : x y / x <=_r y >-> (x <= y)%O} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma leW_mono_as :
     {mono f : x y / x <=_r y >-> (x <= y)%O}
  -> {mono f : x y / x <_r  y >-> (x <  y)%O}.
Proof. exact: anti_mono. Qed.

Lemma ltW_homo_in_as :
     {in D & D', {homo f : x y / x <_r  y >-> (x <  y)%O}}
  -> {in D & D', {homo f : x y / x <=_r y >-> (x <= y)%O}}.
Proof. exact: homoW_in. Qed.

Lemma inj_homo_lt_in_as :
     {in D & D', injective f}
  -> {in D & D', {homo f : x y / x <=_r y >-> (x <= y)%O}}
  -> {in D & D', {homo f : x y / x <_r  y >-> (x <  y)%O}}.
Proof. exact: inj_homo_in. Qed.

Lemma inc_inj_in_as :
      {in D &, {mono f : x y / x <=_r y >-> (x <= y)%O}}
   -> {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma leW_mono_in_as :
     {in D &, {mono f : x y / x <=_r y >-> (x <= y)%O}}
  -> {in D &, {mono f : x y / x <_r  y >-> (x <  y)%O}}.
Proof. exact: anti_mono_in. Qed.
End POrderMonotonyTheoryCodom.

(* -------------------------------------------------------------------- *)
Module PreLattice.
Section ClassDef.

Context {T : choiceType}.

Set Primitive Projections.

Record mixin_of (le : rel T) (witness : T)
       (premeet : {fset T} -> T -> T -> T)
       (prejoin : {fset T} -> T -> T -> T) := Mixin
{
  premeet_min : forall S x y, x \in S -> y \in S ->
    le (premeet S x y) x /\ le (premeet S x y) y;
  premeet_inf : forall S x y z, x \in S -> y \in S -> z \in S ->
    le z x -> le z y -> le z (premeet S x y);
  premeet_incr : forall S S' x y, S `<=` S' -> x \in S -> y \in S ->
    le (premeet S x y) (premeet S' x y);
  prejoin_max : forall S x y, x \in S -> y \in S ->
    dual_rel le (prejoin S x y) x /\ dual_rel le (prejoin S x y) y;
  prejoin_sumeet : forall S x y z, x \in S -> y \in S -> z \in S ->
    dual_rel le z x -> dual_rel le z y ->
    dual_rel le z (prejoin S x y);
  prejoin_decr : forall S S' x y, S `<=` S' -> x \in S -> y \in S ->
    dual_rel le (prejoin S x y) (prejoin S' x y)
}.

Record class_of (le lt : rel T) (witness : T)
       (premeet : {fset T} -> T -> T -> T)
       (prejoin : {fset T} -> T -> T -> T) := Class {
  base : POrder.class_of le lt;
  mixin : mixin_of le witness premeet prejoin;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  witness : T;
  premeet : {fset T} -> T -> T -> T;
  prejoin : {fset T} -> T -> T -> T;
  class_ : class_of le lt witness premeet prejoin
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord)
                            (witness ord) (premeet ord) (prejoin ord)  :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.

Variable (leT ltT : rel T) (wT : T)
         (premeetT : {fset T} -> T -> T -> T)
         (prejoinT : {fset T} -> T -> T -> T).

Definition clone c of phant_id class c :=
  @Pack phT leT ltT wT premeetT prejoinT c.

Definition pack (m0 : mixin_of leT wT premeetT prejoinT) :=
  fun (bord : POrder.order phT) b
        & phant_id (POrder.class bord) b =>
    fun m & phant_id m0 m =>
      @Pack phT leT ltT wT premeetT prejoinT
            (@Class leT ltT wT premeetT prejoinT b m).

End ClassDef.

(* ---------------------------------------------------------------------- *)
Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Notation "{ 'preLattice' T }" := (order (Phant T))
  (at level 0, format "{ 'preLattice'  T }").
Notation PreLattice le lt w premeet prejoin mixin :=
  (@pack _ (Phant _) le lt w premeet prejoin mixin _ _ id _ id).
Notation "[ 'preLattice' 'of' le ]" :=
  (@clone _ (Phant _) _ le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _) _ id)
    (at level 0, format "[ 'preLattice'  'of'  le ]").
Notation witness := witness.
Notation premeet := premeet.
Notation prejoin := prejoin.
End Exports.

End PreLattice.
Include PreLattice.Exports.

Section DualPreLattice.

Context {T: choiceType}.
Variable (L : {preLattice T}).

Definition DualPreLatticeMixin :=
  let: PreLattice.Class _ m := PreLattice.class L in
  @PreLattice.Mixin T
    (dual_rel <=:L)
    (PreLattice.witness L)
    (prejoin L) (premeet L)
      (PreLattice.prejoin_max m) (PreLattice.prejoin_sumeet m)
      (PreLattice.prejoin_decr m)
      (PreLattice.premeet_min m) (PreLattice.premeet_inf m)
      (PreLattice.premeet_incr m).

Canonical DualPreLatticePack :=
  PreLattice (dual_rel <=:L) _ _ _ _ DualPreLatticeMixin.

End DualPreLattice.

Notation "L ^~pl" := ([preLattice of (<=:(L^~))]) (at level 0, only parsing).

Section PreLatticeTheory.

Context {T: choiceType}.
Implicit Type L: {preLattice T}.

(* TO IMPROVE *)
Definition mixin L := (PreLattice.mixin (PreLattice.class L)).

Lemma premeet_min L S:
  {in S &, forall x y, premeet L S x y <=_L x /\ premeet L S x y <=_L y}.
Proof. exact: (PreLattice.premeet_min (mixin L)). Qed.

Lemma premeet_minl L S:
  {in S &, forall x y, premeet L S x y <=_L x}.
Proof. by move=> x y xS yS; case: (PreLattice.premeet_min (mixin L) xS yS). Qed.

Lemma premeet_minr L S:
  {in S &, forall x y, premeet L S x y <=_L y}.
Proof. by move=> x y xS yS; case: (PreLattice.premeet_min (mixin L) xS yS). Qed.

Lemma premeet_inf L S:
  {in S & &, forall x y z, z <=_L x -> z <=_L y -> z <=_L premeet L S x y}.
Proof. exact: (PreLattice.premeet_inf (mixin L)). Qed.

Lemma premeet_incr L S S': S `<=` S' ->
  {in S &, forall x y, premeet L S x y <=_L premeet L S' x y}.
Proof. move=> ?????; exact: (PreLattice.premeet_incr (mixin L)). Qed.

Lemma prejoin_max L S:
  {in S &, forall x y, prejoin L S x y <=_(L^~) x /\ prejoin L S x y <=_(L^~) y}.
Proof. exact: (PreLattice.prejoin_max (mixin L)). Qed.

Lemma prejoin_maxl L S:
  {in S &, forall x y, prejoin L S x y <=_(L^~) x}.
Proof. by move=> x y xS yS; case: (PreLattice.prejoin_max (mixin L) xS yS). Qed.

Lemma prejoin_maxr L S:
  {in S &, forall x y, prejoin L S x y <=_(L^~) y}.
Proof. by move=> x y xS yS; case: (PreLattice.prejoin_max (mixin L) xS yS). Qed.

Lemma prejoin_sumeet L S:
  {in S & &, forall x y z, z <=_(L^~) x -> z <=_(L^~) y -> z <=_(L^~) prejoin L S x y}.
Proof. exact: (PreLattice.prejoin_sumeet (mixin L)). Qed.

Lemma prejoin_decr L S S': S `<=` S' ->
  {in S &, forall x y, prejoin L S x y <=_(L^~) prejoin L S' x y}.
Proof. move=> ?????; exact: (PreLattice.prejoin_decr (mixin L)). Qed.

Lemma dual_premeet L S x y:
  premeet [preLattice of <=:(L^~)] S x y = prejoin L S x y.
Proof. by []. Qed.

Lemma dual_prejoin L S x y:
  prejoin [preLattice of <=:(L^~)] S x y = premeet L S x y.
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

Lemma Mjoin_sumeet S x y z :
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

Definition MeetPreLatticeMixin := @PreLattice.Mixin
  T (<=:M) (top M) _ _ (Mmeet_min) (Mmeet_inf) (Mmeet_incr)
  (Mjoin_max) (Mjoin_sumeet) (Mjoin_decr).

(*Canonical MeetPreLattice :=
  PreLattice (<=:M) _ _ _ _ MeetPreLatticeMixin.
*)
End MeetToPreLattice.

Section JoinToPreLattice.

Context {T: choiceType} (J : {bJoinOrder T}).

Definition JoinPreLatticeMixin :=
  MeetPreLatticeMixin [tMeetOrder of (<=:(J^~))].

End JoinToPreLattice.

Section FinLattice.

Context {T : choiceType}.

Definition premeet_closed (L: {preLattice T}) (S : {fset T}) :=
  [forall x : S, [forall y : S, premeet L S (fsval x) (fsval y) \in S]].

(*TODO : Change S by a predicate*)

Lemma premeet_closedP (L: {preLattice T}) (S : {fset T}) :
  reflect (forall x y, x \in S -> y \in S ->
    premeet L S x y \in S)
    (premeet_closed L S).
Proof.
apply/(iffP idP).
- by move => + x y xS yS; move/forallP/(_ [`xS])/forallP/(_ [`yS]).
- move=> premeet_closedH; apply/forallP => x; apply/forallP => y.
  apply: premeet_closedH; exact: fsvalP.
Qed.

Variable (L: {preLattice T}).

Record finLattice :=
  FinLattice { elements :> {fset T};
  _ : [&& premeet_closed L elements,
      premeet_closed L^~pl elements &
      elements != fset0]}.

Canonical finLattice_subType := Eval hnf in [subType for elements].

Definition finLattice_eqMixin := Eval hnf in [eqMixin of finLattice by <:].
Canonical  finLattice_eqType  := Eval hnf in EqType finLattice finLattice_eqMixin.

Definition finLattice_choiceMixin := [choiceMixin of finLattice by <:].
Canonical  finLattice_choiceType  :=
  Eval hnf in ChoiceType finLattice finLattice_choiceMixin.

(*Canonical finLattice_finType (S : finLattice) := [finType of S].*)

Coercion mem_finLattice (S: finLattice) : {pred T} :=
  fun x : T => (x \in (elements S)).
Canonical finLattice_predType := PredType mem_finLattice.

Lemma in_finLatticeE (S: finLattice) x : (x \in S) = (x \in elements S).
Proof. by []. Qed.

Definition inE := (@in_finLatticeE, inE).

Definition fmeet (S: finLattice) := premeet L S.
Definition fjoin (S: finLattice) := prejoin L S.

Lemma finlattice_eqP (S S' : finLattice) :
  S =i S' <-> S = S'.
Proof. by split => [eq |-> //];apply/val_inj/fsetP. Qed.

End FinLattice.

Notation "{ 'finLattice' L }" := (finLattice L) (at level 0, format "{ 'finLattice'  L }").
Notation "'\fmeet_' S" := (@fmeet _ _ S) (at level 8, format "'\fmeet_' S").
Notation "'\fjoin_' S" := (@fjoin _ _ S) (at level 8, format "'\fjoin_' S").

Section FinLatticeDual.

Context {T : choiceType} (L : {preLattice T}) (S : {finLattice L}).

(* TODO: add (only parsing) notation for [preLattice of (<=:(L^~))] *)
(* TODO: same for semilattices and lattice *)

Lemma premeet_closedDual :
  [&& premeet_closed L^~pl S,
  (premeet_closed L S) &
  S != fset0 :> {fset _}].
Proof. by case: S => S0 premeet_closedS0; rewrite andbCA. Defined.

Canonical FinLatticeDual := FinLattice premeet_closedDual.

Lemma dual_fjoinE:
  \fjoin_(FinLatticeDual)= \fmeet_S.
Proof. by []. Qed.

Lemma dual_fmeetE: \fmeet_(FinLatticeDual) = \fjoin_S.
Proof. by []. Qed.

End FinLatticeDual.

Notation "S ^~s" := (FinLatticeDual S)
  (at level 8, format "S ^~s").


(* TODO: Module FinLatticeStructure *)
(* use a lifting function :
   fun_val f x := f (val x)
   fun2_val f x y := f (val x) (val y)
   \big[\meetS/ \top_S]_(i <- S | P i) f i = \big[val_fun \meet_S]_(i : S | fun_val P i) fun_val f i
 TO BE DEVELOPED in a separate file *)

Module FinLatticeStructure.
Section FinLatticeStructure.

Context {T : choiceType}.

Definition fun_val {A : Type} {S : {fset T}} (f : T -> A) (x : S) :=
  f (fsval x).
Definition fun2_val {A : Type} {S : {fset T}} (f : T -> T -> A)
  (x y : S) :=
  f (fsval x) (fsval y).

Lemma premeet_closed_fun (L : {preLattice T}) (S : {finLattice L}) (x y : S) :
  (fun2_val (\fmeet_S) x y \in S).
Proof.
rewrite /fmeet inE; move: S x y; case => /= S + x y.
by case/andP => /premeet_closedP /(_ _ _ (fsvalP x) (fsvalP y)).
Qed.

Context (L : {preLattice T}) (S : {finLattice L}).

Local Notation Sle := (@fun2_val _ S (<=:L)).
Local Notation Slt := (@fun2_val _ S (<:L)).

Lemma Slexx : reflexive Sle.
Proof. by move=> x; rewrite /fun2_val. Qed.

Lemma Sle_anti : forall (x y : S), Sle x y -> Sle y x -> x = y.
Proof.
move=> x y; rewrite /fun2_val => le1 le2; apply/val_inj/(@le_anti _ L).
by rewrite le1 le2.
Qed.

Lemma Sle_trans : transitive Sle.
Proof. move=> y x z; rewrite /fun2_val; exact: le_trans. Qed.

Lemma Slt_def : forall (x y : S), Slt x y = (x != y) && Sle x y.
Proof. move=> x y; rewrite /fun2_val lt_def; congr (_ && _). Qed.

Lemma dSlt_def : forall (x y : S), Slt y x = (x != y) && Sle y x.
Proof. move=> x y; rewrite /fun2_val lt_def eq_sym; congr (_ && _). Qed.

Definition Sle_mixin :=
  POrder.Mixin Slexx Sle_anti Sle_trans Slt_def dSlt_def.


Definition Smeet (x y : S) := [`premeet_closed_fun x y].
Definition Sjoin (x y : S) := [` @premeet_closed_fun _ S^~s x y].


Lemma SmeetC : commutative Smeet.
Proof.
move=> x y; apply/val_inj/(@le_anti _ L).
by rewrite !premeet_inf // ?premeet_minl ?premeet_minr ?fsvalP.
Qed.

Lemma SmeetAl : forall (x y z t : S), t \in [fset x; y; z] ->
  val (Smeet x (Smeet y z)) <=_L val t.
Proof.
move=> x y z t; rewrite !in_fsetE; case/orP => [/orP []|] /eqP ->  /=.
+ by rewrite premeet_minl ?fsvalP ?premeet_closed_fun.
+ apply:(le_trans _ (premeet_minl L (fsvalP y) (fsvalP z))).
  by rewrite premeet_minr ?fsvalP ?premeet_closed_fun.
+ apply:(le_trans _ (premeet_minr L (fsvalP y) (fsvalP z))).
  by rewrite premeet_minr ?fsvalP ?premeet_closed_fun.
Qed.

Lemma SmeetAr : forall (x y z t : S), t \in [fset x; y; z] ->
  val (Smeet (Smeet x y) z) <=_L val t.
Proof.
move=> x y z t; rewrite !in_fsetE; case/orP => [/orP []|] /eqP -> /=.
+ apply:(le_trans _ (premeet_minl L (fsvalP x) (fsvalP y))).
  by rewrite premeet_minl ?fsvalP ?premeet_closed_fun.
+ apply:(le_trans _ (premeet_minr L (fsvalP x) (fsvalP y))).
  by rewrite premeet_minl ?fsvalP ?premeet_closed_fun.
+ by rewrite premeet_minr ?fsvalP ?premeet_closed_fun.
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
by rewrite !prejoin_sumeet ?prejoin_maxl ?prejoin_maxr ?premeet_closed_fun ?fsvalP.
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
by rewrite !prejoin_sumeet ?fsvalP ?SjoinAl ?SjoinAr //
  !in_fsetE eq_refl ?orbT.
Qed.

Lemma leSjoin : forall x y : S, dual_rel Sle x y = (Sjoin x y == x).
Proof.
move=> x y; apply/(sameP idP)/(iffP idP).
- move/eqP => <-; rewrite /Sle /dual_rel.
  exact:(prejoin_maxr L (fsvalP x) (fsvalP y)).
- rewrite /dual_rel /Sle => ylex; apply/eqP/val_inj/(@le_anti _ L^~).
  by rewrite prejoin_maxl ?prejoin_sumeet ?fsvalP.
Qed.

Definition Sjoin_mixin := Meet.Mixin SjoinC SjoinA leSjoin.
Definition SLattice_class := Lattice.Class Smeet_class Sjoin_mixin.
Definition SLattice_pack := Lattice.Pack (Phant _) SLattice_class.

End FinLatticeStructure.
Module Exports.
Coercion SLattice_pack : finLattice >-> Lattice.order.
Canonical SLattice_pack.
End Exports.
End FinLatticeStructure.
Include FinLatticeStructure.Exports.

(* ========================================================================= *)

Section FinLatticeTheory.

Context {T: choiceType}.
Implicit Type L : {preLattice T}.

Lemma sub_pred1 (K : {fset T}) (P : T -> Prop) :
  (forall x : K, P (fsval x)) -> {in K, forall x, P x}.
Proof. move=> Pval x xK; exact: (Pval [`xK]). Qed.

Lemma sub_pred2 (K : {fset T}) (P : T -> T -> Prop) :
  (forall x y : K, P (fsval x) (fsval y)) -> {in K &, forall x y, P x y}.
Proof. move=> Pval x y xS yS; exact: (Pval [`xS] [`yS]). Qed.

Lemma sub_pred3 (K : {fset T}) (P : T -> T -> T -> Prop) :
  (forall x y z: K, P (fsval x) (fsval y) (fsval z)) ->
  {in K & &, forall x y z, P x y z}.
Proof. move=> Pval x y z xS yS zS; exact: (Pval [`xS] [`yS] [`zS]). Qed.

Lemma mem_fmeet L (S : {finLattice L}) : {in S &, forall x y, \fmeet_S x y \in S}.
Proof.
move=> x y; case: S => S premeet_closeds; rewrite /fmeet !inE /= => xS yS.
by case/andP: premeet_closeds => /premeet_closedP/(_ x y xS yS).
Qed.

Lemma mem_fjoin L (S: {finLattice L}): {in S &, forall x y, \fjoin_S x y \in S}.
Proof. exact: (@mem_fmeet _ S^~s). Qed.

Lemma finLattice_prop0 L (S : {finLattice L}): S != fset0 :> {fset _}.
Proof. by case: S => S /= /and3P []. Qed.

Section FMeetTheory.

Lemma leIfl L (S : {finLattice L}) : {in S &, forall x y, \fmeet_S x y <=_L x}.
Proof. apply: sub_pred2; exact: (@leIl _ S). Qed.


Lemma leIfr L (S : {finLattice L}) : {in S &, forall x y, \fmeet_S y x <=_L x}.
Proof. apply: sub_pred2; exact: (@leIr _ S). Qed.

Lemma lefI L (S : {finLattice L}) :
  {in S & &, forall x y z, (x <=_L \fmeet_S y z) = (x <=_L y) && (x <=_L z)}.
Proof. apply: sub_pred3; exact (@lexI _ S). Qed.

Lemma fmeetC L (S : {finLattice L}) : {in S &, commutative (\fmeet_S)}.
Proof.
apply: sub_pred2=> x y; move: (@meetC _ S x y).
exact: (@congr1 _ _ (@fsval _ S)).
Qed.

Lemma lefIl L (S : {finLattice L}) :
  {in S & &, forall x y z, y <=_L x -> \fmeet_S y z <=_L x}.
Proof. apply: sub_pred3; exact: (@leIxl _ S). Qed.

Lemma lefIr L (S : {finLattice L}) :
  {in S & &, forall x y z, z <=_L x -> \fmeet_S y z <=_L x}.
Proof. move=> x y z xS yS zS zlex; rewrite fmeetC //; exact: lefIl. Qed.

Lemma fmeetA L (S : {finLattice L}) : {in S & &, associative (\fmeet_S) }.
Proof.
apply: sub_pred3=> x y z; move:(@meetA _ S x y z).
exact: (@congr1 _ _ (@fsval _ S)).
Qed.

Lemma fmeetxx L (S : {finLattice L}) : {in S, idempotent (\fmeet_S)}.
Proof.
apply: sub_pred1=> x; move:(@meetxx _ S x).
exact: (@congr1 _ _ (@fsval _ S)).
Qed.

Lemma leEfmeet L (S : {finLattice L}) :
  {in S &, forall x y, (x <=_L y) = (\fmeet_S x y == x)}.
Proof. apply: sub_pred2; exact:(@leEmeet _ S). Qed.

Lemma fmeetAC L (S : {finLattice L}) :
  {in S & &, right_commutative (\fmeet_S)}.
Proof.
apply: sub_pred3=> x y z; move:(@meetAC _ S x y z).
exact: (@congr1 _ _ (@fsval _ S)).
Qed.

Lemma fmeetCA L (S : {finLattice L}) :
  {in S & &, left_commutative (\fmeet_S)}.
Proof.
apply: sub_pred3=> x y z; move:(@meetCA _ S x y z).
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

End FMeetTheory.

(* -------------------------------------------------------------------- *)
Section FJoinTheory.

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

Lemma fjoinKU L (S: {finLattice L}) :
  {in S &, forall x y, \fjoin_S x (\fjoin_S x y) = \fjoin_S x y}.
Proof. exact: (@fmeetKI _ S^~s). Qed.

Lemma fjoinUK L (S : {finLattice L}) :
  {in S &, forall x y, \fjoin_S (\fjoin_S x y) y = \fjoin_S x y}.
Proof. exact: (@fmeetIK _ S^~s). Qed.

Lemma fjoinKUC L (S : {finLattice L}) :
  {in S &, forall x y, \fjoin_S x (\fjoin_S y x) = \fjoin_S x y}.
Proof. exact: (@fmeetKIC _ S^~s). Qed.

Lemma fjoinUKC L (S : {finLattice L}) :
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

Lemma lefU2 L (S : {finLattice L}) :
  {in S & &, forall x y z, (x <=_L y) || (x <=_L z) ->
  x <=_L \fjoin_S y z}.
Proof.
move=> ??????; exact: (@leIf2 _ S^~s).
Qed.

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

End FJoinTheory.

Section FMeetJoinTheory.

Lemma fmeetUK L (S : {finLattice L}) :
  {in S &, forall x y, \fjoin_S (\fmeet_S x y) y = y}.
 Proof. by move=> x y xS yS; apply/eqP; rewrite eq_fjoinr ?leIfr ?mem_fmeet. Qed.

Lemma fmeetUKC L (S : {finLattice L}) :
  {in S &, forall x y, \fjoin_S (\fmeet_S y x) y = y}.
Proof. by move=> ????; rewrite fmeetC ?fmeetUK. Qed.

Lemma fmeetKUC L (S : {finLattice L}) :
  {in S &, forall x y, \fjoin_S x (\fmeet_S y x) = x}.
Proof. by move=> ????; rewrite fjoinC ?fmeetUK ?mem_fmeet. Qed.

Lemma fmeetKU L (S : {finLattice L}) :
  {in S &, forall x y, \fjoin_S x (\fmeet_S x y) = x}.
Proof. by move=> ????; rewrite fmeetC ?fmeetKUC. Qed.

Lemma fjoinIK L (S : {finLattice L}) :
  {in S &, forall x y, \fmeet_S (\fjoin_S x y) y = y}.
Proof. exact: (@fmeetUK _ S^~s). Qed.

Lemma fjoinIKC L (S : {finLattice L}) :
  {in S &, forall x y, \fmeet_S (\fjoin_S y x) y = y}.
Proof. exact: (@fmeetUKC _ S^~s). Qed.

Lemma fjoinKIC L (S : {finLattice L}) :
  {in S &, forall x y, \fmeet_S x (\fjoin_S y x) = x}.
Proof. exact: (@fmeetKUC _ S^~s). Qed.

Lemma fjoinKI L (S : {finLattice L}) :
  {in S &, forall x y, \fmeet_S x (\fjoin_S x y) = x}.
Proof. exact: (@fmeetKU _ S^~s). Qed.

End FMeetJoinTheory.

(*Section FBigTheory.

Lemma mem_bigfmeet L (S: {finLattice L})
  (r : seq T) (P : pred T) (F : T -> T) x :
  x \in r -> {in S, forall y, F y \in S} -> {in r, forall y, y \in S} ->
  \big[\fmeet_S / x]_(i <- r | P i) F i \in S.
Proof.
move=> xr FS rS; rewrite big_seq_cond; apply: (big_ind (fun x => x \in S)).
- exact: rS.
- exact: mem_fmeet.
- by move=> i /andP [/rS /FS].
Qed.

Lemma mem_bigfjoin L (S: {finLattice L})
  (r : seq T) (P : pred T) (F : T -> T) x :
  x \in r -> {in S, forall y, F y \in S} -> {in r, forall y, y \in S} ->
  \big[\fjoin_S / x]_(i <- r | P i) F i \in S.
Proof.
exact: (@mem_bigfmeet _ S^~s).
Qed.

(* TODO : new lemma names *)

Lemma fmeet_inf_seq_idx L (S : {finLattice L})
  (r : seq T) (P : {pred T}) (F : T -> T) x :
  x \in r -> P x -> {in S, forall y, F y \in S} -> {in r, forall y, y \in S} ->
  \big[\fmeet_S / F x]_(i <- r | P i) F i <=_L F x.
Proof.
move=> xr Px FS rS.
suff: (\big[\fmeet_S / F x]_(i <- r | P i) F i <=_L F x) &&
(\big[\fmeet_S / F x]_(i <- r | P i) F i \in S) by case/andP.
rewrite big_seq_cond; apply: (big_rec (fun y => (y <=_L F x) && (y \in S))).
- by rewrite lexx FS ?rS.
- move=> a b /andP [/rS aS _] /andP [bleFx bS].
  by rewrite lefIr ?mem_fmeet ?FS // rS.
Qed.

Lemma fmeet_max_seq L (S : {finLattice L})
  (r : seq T) (P : {pred T}) (F : T -> T) x u:
  x \in r -> P x -> {in S, forall y, F y \in S} -> {in r, forall y, y \in S} ->
  F x <=_L u -> u \in S ->
  \big[\fmeet_S / F x]_(i <- r | P i) F i <=_L u.
Proof.
move=> xr Px FS rS Fxleu uS.
suff: (\big[\fmeet_S / F x]_(i <- r | P i) F i <=_L u) &&
(\big[\fmeet_S / F x]_(i <- r | P i) F i \in S) by case/andP.
rewrite big_seq_cond; apply: (big_rec (fun y => (y <=_L u) && (y \in S))).
- by rewrite Fxleu FS ?rS.
- move=> a b /andP [/rS aS _] /andP [bleFx bS].
  by rewrite lefIr ?mem_fmeet ?FS //.
Qed.

Lemma fjoin_sumeet_seq L (S : {finLattice L})
  (r : seq T) (P : {pred T}) (F : T -> T) x :
  x \in r -> P x -> {in S, forall y, F y \in S} -> {in r, forall y, y \in S} ->
  \big[\fjoin_S / F x]_(i <- r | P i) F i >=_L F x.
Proof. exact : (@fmeet_inf_seq _ S^~s). Qed.

Lemma fjoin_min_seq L (S : {finLattice L})
  (r : seq T) (P : {pred T}) (F : T -> T) x u:
  x \in r -> P x -> {in S, forall y, F y \in S} -> {in r, forall y, y \in S} ->
  F x >=_L u -> u \in S ->
  \big[\fjoin_S / F x]_(i <- r | P i) F i >=_L u.
Proof. exact: (@fmeet_max_seq _ S^~s). Qed.

End FBigTheory.*)

End FinLatticeTheory.

(* -------------------------------------------------------------------- *)
Section TBDefs.

Context {T: choiceType}.
Implicit Type L : {preLattice T}.

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

Definition ftop L (S : {finLattice L}) := fbot (S^~s).

End TBDefs.

Notation "\fbot_ S" := (fbot S) (at level 2, S at next level, format "\fbot_ S").
Notation "\ftop_ S" := (ftop S) (at level 2, S at next level, format "\ftop_ S").

Section TBFinLatticeTheory.

Context {T: choiceType}.
Implicit Type L : {preLattice T}.

Lemma fbot_def L (S : {finLattice L}) x0 :
  x0 \in S -> \fbot_S = \big[\fmeet_S/x0]_(x <- S) x.
Proof.
rewrite inE /fbot; case: fpickP => [->//|y0 y0_in_S x0_in_S].
rewrite big_seq [RHS]big_seq; apply: (big_idxx (Q := mem S)) => //;
  [exact: fmeetC| exact: fmeetA| exact: mem_fmeet| exact: fmeetxx].
Qed.

Lemma mem_fbot L (S : {finLattice L}) : \fbot_S \in S.
Proof.
case/fset0Pn: (finLattice_prop0 S)  => x0 x0S.
rewrite (fbot_def x0S) big_seq.
by apply/big_stable => //; apply/mem_fmeet.
Qed.

Lemma mem_ftop L (S : {finLattice L}) : \ftop_S \in S.
Proof. exact: (@mem_fbot _ S^~s). Qed.

Lemma fbotE L (S: {finLattice L}) :
  \fbot_S = \big[\fmeet_S / \ftop_S]_(i <- S) i.
Proof. by rewrite (fbot_def (mem_ftop S)). Qed.

Lemma ftopE L (S: {finLattice L}) :
  \ftop_S = \big[\fjoin_S / \fbot_S]_(i <- S) i.
Proof. exact: (@fbotE _ S^~s). Qed.

(* ----------------------------------------------------------------- *)

Lemma le0f L (S : {finLattice L}) : {in S, forall x, \fbot_S <=_L x}.
Proof.
move => x xS; rewrite (fbot_def xS) big_seq.
rewrite (big_mem_sub _ _ _ _ xS xS)  ?leIfl //. (* TODO: FIX IT *)
apply/big_stable => //; apply/mem_fmeet.
- exact: fmeetC.
- exact: fmeetA.
- exact: mem_fmeet.
Qed.

Lemma fjoinf0 L (S : {finLattice L}) : {in S, right_id \fbot_S (\fjoin_S)}.
Proof. by move=> x xS; apply/eqP; rewrite eq_fjoinl ?le0f ?mem_fbot. Qed.

Lemma fjoin0f L (S : {finLattice L}): {in S, left_id \fbot_S (\fjoin_S)}.
Proof. by move=> x xS; apply/eqP; rewrite eq_fjoinr ?le0f ?mem_fbot. Qed.

Lemma lef1 L (S : {finLattice L}) : {in S, forall x, x <=_L \ftop_S}.
Proof. move=> ??; exact: (@le0f _ S^~s). Qed.

Lemma fmeetf1 L (S : {finLattice L}) : {in S, right_id \ftop_S (\fmeet_S)}.
Proof. exact: (@fjoinf0 _ S^~s). Qed.

Lemma fmeet1f L (S : {finLattice L}) : {in S, left_id \ftop_S (\fmeet_S)}.
Proof. exact: (@fjoin0f _ S^~s). Qed.

Lemma ltf1 L (S : {finLattice L}) :
  {in S, forall x, (x <_L \ftop_S) = (x != \ftop_S)}.
Proof. by move=> x xS; rewrite lt_neqAle ?lef1 ?andbT. Qed.

Lemma lt0f L (S : {finLattice L}) :
  {in S, forall x, (\fbot_S <_L x) = (x != \fbot_S)}.
Proof. by move=> x xS; rewrite lt_def ?le0f ?andbT // eq_sym. Qed.

Lemma ftop_id L (S: {finLattice L}) :
  {in S, forall t, (forall x, x \in S -> x <=_L t) -> \ftop_S = t}.
Proof.
move=> t tS ttop; apply/(@le_anti _ L).
by rewrite lef1 //= andbT; apply/ttop; rewrite mem_ftop.
Qed.


Lemma fbot_id L (S: {finLattice L}) :
  {in S, forall t, (forall x, x \in S -> x >=_L t) -> \fbot_S = t}.
Proof. exact: (@ftop_id _ S^~s). Qed.

(* ------------------------------------------------------------------ *)

Section BigOpFinLattice.

Lemma mem_bigfmeet L (S: {finLattice L})
  (r : seq T) (P : pred T) (F : T -> T):
  {in S, forall y, F y \in S} -> {subset r <= S} ->
  \big[\fmeet_S / \ftop_S]_(i <- r | P i) F i \in S.
Proof.
move=> FS rS; rewrite big_seq_cond; apply: (big_ind (fun x => x \in S)).
- exact: mem_ftop.
- exact: mem_fmeet.
- by move=> i /andP [/rS /FS].
Qed.

Lemma mem_bigfjoin L (S: {finLattice L})
  (r : seq T) (P : pred T) (F : T -> T):
  {in S, forall y, F y \in S} -> {subset r <= S} ->
  \big[\fjoin_S / \fbot_S]_(i <- r | P i) F i \in S.
Proof. exact: (@mem_bigfmeet _ S^~s). Qed.

Lemma fmeet_inf_seq L (S: {finLattice L})
  (r: seq T) (P : pred T) (F : T -> T) x :
  {subset r <= S} -> {in S, forall y, F y \in S} -> x \in r -> P x ->
     \big[\fmeet_S / \ftop_S]_(i <- r | P i) F i <=_L F x.
Proof.
move=> rS FS xr Px; rewrite big_map_fun.
have FxS: F x \in [seq F j | j <- r & P j] by
  apply/map_f; rewrite mem_filter Px xr.
rewrite big_seq.
have filtS: forall i, i \in [seq F j | j <- r & P j] -> i \in S by
  move=> i /mapP [j]; rewrite mem_filter => /andP [_ jS] ->; exact/FS/rS.
rewrite (big_mem_sub _ _ _ filtS _ FxS) ?lefIl ?(filtS _ FxS)
  ?(big_stable _ filtS) ?mem_ftop //.
- exact: mem_fmeet.
- exact: fmeetC.
- exact: fmeetA.
- exact: mem_fmeet.
Qed.

Lemma fjoin_sumeet_seq L (S: {finLattice L})
  (r : seq T) (P : pred T) (F : T -> T) x :
  {subset r <= S} -> {in S, forall y, F y \in S} -> x \in r -> P x ->
     F x <=_L \big[\fjoin_S / \fbot_S]_(i <- r | P i) F i.
Proof. exact: (@fmeet_inf_seq _ S^~s). Qed.

Lemma fmeetsP L (S : {finLattice L}) (P : pred T) (F : T -> T) x :
  {in S, forall y, P y -> x <=_L F y} -> x <=_L \big[\fmeet_S / \ftop_S]_(y <- S | P y) F y.
Admitted.

Lemma fjoin_meets L (S: {finLattice L}) x y :
  x \in S -> y \in S ->
  \fjoin_S x y = \big[\fmeet_S / \ftop_S]_(i <- S | (x <=_L i) && (y <=_L i)) i.
Proof.
move=> xS yS; apply/(le_anti L)/andP; split; last first.
- apply/fmeet_inf_seq; rewrite ?mem_fjoin //.
  by apply/andP; split; rewrite ?lefUl ?lefUr.
- by apply/fmeetsP=> ???; rewrite leUf.
Qed.

Lemma fjoinsP L (S : {finLattice L}) (P : pred T) (F : T -> T) x :
  {in S, forall y, P y -> F y <=_L x} -> \big[\fjoin_S / \fbot_S]_(y <- S | P y) F y <=_L x.
Proof. exact: (@fmeetsP _ S^~s). Qed.

Lemma fmeet_joins L (S: {finLattice L}) x y :
  x \in S -> y \in S ->
  \fmeet_S x y = \big[\fjoin_S / \fbot_S]_(i <- S | (x >=_L i) && (y >=_L i)) i.
Proof. exact: (@fjoin_meets _ S^~s). Qed.

End BigOpFinLattice.
End TBFinLatticeTheory.

Module FinTBLatticeStructure.
Section FinTBLatticeStructure.

Context {T: choiceType} (L : {preLattice T}) (S : {finLattice L}) (x0 : S).

Definition Sbot := [`mem_fbot S].
Lemma Sbot_mixin : BPOrder.mixin_of (<=:S) Sbot.
Proof. move=> x; exact/le0f/fsvalP. Qed.

Definition BSLattice_class :=
  BLattice.Class (FinLatticeStructure.SLattice_class S) Sbot_mixin.

Definition Stop := [`mem_ftop S].
Lemma Stop_mixin : TPOrder.mixin_of (<=:S) Stop.
Proof. move=> x; exact/lef1/fsvalP. Qed.

Definition TBSLattice_class :=
  TBLattice.Class BSLattice_class Stop_mixin.
Definition TBSLattice_pack := TBLattice.Pack (Phant _) (TBSLattice_class).

End FinTBLatticeStructure.
Module Exports.
Coercion TBSLattice_pack : finLattice >-> TBLattice.order.
Canonical TBSLattice_pack.
Notation Sbot := Sbot.
Notation Stop := Stop.
End Exports.

End FinTBLatticeStructure.
Include FinTBLatticeStructure.Exports.

Section TestTBFinLattice.

Context {T : choiceType} {L : {preLattice T}} {S : {finLattice L}}.
Context (a : S).
Context (I : Type) (F : I -> T).
Context (P : pred I).

Hypothesis FS : forall i, F i \in S.

Goal forall (r : seq I),
\big[\fmeet_S / \ftop_S]_(i <- r | P i) F i =
(val (\big[meet S / top S]_(i <- r | P i) insubd a (F i))).
Proof.
Admitted.

End TestTBFinLattice.


(* ================================================================== *)
Section FinLattice1.

Context {T : choiceType}.
Implicit Type (L : {preLattice T}) (a : T).

Lemma premeet_closed1 L a : premeet_closed L [fset a].
Proof.
apply/premeet_closedP=> ?? /fset1P-> /fset1P->; apply/fset1P.
apply/(@le_anti _ L)/andP; split.
- by apply/premeet_minl; rewrite fset11.
- by apply/premeet_inf; rewrite ?fset11.
Qed.

Lemma is_lat1 L a :
  [&& premeet_closed L [fset a],
  premeet_closed L^~pl [fset a] &
  [fset a] != fset0].
Proof.
apply/and3P; split; first exact/premeet_closed1;
  first exact/premeet_closed1.
by apply/fset0Pn; exists a; rewrite in_fsetE.
Qed.

Definition lat1 L a := FinLattice (is_lat1 L a).

End FinLattice1.

Notation "[ 'finlattice' a 'for' L ]" := (@lat1 _ L a).

(* ==================================================================== *)
Section Atom.
Context {T : choiceType}.
Implicit Type (L : {preLattice T}).

Definition atom L (S : {finLattice L}) a := [&& a \in S, (\fbot_S <_L a) &
  ~~[exists x : S, (\fbot_S <_L val x) && (val x <_L a)]].

Definition coatom L (S : {finLattice L}) a := @atom _ S^~s a.

Lemma atomP {L} {S : {finLattice L}} {a} : reflect
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

Lemma coatomP {L} {S : {finLattice L}} {a} : reflect
  ([/\ a \in S, (a <_L \ftop_S) &
  forall x, x \in S -> x <_L \ftop_S -> ~~(a <_L x)])
  (coatom S a).
Proof. apply/(iffP idP).
- by move/atomP.
- move=> ?; exact/atomP.
Qed.

Lemma mem_atom L (S : {finLattice L}) x :
  atom S x -> x \in S.
Proof. by case/atomP. Qed.

Lemma mem_coatom L (S : {finLattice L}) x :
  coatom S x -> x \in S.
Proof. by case/coatomP. Qed.

End Atom.

(* ==================================================================== *)
Module Interval.
Section Interval.

Context {T : choiceType}.
Implicit Type (L : {preLattice T}).

Definition umeet L (S : {finLattice L}) a :=
  \big[\fmeet_S / \ftop_S]_(i <- S | i >=_L a) i.

Definition djoin L (S : {finLattice L}) b :=
  \big[\fjoin_S / \fbot_S]_(i <- S | i <=_L b) i.

Definition interval L (S : {finLattice L}) (a b : T) :=
  [fset x | x in S &
    \fmeet_S (umeet S a) (djoin S b) <=_L x <=_L \fjoin_S (umeet S a) (djoin S b)].

(* TODO: interval -> itv in the name of lemmas
 *
 *)

Lemma mem_itv L (S : {finLattice L}) a b x :
  x \in S -> a <=_L x -> x <=_L b -> x \in interval S a b.
Proof.
move=> xS alex xleb; rewrite !inE xS /=.
apply/andP; split.
- apply : lefIl => //;
    [exact: mem_bigfmeet |exact: mem_bigfjoin |exact: fmeet_inf_seq].
- apply : leUfr => //;
    [exact: mem_bigfmeet |exact: mem_bigfjoin |exact: fjoin_sumeet_seq].
Qed.

Lemma umeetE L (S : {finLattice L}) a : a \in S -> umeet S a = a.
Proof.
move=> aS; apply: (@le_anti _ L); rewrite fmeet_inf_seq //=.
suff : ((\big[\fmeet_S/ \ftop_S]_(i <- S | le L a i) i) \in S) &&
  le L a (\big[\fmeet_S/ \ftop_S]_(i <- S | le L a i) i) by
  case/andP.
rewrite big_seq_cond.
rewrite (@big_stable _ _ _ (fun i => (i \in S) && (le L a i))) //.
- move=> x y /andP [xS alex] /andP [yS aley].
  by rewrite mem_fmeet //= lefI ?alex ?aley.
- by rewrite mem_ftop lef1.
Qed.

Lemma djoinE L (S : {finLattice L}) b : b \in S -> djoin S b = b.
Proof. exact: (@umeetE _ S^~s). Qed.

Lemma mem_umeet L (S : {finLattice L}) a : umeet S a \in S.
Proof. exact: mem_bigfmeet. Qed.

Lemma mem_djoin L (S : {finLattice L}) b : djoin S b \in S.
Proof. exact: mem_bigfjoin. Qed.

Lemma itv_prop0 L (S : {finLattice L}) a b :
  interval S a b != fset0.
Proof.
apply/fset0Pn; exists (\fmeet_S (umeet S a) (djoin S b)).
rewrite !inE; apply/and3P; split => //.
- apply: mem_fmeet; [exact: mem_bigfmeet |exact: mem_bigfjoin].
- by rewrite lefIl ?mem_fjoin ?lefUl ?mem_umeet ?mem_djoin.
Qed.

Lemma intervalE L (S : {finLattice L}) a b x :
  a \in S -> b \in S -> a <=_L b ->
  x \in interval S a b = (x \in S) && (a <=_L x <=_L b).
Proof.
move=> aS bS aleb; rewrite !inE umeetE ?djoinE //.
by move: (fmeet_l aS bS aleb) (fjoin_r aS bS aleb) => -> ->.
Qed.

Lemma intervalP L (S : {finLattice L}) a b x :
  a \in S -> b \in S -> a <=_L b ->
  reflect
    (x \in S /\ a <=_L x <=_L b)
    (x \in interval S a b).
Proof. by move=> aS bS aleb; rewrite intervalE //; apply/andP. Qed.

Lemma itv_subset L (S : {finLattice L}) a b :
  {subset interval S a b <= S}.
Proof. move=>?; by rewrite in_fsetE; case/and3P. Qed.


Lemma itv_bound L (S : {finLattice L}) a b x:
  a \in S -> b \in S -> a <=_L b -> x \in interval S a b ->
  a <=_L x <=_L b.
Proof. by move => aS bS aleb /intervalP []. Qed.

Lemma dual_itv_fset_eq L (S: {finLattice L}) a b:
  interval S a b = interval S^~s b a :> {fset _}.
Proof.
apply/eqP/fset_eqP=> x; rewrite !in_fsetE !inE [X in _ && X]andbC.
by rewrite fmeetC ?mem_umeet ?mem_djoin // fjoinC ?mem_umeet ?mem_djoin.
Qed.

Lemma itv_premeet_closed L (S : {finLattice L}) x y a b:
  x \in interval S a b -> y \in interval S a b ->
  premeet L S x y \in interval S a b.
Proof.
rewrite !in_fsetE => /and3P[xS alex xleb] /and3P[yS aley yleb].
apply/and3P; split.
- exact: mem_fmeet.
- by apply/premeet_inf=> //; apply/mem_fmeet; rewrite ?mem_umeet ?mem_djoin.
- by apply:(le_trans _ xleb); case: (premeet_min L xS yS).
Qed.

Lemma premeet_itvE L (S : {finLattice L}) a b x y:
  x \in interval S a b -> y \in interval S a b ->
  premeet L S x y = premeet L (interval S a b) x y.
Proof.
move=> x_in y_in.
move: (x_in); rewrite in_fsetE // => /and3P[xS alex xleb].
move: (y_in); rewrite in_fsetE // => /and3P[yS aley yleb].
apply/(@le_anti _ L)/andP; split.
- by apply: premeet_inf=> //; first exact: itv_premeet_closed;
     case: (premeet_min L xS yS).
- apply: premeet_incr=> //; apply/fsubsetP=> ?; exact: itv_subset.
Qed.

Lemma itv_prejoin_closed L (S : {finLattice L}) x y a b:
  x \in interval S a b -> y \in interval S a b ->
  prejoin L S x y \in interval S a b.
Proof. rewrite dual_itv_fset_eq -dual_premeet; exact: itv_premeet_closed. Qed.

Lemma prejoin_itvE L (S: {finLattice L}) a b x y:
  x \in interval S a b -> y \in interval S a b ->
  prejoin L S x y = prejoin L (interval S a b) x y.
Proof. rewrite dual_itv_fset_eq -dual_premeet; exact: premeet_itvE. Qed.

Lemma closed_itv L (S:{finLattice L}) a b:
  [&& premeet_closed L (interval S a b),
  premeet_closed ([preLattice of (<=:(L^~))]) (interval S a b) &
  interval S a b != fset0].
Proof.
apply/and3P; split.
- apply/premeet_closedP; move=> ????.
  by rewrite -premeet_itvE // itv_premeet_closed.
- apply/premeet_closedP; move=> ????.
  by rewrite /= -prejoin_itvE // itv_prejoin_closed.
- exact: itv_prop0.
Qed.

Definition FinLatInterval L (S: {finLattice L}) a b :=
  FinLattice (@closed_itv L S a b).

End Interval.
Module Exports.
Notation " [< a ; b >]_ S " := (@FinLatInterval _ _ S a b)
  (at level 8, S at level 8, format "[<  a ;  b  >]_ S").
Notation umeet := umeet.
Notation djoin := djoin.
End Exports.
End Interval.
Include Interval.Exports.

Section IntervalTheory.

Context {T : choiceType}.
Implicit Type (L : {preLattice T}).

Lemma fmeet_itvE L (S : {finLattice L}) a b :
  {in [<a; b>]_S &, \fmeet_([< a ; b >]_S) =2 \fmeet_S}.
Proof. by move => x y x_in y_in; rewrite /fmeet -Interval.premeet_itvE. Qed.

Lemma fjoin_itvE L (S : {finLattice L}) a b :
  {in [<a; b>]_S &, \fjoin_([< a ; b >]_S) =2 \fjoin_S}.
Proof. by move => x y x_in y_in; rewrite /fjoin -Interval.prejoin_itvE. Qed.

Lemma mem_itv L (S : {finLattice L}) a b x :
  x \in S -> a <=_L x -> x <=_L b -> x \in [< a ; b >]_S.
Proof. exact: Interval.mem_itv. Qed.

Lemma intervalE L (S : {finLattice L}) a b x :
  a \in S -> b \in S -> a <=_L b ->
  x \in [< a ; b >]_S = (x \in S) && (a <=_L x <=_L b).
Proof. exact: Interval.intervalE. Qed.

Lemma intervalP L (S: {finLattice L}) a b x:
  a \in S -> b \in S -> a <=_L b ->
  reflect
   (x \in S /\ a <=_L x <=_L b)
    (x \in [< a ; b >]_S).
Proof. exact: Interval.intervalP. Qed.

Lemma itv_subset L (S: {finLattice L}) a b x :
  x \in [< a ; b >]_S -> x \in S.
Proof. exact: Interval.itv_subset. Qed.
Lemma itv_bigrange L (S: {finLattice L}) a b x :
  x \in [< a ; b >]_S ->
  \fmeet_S (umeet S a) (djoin S b) <=_L x <=_L \fjoin_S (umeet S a) (djoin S b).
Proof. by rewrite !inE /=; case/andP. Qed.

Lemma itv_geL L (S: {finLattice L}) a b x :
  a \in S -> a <=_L b -> x \in [< a ; b >]_S -> a <=_L x.
Admitted.
(* Proof. move=> aS; rewrite !inE Interval.umeetE // => /and3P []. Qed.*)

Lemma itv_leR L (S: {finLattice L}) a b x :
  b \in S -> a <=_L b -> x \in [< a ; b >]_S -> x <=_L b.
Admitted.
(*Proof. by move=> bS; rewrite !inE Interval.join_bar // => /and3P []. Qed.*)

Lemma itv_id L (S: {finLattice L}) : [<\fbot_S; \ftop_S>]_S = S.
Proof.
apply/eqP/fset_eqP => x.
rewrite !inE; apply: andb_idr => xS.
rewrite ?Interval.umeetE ?Interval.djoinE ?mem_ftop ?mem_fbot //.
by rewrite fmeet_l ?fjoin_r ?le0f ?lef1 ?mem_fbot.
Qed.

Lemma mono_itv L (S : {finLattice L}) (A B a b : T) :
  A \in S -> B \in S -> a \in [< A; B >]_S -> b \in [<A ; B >]_S ->
  [< a; b >]_[< A; B >]_S = [< a; b >]_S.
Admitted.
(*Proof.
move=> AS BS; rewrite intervalE // => /and3P [aS Alea aleB].
rewrite intervalE // => /and3P [bS Aleb bleB].
apply/eqP/fset_eqP=> z.
apply/(sameP idP)/(iffP idP).
- case/intervalP => // zS /andP [alez zleb].
  rewrite !intervalE ?alez ?zleb ?andbT ?aS ?bS ?zS ?Aleb ?Alea //=.
  by rewrite (le_trans Alea) ?(le_trans _ bleB).
- case/intervalP; rewrite intervalE ?aS ?bS ?Alea ?Aleb //.
  by case/and3P => zS _ _ alezleb; apply/intervalP.
Qed.*)

Lemma sub_itv L (S : {finLattice L}) a b c d:
  a \in S -> b \in S -> c \in S -> d \in S ->
  a <=_L b -> c <=_L d ->
  ([<a;b>]_S `<=` [<c;d>]_S)%fset = (c <=_L a) && (b <=_L d).
Proof.
move=> aS bS cS dS aleb cled; apply/(sameP idP)/(iffP idP).
- case/andP => clea bled; apply/fsubsetP => z.
  case/intervalP => // zS /andP [alez zleb].
  by rewrite intervalE // zS (le_trans clea alez) (le_trans zleb bled).
- move/fsubsetP => sub.
  have/intervalP: a \in [<c;d>]_S by
    apply/sub; rewrite mem_itv ?aS ?aleb.
  have/intervalP: b \in [<c;d>]_S by
    apply/sub; rewrite mem_itv ?aS ?aleb.
  by case/(_ cS dS) => // _ /andP [_ ->] /(_ cS dS cled) [_ /andP [->]].
Qed.

Lemma dual_itv_r L (S : {finLattice L}) a b :
  ([<a; b>]_S)^~s = [< b ; a>]_(S^~s).
Proof.  by apply/val_inj/Interval.dual_itv_fset_eq.  Qed.

Definition dual_itv :=
  (@dual_itv_r, fun L => @dual_itv_r [preLattice of (<=:(L^~))]).

Lemma mem_itvL L (S : {finLattice L}) (x y : T) :
  x \in S -> x <=_L y -> x \in [< x; y >]_S.
Proof. by move=> xS xy; apply/Interval.mem_itv. Qed.

Lemma mem_itvR L (S : {finLattice L}) (x y : T) :
  y \in S -> x <=_L y -> y \in [< x; y >]_S.
Proof.
have -> : S = (S^~s)^~s by exact/val_inj.
rewrite -dual_itv => ??; exact: mem_itvL.
Qed.

Lemma mem_0itv L (S : {finLattice L}) (y : T) :
  y \in S -> \fbot_S \in [< \fbot_S; y >]_S.
Admitted.
(*Proof. by move=> yS; rewrite mem_itvL ?(mem_fbot yS) ?le0f. Qed.*)


Lemma mem_itv1 L (S : {finLattice L}) (x : T) :
  x \in S -> \ftop_S \in [< x; \ftop_S >]_S.
Proof.
have -> : S = (S^~s)^~s by exact/val_inj.
rewrite -dual_itv => ?. exact: mem_0itv.
Qed.

Lemma itvE0 L (S : {finLattice L}) :
  {in S &, forall a b, a <=_L b -> \fbot_([<a; b>]_S) = a}.
Admitted.
(*Proof.
move=> a b aS bS aleb; apply: fbot_id;
  rewrite ?mem_itvL //.
by move=> x /intervalP; case/(_ aS bS) => _ /andP [].
Qed.*)


Lemma itvE1 L (S : {finLattice L}):
  {in S &, forall a b, a <=_L b -> \ftop_([<a; b>]_S) = b}.
Proof.
move=> a b aS bS aleb.
have -> : S = (S^~s)^~s by exact/val_inj.
rewrite -dual_itv; exact : itvE0.
Qed.

Lemma sub_atomic L (S: {finLattice L}) x:
  x \in S -> \fbot_S <_L x ->
  exists2 y, atom S y & y <=_L x.
Admitted.
(*Proof.
set S' := ([< \fbot_S; x >]_S `\` [fset \fbot_S; x])%fset.
move=> x_in_S bot_lt_x.
have Sprop0: S != fset0 :> {fset _} by apply/fset0Pn; exists x.
case/boolP: (S' == fset0).
- rewrite fsetD_eq0 => /fsubsetP intv_sub.
  exists x => //.
  apply/atomP; split => // y y_in_S; apply: contraTN => y_lt_x.
  rewrite lt_neqAle le0f ?andbT //.
  have/intv_sub: (y \in [<\fbot_S; x>]_S)
    by apply/mem_itv=> //; rewrite (le0f, ltW).
  by rewrite !inE (lt_eqF y_lt_x) orbF => /eqP ->; rewrite eq_refl.
- case/(minset_neq0 L)/fset0Pn => y /mem_minsetE.
  rewrite in_fsetD intervalE ?(mem_fbot x_in_S) // !inE negb_or.
  case => /and4P [/andP [yNbot y_neq_x] y_in_S bot_le_y y_le_x mini_y].
  exists y => //. apply/atomP; split => //.
    by rewrite lt_neqAle eq_sym yNbot bot_le_y.
  move=> x0 x0_in_S bot_lt_x0; apply: contraT; rewrite negbK => x0_lt_y.
  have/mini_y: x0 \in S'.
  + rewrite in_fsetD intervalE ?(mem_fbot x_in_S) //.
    rewrite ?le0f ?x0_in_S //.
    rewrite ?(ltW (lt_le_trans x0_lt_y y_le_x)) ?andbT.
    rewrite !inE negb_or (gt_eqF bot_lt_x0) /=.
    by rewrite (lt_eqF (lt_le_trans x0_lt_y y_le_x)).
  by rewrite x0_lt_y.
Qed.*)

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
Admitted.
(*Proof.
move=> xS PS.
move: {2}#|`_| (leqnn #|`[< \fbot_S; x >]_S|) => n.
elim: n S xS PS => [|n ih] S xS PS.
- rewrite leqn0 => /eqP /cardfs0_eq /(congr1 (fun S => x \in S)).
  by rewrite in_fset0 intervalE ?le0f ?lexx
    ?(mem_fbot xS) ?xS.
case/boolP: (atom S x) => [atom_Sx|atomN_Sx];
  first by move=> _; apply: P_incr.
case: (x =P \fbot_S) => [-> _|/eqP neq0_x];
  first by rewrite itv_id.
have bot_lt_x: \fbot_S <_L x by
  rewrite lt_def eq_sym neq0_x le0f.
move=> sz; case: (sub_atomic xS bot_lt_x) =>
  y atom_Sy ylex.
have yS: y \in S by case/atomP: atom_Sy.
have ne_xy: x != y by apply: contraNneq atomN_Sx => ->.
have: x \in [< y; \ftop_S >]_S by
  rewrite intervalE ?ylex ?lef1 ?(mem_ftop xS) ?xS ?yS.
move/ih => /(_ (P_incr atom_Sy PS)).
rewrite !(itvE0, itvE1) ?(mem_ftop xS) ?lef1 //.
rewrite !mono_itv ?mem_itv1 ?mem_itvL
  ?intervalE ?yS ?(mem_ftop xS) ?xS ?ylex ?lef1 //.
apply.
rewrite -ltnS; pose X := \fbot_S |` [< \fbot_S; x >]_S `\ \fbot_S.
apply: (@leq_trans #|`X|); last by rewrite /X fsetD1K // mem_0itv.
apply: fproper_ltn_card; rewrite {}/X.
rewrite fsetD1K ?mem_0itv //.
apply: (@fsub_proper_trans _ ([< \fbot_S; x >]_S `\ \fbot_S)); last first.
- by apply/fproperD1; rewrite mem_0itv.
apply/fsubsetD1P; split.
- rewrite sub_itv ?le0f ?(mem_fbot xS) ?xS ?yS //=.
apply: contraL atom_Sy; rewrite intervalE //.
case/and3P => _ ylebot _; apply/negP => /atomP[].
by rewrite (le_gtF ylebot).
Qed.*)
End IndIncr.

(* -------------------------------------------------------------------- *)
Section IndDecr.
Lemma dualK (L : {preLattice T}) (S : {finLattice L}) : (S^~s)^~s = S.
Proof. by exact/val_inj. Qed.

Lemma fbot_dual_r (L : {preLattice T}) (S : {finLattice L}) :
  \fbot_(S^~s) = \ftop_S.
Proof. by []. Qed.
Notation dualize := (fun f => (@f, fun L => @f [preLattice of (<=:(L^~))])).

Definition fbot_dual := dualize fbot_dual_r.

Context (L : {preLattice T}).
Variable (P : {finLattice L} -> Prop).

Hypothesis (P_decr : forall S, forall x,
  coatom S x -> P S -> P [<\fbot_S; x>]_S).

Lemma ind_decr (S : {finLattice L}) (x : T) :
  x \in S -> P S -> P [<\fbot_S; x>]_S.
Proof.
move=> x_in_S PS.
rewrite -[S]dualK -dual_itv fbot_dual.
apply: (ind_incr (P := fun S' : finLattice [preLattice of (<=:(L^~))] => P S'^~s)) => //.
- by move=> S' x' ??; rewrite dual_itv; apply: P_decr.
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
Admitted.
(*Proof.
move=> xS yS xley PS; have h: P [< x; \ftop_S >]_S by apply: ind_incr.
have Sprop0 : S != fset0 :> {fset _} by apply/fset0Pn; exists x.
suff: P [< \fbot_[< x; \ftop_S >]_S; y >]_[< x; \ftop_S >]_S.
  rewrite itvE0 ?mono_itv ?andbT ?mem_itvL ?intervalE
    ?yS ?xley ?(mem_ftop xS) ?lef1 //.
by apply: ind_decr; rewrite ?intervalE // ?xley ?lef1 ?yS ?(mem_ftop xS).
Qed.*)
End Ind.

End IntervalTheory.

(* -------------------------------------------------------------------- *)
Module Morphism.
Section ClassDef.
Context (T : choiceType) (L : {preLattice T}) (S1 S2 : {finLattice L}).

Definition axiom (f : T -> T) :=
  [/\ {in S1, forall x, f x \in S2}
    , {in S1&, {morph f : x y / \fjoin_S1 x y >-> \fjoin_S2 x y}}
    , {in S1&, {morph f : x y / \fmeet_S1 x y >-> \fmeet_S2 x y}}
    , f \fbot_S1 = \fbot_S2
    & f \ftop_S1 = \ftop_S2].

Structure map (phS1 : phant S1) (phS2 : phant S2) :=
  Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.

Context (phS1 : phant S1) (phS2 : phant S2).
Context (f g : T -> T) (cF : map phS1 phS2).

Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phS1 phS2 f fA.
End ClassDef.

Module Exports.
Notation fmorphism f := (axiom f).
Coercion apply : map >-> Funclass.
Notation FMorphism fM := (Pack (Phant _) (Phant _) fM).
Notation "{ 'fmorphism' S1 '>->' S2 }" := (map (Phant S1) (Phant S2))
  (at level 0, format "{ 'fmorphism'  S1  '>->'  S2 }").
End Exports.
End Morphism.

Include Morphism.Exports.

(* -------------------------------------------------------------------- *)
Section MorphismTheory.
Context (T : choiceType).

Implicit Type (L : {preLattice T}).

Lemma fmorphismP L (S1 S2 : {finLattice L}) (f : {fmorphism S1 >-> S2}) :
  fmorphism S1 S2 f.
Proof. by case : f. Qed.

Lemma meet_morph_homo L (S1 S2 : {finLattice L}) f :
  {in S1, forall x, f x \in S2} ->
  {in S1 &, {morph f : x y / \fmeet_S1 x y >-> \fmeet_S2 x y}} ->
  {in S1 &, {homo f : x y / x <=_L y}}.
Proof.
move=> f_im f_morph.
move=> x y xS yS; rewrite (leEfmeet xS) // => /eqP.
move/(congr1 f); rewrite f_morph // => <-.
by apply/lefIr =>//; apply/f_im.
Qed.

Lemma meet_morph_mono L (S1 S2 : {finLattice L}) f :
  {in S1, forall x, f x \in S2} ->
  {in S1 &, {morph f : x y / \fmeet_S1 x y >-> \fmeet_S2 x y}} ->
  {in S1 &, injective f} -> {in S1&, {mono f : x y / x <=_L y}}.
Proof.
move=> f_im f_morph f_inj.
move=> x y xS yS; rewrite (leEfmeet xS) //.
rewrite (leEfmeet (f_im _ xS)) ?f_im //.
by rewrite -f_morph //; apply/(inj_in_eq f_inj) => //; apply: mem_fjoin.
Qed.

Lemma meet_fmorphism L (S1 S2 : {finLattice L}) (f : T -> T) :
  {in S1, forall x, f x \in S2} ->
  {in S1&, {morph f : x y / \fmeet_S1 x y >-> \fmeet_S2 x y}} ->
  {in S1 & on S2, bijective f} -> fmorphism S1 S2 f.
Proof.
move=> f_im f_morph [g] [g_im fgK gfK].
have f_mono := (meet_morph_mono f_im f_morph (can_in_inj fgK)).
split => //.
+ move=> x y xS yS.
  apply/(le_anti L)/andP; split.
  - rewrite -[X in (_ <=__ X)]gfK ?f_mono ?leUf ?g_im ?mem_fjoin ?f_im //.
    rewrite -f_mono ?g_im ?mem_fjoin ?f_im //.
    rewrite -[X in _ && X]f_mono ?g_im ?mem_fjoin ?f_im //.
    by rewrite gfK ?lefUl ?lefUr ?mem_fjoin ?f_im.
  - by rewrite leUf ?f_mono ?lefUl ?lefUr ?f_im ?mem_fjoin.
+ apply/(le_anti L)/andP; split; rewrite ?le0f ?f_im ?mem_fbot //.
  by rewrite -[X in (_ <=__ X)]gfK ?f_mono ?le0f ?g_im ?mem_fbot.
+ apply/(le_anti L)/andP; split; rewrite ?lef1 ?f_im ?mem_fbot //.
  by rewrite -[X in (X <=__ _)]gfK ?f_mono ?lef1 ?g_im ?mem_fbot.
Qed.

Lemma dual_fmorphism L (S1 S2 : {finLattice L}) (f : T -> T) :
  fmorphism S1 S2 f <-> fmorphism S1^~s S2^~s f.
Proof. by split; case; split. Qed.

Lemma join_fmorphism L (S1 S2 : {finLattice L}) (f : T -> T) :
  {in S1, forall x, f x \in S2} ->
  {in S1&, {morph f : x y / \fjoin_S1 x y >-> \fjoin_S2 x y}} ->
  {in S1 & on S2, bijective f} -> fmorphism S1 S2 f.
Proof. by move=>???; apply/dual_fmorphism/(@meet_fmorphism _ S1^~s S2^~s). Qed.

Context (L : {preLattice T}) (S1 S2 : {finLattice L}) (f g : {fmorphism S1 >-> S2}).

Lemma fmorph_premeet_closed : {in S1, forall x, f x \in S2}.
Proof. by case: f => ? []. Qed.

Lemma fmorphU : {in S1&, {morph f : x y / \fjoin_S1 x y >-> \fjoin_S2 x y}}.
Proof. by case: f => ? []. Qed.

Lemma fmorphI : {in S1&, {morph f : x y / \fmeet_S1 x y >-> \fmeet_S2 x y}}.
Proof. by case: f => ? []. Qed.

Lemma fmorph0 : f \fbot_S1 = \fbot_S2.
Proof. by case: f => ? []. Qed.

Lemma fmorph1: f \ftop_S1 = \ftop_S2.
Proof. by case: f => ? []. Qed.

Lemma fmorph_homo : {in S1&, {homo f : x y / x <=_L y}}.
Proof.
move=> x y xS yS; rewrite (leEfjoin xS) // => /eqP.
move/(congr1 f); rewrite fmorphU // => <-.
by apply/lefUr; apply: fmorph_premeet_closed.
Qed.

Lemma fmorph_mono :
  {in S1&, injective f} -> {in S1&, {mono f : x y / x <=_L y}}.
Proof.
move=> f_inj x y xS yS; rewrite (leEfjoin xS) //.
rewrite (leEfjoin (fmorph_premeet_closed xS)) ?(fmorph_premeet_closed yS) //.
by rewrite -fmorphU //; apply/(inj_in_eq f_inj)=> //; apply: mem_fjoin.
Qed.

Lemma fmorph_itv a b :
  a \in S1 -> b \in S1 -> a <=_L b ->
    fmorphism [<a; b>]_S1 [<f a; f b>]_S2 f.
move=> aS1 bS1 a_le_b.
have faS2: f a \in S2 by apply/fmorph_premeet_closed.
have fbS2: f b \in S2 by apply/fmorph_premeet_closed.
have fa_le_fb : f a <=_L f b by apply/fmorph_homo.
have f_itv: {in [< a; b >]_S1, forall x : T, f x \in [< f a; f b >]_S2}.
+ move=> x; case/intervalP=> // xS1 /andP [??].
  by apply/mem_itv; rewrite ?fmorph_premeet_closed ?fmorph_homo.
split => //.
+ move=> x y x_in y_in.
  rewrite !fjoin_itvE ?f_itv //.
  by rewrite fmorphU ?(itv_subset x_in) ?(itv_subset y_in).
+ move=> x y x_in y_in.
  rewrite !fmeet_itvE ?f_itv //.
  by rewrite fmorphI ?(itv_subset x_in) ?(itv_subset y_in).
+ by rewrite ?itvE0.
+ by rewrite ?itvE1.
Qed.

Lemma fmorph_itv_bij a b :
  a \in S1 -> b \in S1 -> a <=_L b ->
    {in S1 & on S2, bijective f} ->
    {in [<a; b>]_S1 & on [<f a; f b>]_S2, bijective f}.
Proof.
move=> aS1 bS1 a_le_b [f'] [f'_im fK f'K].
exists f'; split.
+ move=> x; case/intervalP; rewrite ?fmorph_premeet_closed ?fmorph_homo => // xS2.
  have {-3}->: x = f (f' x) by rewrite f'K.
  rewrite 2?fmorph_mono ?f'_im //; try by apply/(can_in_inj fK).
  by case/andP=>??; apply/mem_itv=>//; exact: f'_im.
+ move=> x /itv_subset /=; exact: fK.
+ move=> x /itv_subset /=; exact: f'K.
Qed.

Lemma fmorph_atom x :
  {in S1 & on S2, bijective f} -> atom S1 x -> atom S2 (f x).
Proof.
move=> f_bij /atomP [x_in x_lt x_min]; apply/atomP; split.
- by rewrite fmorph_premeet_closed.
- rewrite -fmorph0 (leW_mono_in (fmorph_mono _)) ?mem_fbot //.
  by apply: (in_on_bij_inj f_bij).
- move=> y yS2.
  have [x' x'_in ->]: exists2 x', x' \in S1 & y = f x'.
  - case: f_bij => f' [f'_im fK f'K].
    by exists (f' y); rewrite ?f'_im ?f'K.
  rewrite -fmorph0 !(leW_mono_in (fmorph_mono _)) ?mem_fbot //;
    try by apply/(in_on_bij_inj f_bij).
  by apply/x_min.
Qed.

End MorphismTheory.

Section BijMorphism.

Context {T : choiceType}.
Implicit Type (L : {preLattice T}).

Lemma comp_fmorphism L (S1 S2 S3 : {finLattice L})
      (f : {fmorphism S1 >-> S2}) (g : {fmorphism S2 >-> S3}) :
  fmorphism S1 S2 f -> fmorphism S2 S3 g -> fmorphism S1 S3 (g \o f).
Proof.
move=> fm gm; split.
- by move=> x x_in; rewrite ?fmorph_premeet_closed.
- by move => x y x_in y_in; rewrite /= !fmorphU ?fmorph_premeet_closed.
- by move => x y x_in y_in; rewrite /= !fmorphI ?fmorph_premeet_closed.
- by rewrite /= !fmorph0.
- by rewrite /= !fmorph1.
Qed.

Canonical fcomp L (S1 S2 S3 : {finLattice L})
           (f : {fmorphism S1 >-> S2}) (g : {fmorphism S2 >-> S3}) :=
  FMorphism (comp_fmorphism (fmorphismP f) (fmorphismP g)).

Lemma fmorphism_id L (S : {finLattice L}) :
  fmorphism S S id.
Proof. by split. Qed.

Canonical fmorph_id L (S : {finLattice L}) := FMorphism (fmorphism_id S).

Section Test.
Definition fmorph_of L (S1 S2 : {finLattice L}) (f : {fmorphism S1 >-> S2})
           & (phantom (T -> T) f) : {fmorphism S1 >-> S2} := f.
Notation "f %:fmorph" := (fmorph_of (Phantom (T -> T) f)) (at level 0).

Variable (L : {preLattice T}) (S1 S2 S3 : {finLattice L}) (f : {fmorphism S1 >-> S2}) (g : {fmorphism S2 >-> S3}).

(*Check ((g \o f)%:fmorph : {fmorphism S1 >-> S3}).*)
(*Check (id %:fmorph : {fmorphism S1 >-> S1}).*)
End Test.

Lemma fcomp_bij L (S1 S2 S3 : {finLattice L})
      (f : {fmorphism S1 >-> S2}) (g : {fmorphism S2 >-> S3}) :
  {in S1 & on S2, bijective f} -> {in S2 & on S3, bijective g} ->
  {in S1 & on S3, bijective (fcomp f g)}.
Proof.
case=> f' [f'_im fK f'K]; case=> g' [g'_im gK g'K].
exists (f' \o g'); split.
- by move=> x x_in; apply/f'_im/g'_im.
- by move=> x x_in; rewrite /= gK ?fK ?fmorph_premeet_closed.
- by move=> x x_in; rewrite /= f'K ?g'K ?g'_im.
Qed.

End BijMorphism.

(* -------------------------------------------------------------------- *)
Module Rank.
Section ClassDef.
Context (T : choiceType) (L : {preLattice T}) (S : {finLattice L}).

Definition axiom (rank : T -> nat) :=
  [/\ rank \fbot_S = 0%N
    , {in S&, {homo rank : x y / x <_L y >-> (x < y)%N}}
    & {in S&, forall x z, x <=_L z -> ((rank x).+1 < rank z)%N ->
        exists2 y, y \in S & x <_L y <_L z}].

Structure map (phS : phant S) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.

Context (phS : phant S).
Context (f g : T -> nat) (cF : map phS).

Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phS f fA.
End ClassDef.

Module Exports.
Notation rank f := (axiom f).
Coercion apply : map >-> Funclass.
Notation Rank rk := (Pack (Phant _) rk).
Notation "{ 'rank' S }" := (map (Phant S))
  (at level 0, format "{ 'rank'  S }").
End Exports.
End Rank.

Include Rank.Exports.

(* -------------------------------------------------------------------- *)
Section RankTheory.
Context (T : choiceType) (L : {preLattice T}) (S : {finLattice L}).

Implicit Types (rk : {rank S}).

Lemma rank0 rk : rk \fbot_S = 0%N.
Proof. by case: rk => ? []. Qed.

Lemma homo_rank_lt rk : {in S&, {homo rk : x y / x <_L y >-> (x < y)%N}}.
Proof. by case: rk => ? []. Qed.

Lemma homo_rank_le rk : {in S&, {homo rk : x y / x <=_L y >-> (x <= y)%N}}.
Proof. by apply/(ltW_homo_in_as (f := rk))/homo_rank_lt. Qed.

Lemma graded_rank rk :
  {in S&, forall x z, x <=_L z -> ((rk x).+1 < rk z)%N ->
    exists2 y, y \in S & x <_L y <_L z}.
Proof. by case: rk => ? []. Qed.

Lemma rank_eq0 rk x : x \in S -> (rk x == 0%N) = (x == \fbot_S).
Proof.
move=> xS; apply/(sameP idP)/(iffP idP).
- by move/eqP => ->; rewrite rank0.
- apply: contraTT; rewrite -lt0f // => /(homo_rank_lt rk (mem_fbot S) xS).
  by rewrite rank0 lt0n.
Qed.

Lemma rank_eq1 rk x : x \in S -> (rk x == rk \ftop_S) = (x == \ftop_S).
Proof.
move=> xS; apply/(sameP idP)/(iffP idP) => [/eqP->//|].
apply: contraTT; rewrite -ltf1 // => /(homo_rank_lt rk xS (mem_ftop S)).
by rewrite neq_ltn => ->.
Qed.

Lemma rank_gt0 rk x : x \in S -> (0 < rk x)%N = (\fbot_S <_L x).
Proof. move=> xS; rewrite lt0n lt0f //; congr (~~ _); exact: rank_eq0. Qed.

Lemma rank_le1 rk x : x \in S -> (rk x <= rk \ftop_S)%N.
Proof. by move=> xS; apply/homo_rank_le/lef1 => //; apply/(mem_ftop S). Qed.

Lemma rank_gt1 rk x : x \in S -> (rk x < rk \ftop_S)%N = (x <_L \ftop_S).
Proof.
by move=> xS; rewrite ltn_neqAle rank_le1 // andbT ltf1 // rank_eq1.
Qed.

Lemma rankI rk (x y : T) : x \in S -> y \in S ->
  (rk (\fmeet_S x  y) <= minn (rk x) (rk y))%N.
Proof.
move=> xS yS; rewrite leq_min !homo_rank_le ?(leIfl, leIfr) //;
  by apply: mem_fmeet.
Qed.
End RankTheory.

(* -------------------------------------------------------------------- *)
Section RankInd.
Context (T : choiceType) (L : {preLattice T}) (S : {finLattice L}).
Context (rk : {rank S}) (P : T -> Prop).

Hypothesis PH :
  {in S, forall x, {in S, forall y, (rk y < rk x)%N -> P y} -> P x}.

Lemma rank_ind x : x \in S -> P x.
Proof.
move: {2}(rk x) (leqnn (rk x)) => n; elim: n x => [|n ih] x.
+ move=> + xS; rewrite leqn0 rank_eq0 // => /eqP->.
  apply: PH; first  by rewrite (mem_fbot S).
  by move=> y yS; rewrite rank0.
rewrite leq_eqVlt=> /orP[]; last by rewrite ltnS => /ih.
move/eqP => rkx xS; apply: PH => // y yS.
by rewrite rkx ltnS => /ih; apply.
Qed.
End RankInd.

Arguments rank_ind [_ _ _] _ [_].

(* -------------------------------------------------------------------- *)
Section GradedRankS.
Context (T : choiceType) (L : {preLattice T}).
Context (S : {finLattice L}) (rk : {rank S}).

Lemma graded_rankS (x : T) : x \in S ->
  (0 < rk x)%N -> exists y : T, [/\ y \in S, y <_L x & (rk y).+1 = rk x].
Proof.
move=> xS; rewrite lt0n rank_eq0 // => nz_x; case/boolP: (rk x < 2)%N.
+ rewrite ltnS leq_eqVlt ltnS leqn0 rank_eq0 // (negbTE nz_x) orbF.
  move=> /eqP->; exists \fbot_S; split=> //; first exact: (mem_fbot S).
  - by rewrite lt0f // (mem_fbot xS). - by rewrite rank0.
rewrite -leqNgt => gt1_rkx. case: (@graded_rank _ _ _ rk \fbot_S x) => //.
- by apply: (mem_fbot S). - by rewrite (le0f xS). - by rewrite rank0.
move=> y; move: {2}(rk x - rk y)%N (leqnn (rk x - rk y)).
move=> n; elim: n y => [|n ih] y.
+ rewrite leqn0 subn_eq0 => le_rk_xy yS /andP[_ /homo_rank_lt].
  by move=> /(_ _ rk yS xS); rewrite ltnNge le_rk_xy.
rewrite leq_eqVlt => /orP[]; last by rewrite ltnS => /ih.
move=> h; have {h}: rk x = ((rk y).+1 + n)%N.
+ have: (rk x - rk y != 0)%N by rewrite (eqP h).
  rewrite subn_eq0 -ltnNge => lt_rk_yx.
  by rewrite addSnnS -(eqP h) addnC subnK // ltnW.
case: (n =P 0)%N => [{ih}-> rkxE yS /andP[_ lt_yx]|/eqP nz_n rkxE yS].
+ by exists y => //; rewrite rkxE addn0.
case/andP => [gt0_y lt_yx]; case: (@graded_rank _ _ _ rk y x) => //.
+ by apply/ltW. + by rewrite rkxE -[X in (X < _)%N]addn0 ltn_add2l lt0n.
move=> z zS /andP[lt_yz lt_zx]; case: (ih z) => //.
+ by rewrite rkxE leq_subCl addnK; apply: homo_rank_lt.
+ by rewrite (lt_trans gt0_y lt_yz) lt_zx.
by move=> t [tS lt_tx <-]; exists t.
Qed.
End GradedRankS.

(* -------------------------------------------------------------------- *)
Section FMorphismRank.

Context (T : choiceType) (L : {preLattice T}) (S1 S2 : {finLattice L}).
Context (f : {fmorphism S1 >-> S2}) (rk1 : {rank S1}) (rk2 : {rank S2}).

Lemma rank_morph x :
  x \in S1 -> {in S1&, injective f} ->  (rk1 x <= rk2 (f x))%N.
Proof.
move=> + inj_f; move: x; apply: (rank_ind rk1) => x xS1 ih.
case: (x =P \fbot_S1) => [->|]; first by rewrite rank0.
move/eqP; rewrite -(rank_eq0 rk1) // -lt0n => /graded_rankS -/(_ xS1).
case=> y [yS1 lt_yx <-]; apply: (leq_ltn_trans (ih _ _ _)) => //.
+ by apply: homo_rank_lt.
apply/homo_rank_lt; try by apply/fmorph_premeet_closed.
by apply/(inj_homo_lt_in inj_f (fmorph_homo f)).
Qed.
End FMorphismRank.

(* -------------------------------------------------------------------- *)
Section Atomistic.
Context (T : choiceType) (L : {preLattice T}) (S : {finLattice L}).

Definition atomistic_r (a : S) :=
  [exists A : {fset S},
       [forall x in A, atom S (val x)]
    && (a == (\big[join S/bottom (S)]_(x in A) x))].

Definition atomistic (a : T) :=
  if @idP (a \in S) is  ReflectT h then atomistic_r [` h] else false.

Definition coatomistic_r (a : S) :=
  [exists A : {fset S},
       [forall x in A, coatom S (val x)]
    && (a == (\big[meet S/top S]_(x in A) x))].

Definition coatomistic (a : T) :=
  if @idP (a \in S) is  ReflectT h then coatomistic_r [` h] else false.
End Atomistic.
