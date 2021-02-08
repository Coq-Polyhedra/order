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

Lemma premeet_min_r L S:
  {in S &, forall x y, premeet L S x y <=_L x /\ premeet L S x y <=_L y}.
Proof. exact: (PreLattice.premeet_min (mixin L)). Qed.

Lemma premeet_minl L S:
  {in S &, forall x y, premeet L S x y <=_L x}.
Proof. by move=> x y xS yS; case: (PreLattice.premeet_min (mixin L) xS yS). Qed.

Lemma premeet_minr L S:
  {in S &, forall x y, premeet L S x y <=_L y}.
Proof. by move=> x y xS yS; case: (PreLattice.premeet_min (mixin L) xS yS). Qed.

Definition premeet_min := (premeet_minl, premeet_minr).

Lemma premeet_inf L S:
  {in S & &, forall x y z, z <=_L x -> z <=_L y -> z <=_L premeet L S x y}.
Proof. exact: (PreLattice.premeet_inf (mixin L)). Qed.

Lemma premeet_incr L S S': S `<=` S' ->
  {in S &, forall x y, premeet L S x y <=_L premeet L S' x y}.
Proof. move=> ?????; exact: (PreLattice.premeet_incr (mixin L)). Qed.

Lemma prejoin_max_r L S:
  {in S &, forall x y, prejoin L S x y <=_(L^~) x /\ prejoin L S x y <=_(L^~) y}.
Proof. exact: (PreLattice.prejoin_max (mixin L)). Qed.

Lemma prejoin_maxl L S:
  {in S &, forall x y, prejoin L S x y <=_(L^~) x}.
Proof. by move=> x y xS yS; case: (PreLattice.prejoin_max (mixin L) xS yS). Qed.

Lemma prejoin_maxr L S:
  {in S &, forall x y, prejoin L S x y <=_(L^~) y}.
Proof. by move=> x y xS yS; case: (PreLattice.prejoin_max (mixin L) xS yS). Qed.

Definition prejoin_max := (prejoin_maxl, prejoin_maxr).

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

Definition fmeet (S : finLattice) := (premeet L S).
Definition fjoin (S : finLattice) := (prejoin L S).

Lemma finlattice_eqP (S S' : finLattice) :
  S =i S' <-> S = S'.
Proof. by split => [eq |-> //];apply/val_inj/fsetP. Qed.

End FinLattice.

Notation "{ 'finLattice' L }" := (finLattice L) (at level 0, format "{ 'finLattice'  L }").
Notation "'\fmeet_' S" := (fmeet S) (at level 8, format "'\fmeet_' S").
Notation "'\fjoin_' S" := (fjoin S) (at level 8, format "'\fjoin_' S").

(*Section Test.

Context {T : choiceType} {L : {preLattice T}}.
Context (S1 S2 : finLattice L) (P : T -> Prop).
Goal forall x y z, \fmeet_S1 x y = z <-> premeet L S1 x y = z.
move=> x y z; split; move=> ->.

End Test.*)


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

Context {T : choiceType} {L : {preLattice T}} {S : {finLattice L}}.

Lemma finLattice_prop0 : S != fset0 :> {fset _}.
Proof. by case: S => S0 /= /and3P []. Qed.

Definition witness := [`xchooseP (fset0Pn S finLattice_prop0)].

Lemma mem_meet : forall x y, x \in S -> y \in S -> \fmeet_S x y \in S.
Proof. 
case: S => S0 i x y; rewrite !inE /fmeet /=.
case/and3P: i => /premeet_closedP + _ _; exact.
Qed.

Lemma mem_join : forall x y, x \in S -> y \in S -> \fjoin_S x y \in S.
Proof.
case: S => S0 i x y; rewrite !inE /fjoin /=.
case/and3P: i => _ /premeet_closedP + _; exact.
Qed.

(* ------------------------------------------------------------------ *)

Definition finle (x y : S) := (val x <=_L val y). 
Definition finlt (x y : S) := (val x <_L val y).

Lemma finlexx : reflexive finle.
Proof. by rewrite /finle. Qed.

Lemma finle_anti : forall (x y : S), finle x y -> finle y x -> x = y.
Proof.
move=> x y; rewrite /finle /fun2_val => le1 le2.
apply/val_inj/(@le_anti _ L).
by rewrite le1 le2.
Qed.

Lemma finle_trans : transitive finle.
Proof. move=> y x z; rewrite /finle; exact: le_trans. Qed.

Lemma finlt_def : forall (x y : S), finlt x y = (x != y) && finle x y.
Proof. move=> x y; rewrite /finle /finlt lt_def; congr (_ && _). Qed.

Lemma dfinlt_def : forall (x y : S), finlt y x = (x != y) && finle y x.
Proof. move=> x y; rewrite finlt_def eq_sym; congr (_ && _). Qed.

Definition finle_mixin :=
  POrder.Mixin finlexx finle_anti finle_trans finlt_def dfinlt_def.


(* --------------------------------------------------------------- *)

Definition finmeet (x y : S) := fun2_val witness (\fmeet_S) x y.
Definition finjoin (x y : S) := fun2_val witness (\fjoin_S) x y.

Lemma finmeet_minl : forall x y, finle (finmeet x y) x.
Proof. by move=> x y; rewrite /finle insubdK ?mem_meet ?premeet_minl ?fsvalP. Qed.

Lemma finmeet_minr : forall x y, finle (finmeet x y) y.
Proof. by move=> x y; rewrite /finle insubdK ?mem_meet ?premeet_minr ?fsvalP. Qed.

Lemma finmeet_inf : forall x y z, finle z x -> finle z y ->
  finle z (finmeet x y).
Proof.
move=> x y z; rewrite /finle insubdK ?mem_meet ?fsvalP //.
apply: premeet_inf; exact: fsvalP.
Qed.

Lemma finjoin_maxl : forall x y, finle x (finjoin x y).
Proof.
move=> x y; rewrite /finle insubdK ?mem_join ?fsvalP //.
apply: prejoin_maxl; exact: fsvalP.
Qed.

Lemma finjoin_maxr : forall x y, finle y (finjoin x y).
Proof.
move=> x y; rewrite /finle insubdK ?mem_join ?fsvalP //.
apply: prejoin_maxr; exact: fsvalP.
Qed.

Lemma finjoin_sup : forall x y z, finle x z -> finle y z ->
  finle (finjoin x y) z.
Proof.
move=> x y z; rewrite /finle insubdK ?mem_join ?fsvalP //.
apply: prejoin_sumeet; exact: fsvalP.
Qed.

(* ------------------------------------------------------------------ *)

Lemma finmeetC : commutative finmeet.
Proof.
by move=> x y; apply/finle_anti; 
  rewrite finmeet_inf ?finmeet_minl ?finmeet_minr.
Qed.

Lemma finmeetAl : forall (x y z t : S), t \in [fset x; y; z] ->
  finle (finmeet x (finmeet y z)) t.
Proof.
move=> x y z t; rewrite !in_fsetE; case/orP => [/orP []|] /eqP ->  /=.
+ exact: finmeet_minl.
+ exact/(finle_trans _ (finmeet_minl y z))/finmeet_minr.
+ exact/(finle_trans _ (finmeet_minr y z))/finmeet_minr.
Qed.

Lemma finmeetAr : forall (x y z t : S), t \in [fset x; y; z] ->
  finle (finmeet (finmeet x y) z) t.
Proof.
move=> x y z t; rewrite !in_fsetE; case/orP => [/orP []|] /eqP -> /=.
+ exact/(finle_trans _ (finmeet_minl x y))/finmeet_minl.
+ exact/(finle_trans _ (finmeet_minr x y))/finmeet_minl.
+ exact:finmeet_minr.
Qed.

Lemma finmeetA : associative finmeet.
Proof.
by move=> x y z; apply: finle_anti;
rewrite !finmeet_inf ?finmeetAr ?finmeetAl ?in_fsetE ?eq_refl ?orbT.
Qed.

Lemma lefinmeet : forall x y : S, finle x y = (finmeet x y == x).
Proof.
move=> x y; apply/(sameP idP)/(iffP idP).
- move/eqP => <-; exact: finmeet_minr.
- by move=> xley; apply/eqP/finle_anti;
  rewrite ?finmeet_minl ?finmeet_inf ?finlexx.
Qed.

Definition finmeet_mixin := Meet.Mixin finmeetC finmeetA lefinmeet.
Definition finmeet_class := Meet.Class finle_mixin finmeet_mixin.

(* ----------------------------------------------------------------- *)

Lemma finjoinC : commutative finjoin.
Proof.
by move=> x y; apply: finle_anti;
  rewrite finjoin_sup ?finjoin_maxl ?finjoin_maxr.
Qed.

Lemma finjoinAl : forall (x y z t : S), t \in [fset x; y; z] ->
  finle t (finjoin x (finjoin y z)).
Proof.
move=> x y z t; rewrite !in_fsetE; case/orP => [/orP []|] /eqP ->.
- exact: finjoin_maxl.
- exact/(finle_trans (finjoin_maxl y z))/finjoin_maxr.
- exact/(finle_trans (finjoin_maxr y z))/finjoin_maxr.
Qed.

Lemma finjoinAr : forall (x y z t : S), t \in [fset x; y; z] ->
  finle t (finjoin (finjoin x y) z).
Proof.
move=> x y z t; rewrite !in_fsetE; case/orP => [/orP []|] /eqP ->.
- exact/(finle_trans (finjoin_maxl x y))/finjoin_maxl.
- exact/(finle_trans (finjoin_maxr x y))/finjoin_maxl.
- exact:finjoin_maxr.
Qed.

Lemma finjoinA : associative finjoin.
Proof.
by move=> x y z; apply: finle_anti;
  rewrite ?finjoin_sup ?finjoinAl ?finjoinAr ?in_fsetE ?eq_refl ?orbT.
Qed.

Lemma lefinjoin : forall x y : S, dual_rel finle x y = (finjoin x y == x).
Proof.
move=> x y; apply/(sameP idP)/(iffP idP).
- move/eqP => <-; exact: finjoin_maxr.
- by move=> ylex; apply/eqP/finle_anti;
  rewrite ?finjoin_maxl ?finjoin_sup ?finlexx.
Qed.

Definition finjoin_mixin := Meet.Mixin finjoinC finjoinA lefinjoin.
Definition finLattice_class := Lattice.Class finmeet_class finjoin_mixin.
Definition finLattice_pack := Lattice.Pack (Phant _) finLattice_class.

End FinLatticeStructure.
Module Exports.
Coercion finLattice_pack : finLattice >-> Lattice.order.
Canonical finLattice_pack.
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

Lemma fmeetE L (S : {finLattice L}) :
  \fmeet_S =2 premeet L S.
Proof. by []. Qed.

Lemma fjoinE L (S : {finLattice L}) :
  \fjoin_S =2 prejoin L S.
Proof. by []. Qed.

Lemma mem_fmeet L (S : {finLattice L}) : {in S &, forall x y, \fmeet_S x y \in S}.
Proof.
move=> x y; case: S => S premeet_closeds; rewrite !inE fmeetE /= => xS yS.
by case/andP: premeet_closeds => /premeet_closedP/(_ x y xS yS).
Qed.

Lemma mem_fjoin L (S: {finLattice L}): {in S &, forall x y, \fjoin_S x y \in S}.
Proof. exact: (@mem_fmeet _ S^~s). Qed.

Lemma finLattice_prop0 L (S : {finLattice L}): S != fset0 :> {fset _}.
Proof. by case: S => S /= /and3P []. Qed.

Lemma finLattice_leE L (S : {finLattice L}) : forall x y : S,
  x <=_S y = fsval x <=_L fsval y.
Proof. by []. Qed.

Lemma finLattice_meetE L (S : {finLattice L}) : forall x y : S,
  fsval (meet S x y) = \fmeet_S (fsval x) (fsval y).
Proof. by move=> x y; rewrite insubdK ?mem_fmeet ?fsvalP. Qed.

Lemma finLattice_joinE L (S : {finLattice L}) : forall x y : S,
  fsval (join S x y) = \fjoin_S (fsval x) (fsval y).
Proof. by move=> x y; rewrite insubdK ?mem_fjoin ?fsvalP. Qed.

(*Goal forall L, forall S : {finLattice L}, forall x y, join S x y = meet (S^~s) x y.
Proof. by move=> L S x y; apply/val_inj; rewrite !insubdK ?mem_fmeet ?fsvalP.*)

Section FMeetTheory.

Lemma leIfl L (S : {finLattice L}) : {in S &, forall x y, \fmeet_S x y <=_L x}.
Proof. 
apply: sub_pred2 => x y; move: (@leIl _ S x y).
by rewrite finLattice_leE finLattice_meetE.
Qed.


Lemma leIfr L (S : {finLattice L}) : {in S &, forall x y, \fmeet_S y x <=_L x}.
Proof.
apply: sub_pred2 => x y; move: (@leIr _ S x y).
by rewrite finLattice_leE finLattice_meetE.
Qed.

Lemma lefI L (S : {finLattice L}) :
  {in S & &, forall x y z, (x <=_L \fmeet_S y z) = (x <=_L y) && (x <=_L z)}.
Proof.
apply: sub_pred3 => x y z; move: (@lexI _ S x y z).
by rewrite !finLattice_leE finLattice_meetE. 
Qed.

Lemma fmeetC L (S : {finLattice L}) : {in S &, commutative (\fmeet_S)}.
Proof.
apply: sub_pred2=> x y; move: (@meetC _ S x y).
by move/(@congr1 _ _ (@fsval _ S)); rewrite !finLattice_meetE.
Qed.

Lemma lefIl L (S : {finLattice L}) :
  {in S & &, forall x y z, y <=_L x -> \fmeet_S y z <=_L x}.
Proof.
apply: sub_pred3 => x y z; move: (@leIxl _ S x y z).
by rewrite !finLattice_leE !finLattice_meetE.
Qed.

Lemma lefIr L (S : {finLattice L}) :
  {in S & &, forall x y z, z <=_L x -> \fmeet_S y z <=_L x}.
Proof. move=> x y z xS yS zS zlex; rewrite fmeetC //; exact: lefIl. Qed.

Lemma fmeetA L (S : {finLattice L}) : {in S & &, associative (\fmeet_S) }.
Proof.
apply: sub_pred3=> x y z; move:(@meetA _ S x y z).
by move/(@congr1 _ _ (@fsval _ S)); rewrite !finLattice_meetE.
Qed.

Lemma fmeetxx L (S : {finLattice L}) : {in S, idempotent (\fmeet_S)}.
Proof.
apply: sub_pred1=> x; move:(@meetxx _ S x).
by move/(@congr1 _ _ (@fsval _ S)); rewrite finLattice_meetE.
Qed.

Lemma leEfmeet L (S : {finLattice L}) :
  {in S &, forall x y, (x <=_L y) = (\fmeet_S x y == x)}.
Proof.
apply: sub_pred2 => x y; move:(@leEmeet _ S x y).
by rewrite finLattice_leE -val_eqE /= finLattice_meetE.
Qed.

Lemma fmeetAC L (S : {finLattice L}) :
  {in S & &, right_commutative (\fmeet_S)}.
Proof.
apply: sub_pred3=> x y z; move:(@meetAC _ S x y z).
by move/(@congr1 _ _ (@fsval _ S)); rewrite !finLattice_meetE.
Qed.

Lemma fmeetCA L (S : {finLattice L}) :
  {in S & &, left_commutative (\fmeet_S)}.
Proof.
apply: sub_pred3=> x y z; move:(@meetCA _ S x y z).
by move/(@congr1 _ _ (@fsval _ S)); rewrite !finLattice_meetE.
Qed.


Lemma fmeetACA L (S : {finLattice L}) x y z t:
  x \in S -> y \in S -> z \in S -> t \in S ->
  \fmeet_S (\fmeet_S x y) (\fmeet_S z t) =
  \fmeet_S (\fmeet_S x z) (\fmeet_S y t).
Proof.
move=> xS yS zS tS; move:(@meetACA _ S [`xS] [`yS] [`zS] [`tS]).
by move/(@congr1 _ _ (@fsval _ S)); rewrite ?finLattice_meetE.
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
Proof. 
move=> xS yS zS tS; move:(@leI2 _ S [`xS] [`yS] [`zS] [`tS]).
by rewrite !finLattice_leE !finLattice_meetE.
Qed.

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

Lemma ftop_def L (S : {finLattice L}) x0 :
  x0 \in S -> \ftop_S = \big[\fjoin_S/x0]_(x <- S) x.
Proof. exact: (@fbot_def _ S^~s). Qed.

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

Lemma fmeet0f L (S : {finLattice L}) :
  {in S, left_zero \fbot_S \fmeet_S}.
Proof. by move=> x xS; apply/eqP; rewrite -leEfmeet ?le0f ?mem_fbot. Qed.

Lemma fmeetf0 L (S : {finLattice L}) :
  {in S, right_zero \fbot_S \fmeet_S}.
Proof. by move=> x xS; apply/eqP; rewrite fmeetC -?leEfmeet ?le0f ?mem_fbot. Qed.

Lemma fjoin1f L (S : {finLattice L}) :
  {in S, left_zero \ftop_S \fjoin_S}.
Proof. exact: (@fmeet0f _ S^~s). Qed.

Lemma fjoinf1 L (S : {finLattice L}) :
  {in S, right_zero \ftop_S \fjoin_S}.
Proof. exact: (@fmeetf0 _ S^~s). Qed.

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

Definition finbot := [`mem_fbot S].
Lemma finbot_mixin : BPOrder.mixin_of (<=:S) finbot.
Proof. move=> x; exact/le0f/fsvalP. Qed.

Definition BSLattice_class :=
  BLattice.Class FinLatticeStructure.finLattice_class finbot_mixin.

Definition fintop := [`mem_ftop S].
Lemma fintop_mixin : TPOrder.mixin_of (<=:S) fintop.
Proof. move=> x; exact/lef1/fsvalP. Qed.

Definition TBfinLattice_class :=
  TBLattice.Class BSLattice_class fintop_mixin.
Definition TBfinLattice_pack :=
  TBLattice.Pack (Phant _) (TBfinLattice_class).

End FinTBLatticeStructure.
Module Exports.
Coercion TBfinLattice_pack : finLattice >-> TBLattice.order.
Canonical TBfinLattice_pack.
Notation finbot := finbot.
Notation fintop := fintop.
End Exports.

End FinTBLatticeStructure.
Include FinTBLatticeStructure.Exports.

Section TestTBFinLattice.

Context {T : choiceType} {L : {preLattice T}} {S : {finLattice L}}.
Context (a : S).
Context (I : Type) (F : I -> S).
Context (P : pred I).

(*Goal forall (r : seq I),
\big[\fmeet_S / \ftop_S]_(i <- r | P i) F i =
(val (\big[meet S / top S]_(i <- r | P i) insubd a (F i))).
Proof.
move=> r; rewrite (big_val a) /vop /vx0 /fun2_val.
- move=> x y z; apply/val_inj.
  by rewrite ?insubdK ?mem_fmeet ?fmeetA ?fsvalP.
- move=> x; apply/val_inj.
  by rewrite !insubdK ?mem_fmeet ?mem_ftop ?fmeet1f ?fsvalP.
- move=> x; apply/val_inj.
  by rewrite !insubdK ?mem_fmeet ?mem_ftop ?fmeetf1 ?fsvalP.
- move=> opA op1x opx1 x y; apply/val_inj.
  rewrite ?insubdK ?mem_fmeet ?fsvalP //; apply: fmeetC; exact: fsvalP.
- move=> opA op1x opx1 opC; congr fsval.
  have eq_idx: insubd a \ftop_S = top S by
    apply/val_inj; rewrite !insubdK ?mem_ftop.
  rewrite {1}eq_idx; apply: (eq_big_op (fun x => val x \in S)).
    + exact: mem_ftop.
    + by move=> x y xS yS; rewrite insubdK ?mem_fmeet.
    + by move=> x y xS yS; apply/val_inj; rewrite !insubdK ?mem_fmeet.
    + by move=> i Pi; rewrite insubdK ?FS.
- exact: mem_ftop.
- exact: mem_fmeet.
- exact: FS.
Qed.*)

Goal forall (r : seq I),
  val (\big[meet S / top S]_(i <- r | P i) F i) =
  \big[\fmeet_S / \ftop_S]_(i <- r | P i) val (F i).
Proof.
move=> r0; rewrite big_val_foo /=.
have ->: fsval (top S) = \ftop_S by [].
rewrite (eq_big_op (fun x => x \in S) \fmeet_S) ?mem_ftop //.
- move=> ????; exact:fsvalP.
- by move=> x y xS yS; rewrite /val_fun2 !insubdK ?mem_fmeet.
- move=> ??; exact: fsvalP.
Qed.

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
- by apply:(le_trans _ xleb); rewrite premeet_min.
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
    rewrite premeet_min.
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

Section UmeetDjoin.

Lemma mem_umeet L (S : {finLattice L}) a: umeet S a \in S.
Proof. exact: Interval.mem_umeet. Qed.

Lemma mem_djoin L (S : {finLattice L}) b: djoin S b \in S.
Proof. exact: Interval.mem_djoin. Qed.

Lemma umeetE L (S : {finLattice L}) a: a \in S -> umeet S a = a.
Proof. exact: Interval.umeetE. Qed.

Lemma djoinE L (S : {finLattice L}) b: b \in S -> djoin S b = b.
Proof. exact: Interval.djoinE. Qed.

Lemma le_umeet L (S : {finLattice L}) a b :
  b \in S -> a <=_L b -> umeet S a <=_L b.
Proof.
by move=> bS aleb; apply: fmeet_inf_seq.
Qed.

Lemma le_djoin L (S : {finLattice L}) a b :
  a \in S -> a <=_L b -> djoin S b >=_L a.
Proof.
by move=> aS aleb; apply: fjoin_sumeet_seq.
Qed.

End UmeetDjoin.

Lemma fmeet_itvE L (S : {finLattice L}) a b :
  {in [<a; b>]_S &, \fmeet_([< a ; b >]_S) =2 \fmeet_S}.
Proof. by move => x y x_in y_in; rewrite fmeetE -Interval.premeet_itvE. Qed.

Lemma fjoin_itvE L (S : {finLattice L}) a b :
  {in [<a; b>]_S &, \fjoin_([< a ; b >]_S) =2 \fjoin_S}.
Proof. by move => x y x_in y_in; rewrite fjoinE -Interval.prejoin_itvE. Qed.

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
Proof.
move=> aS aleb /itv_bigrange /andP [+ _].
by rewrite (umeetE aS) (fmeet_l aS (mem_djoin S b) (le_djoin aS aleb)).
Qed.

Lemma itv_leR L (S: {finLattice L}) a b x :
  b \in S -> a <=_L b -> x \in [< a ; b >]_S -> x <=_L b.
Proof.
move=> bS aleb /itv_bigrange /andP [_].
by rewrite (djoinE bS) (fjoin_r (mem_umeet S a) bS (le_umeet bS aleb)).
Qed.
(*Proof. by move=> bS; rewrite !inE Interval.join_bar // => /and3P []. Qed.*)

Lemma itv_id L (S: {finLattice L}) : [<\fbot_S; \ftop_S>]_S = S.
Proof.
apply/eqP/fset_eqP => x.
rewrite !inE; apply: andb_idr => xS.
rewrite ?Interval.umeetE ?Interval.djoinE ?mem_ftop ?mem_fbot //.
by rewrite fmeet_l ?fjoin_r ?le0f ?lef1 ?mem_fbot.
Qed.

Lemma mono_itv L (S : {finLattice L}) (A B a b : T) :
  A \in S -> B \in S -> A <=_L B ->
  a \in [< A; B >]_S -> b \in [<A ; B >]_S -> a <=_L b ->
  [< a; b >]_[< A; B >]_S = [< a; b >]_S.
Proof.
move=> AS BS AleB; rewrite intervalE // => /and3P [aS Alea aleB].
rewrite intervalE // => /and3P [bS Aleb bleB] aleb.
apply/eqP/fset_eqP => z; apply/(sameP idP)/(iffP idP).
- case/intervalP => // zS /andP [alez zleb]; rewrite !mem_itv //.
  + exact: (le_trans Alea).
  + exact: (le_trans zleb).
- case/intervalP => //;
    rewrite !intervalE ?aS ?Alea ?aleB ?bS ?Aleb ?bleB //.
  by case/andP => -> _ /andP [-> ->].
Qed.

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
Proof. by move=> yS; rewrite mem_itv ?le0f ?mem_fbot. Qed.


Lemma mem_itv1 L (S : {finLattice L}) (x : T) :
  x \in S -> \ftop_S \in [< x; \ftop_S >]_S.
Proof.
have -> : S = (S^~s)^~s by exact/val_inj.
rewrite -dual_itv => ?. exact: mem_0itv.
Qed.

Lemma itvE0 L (S : {finLattice L}) :
  {in S &, forall a b, a <=_L b -> \fbot_([<a; b>]_S) = a}.
Proof.
move=> a b aS bS aleb; apply: fbot_id; rewrite ?mem_itv //.
move=> x; exact: itv_geL.
Qed.


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
Proof.
set S' := ([< \fbot_S; x >]_S `\` [fset \fbot_S; x]).
move=> xS botltx.
case/boolP: (S' == fset0).
- rewrite fsetD_eq0 => /fsubsetP intv_sub.
  exists x => //; apply/atomP; rewrite xS botltx; split=> //.
  move=> y yS; apply: contraTN => yltx.
  have/intv_sub : y \in [< \fbot_S; x >]_S by
    rewrite mem_itv ?le0f ?(ltW yltx).
  by rewrite !inE (lt_eqF yltx) orbF; move/eqP => ->; rewrite ltxx.
- case/(minset_neq0 L)/fset0Pn => y /mem_minsetE.
  rewrite in_fsetD intervalE ?mem_fbot //; [|rewrite le0f //].
  case => /and3P [].
  rewrite !inE negb_or => /andP [ynbot ynx] yS /andP [boty ylex] miny.
  exists y=> //.
  apply/atomP; rewrite yS lt_neqAle boty eq_sym ynbot; split => //.
  move=> z zS botltz; apply: contraT; rewrite negbK => zlty.
  suff/miny: z \in S' by rewrite zlty.
  rewrite in_fsetD intervalE ?le0f ?zS ?mem_fbot //= ?inE.
  rewrite negb_or eq_sym (lt_eqF botltz).
  have zltx := (lt_le_trans zlty ylex).
  by rewrite (lt_eqF zltx) (ltW zltx).
Qed.

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
move=> xS PS.
move: {2}#|`_| (leqnn #|`[< \fbot_S; x >]_S|) => n.
elim: n S xS PS => [|n ih] S xS PS.
- rewrite leqn0 => /eqP /cardfs0_eq /(congr1 (fun S => x \in S)).
  by rewrite in_fset0 intervalE ?le0f ?lexx
    ?mem_fbot ?xS.
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
  rewrite intervalE ?ylex ?lef1 ?mem_ftop ?xS ?yS.
move/ih => /(_ (P_incr atom_Sy PS)).
rewrite !(itvE0, itvE1) ?mem_ftop ?lef1 //.
rewrite !mono_itv ?mem_itv1 ?mem_itvL
  ?intervalE ?yS ?mem_ftop ?xS ?ylex ?lef1 //.
apply.
rewrite -ltnS; pose X := \fbot_S |` [< \fbot_S; x >]_S `\ \fbot_S.
apply: (@leq_trans #|`X|); last by rewrite /X fsetD1K // mem_0itv.
apply: fproper_ltn_card; rewrite {}/X.
rewrite fsetD1K ?mem_0itv //.
apply: (@fsub_proper_trans _ ([< \fbot_S; x >]_S `\ \fbot_S)); last first.
- by apply/fproperD1; rewrite mem_0itv.
apply/fsubsetD1P; split.
- rewrite sub_itv ?le0f ?mem_fbot ?xS ?yS //=.
apply: contraL atom_Sy; rewrite intervalE //.
case/and3P => _ ylebot _; apply/negP => /atomP[].
by rewrite (le_gtF ylebot).
Qed.
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
Proof.
move=> xS yS xley PS; have h: P [< x; \ftop_S >]_S by apply: ind_incr.
have Sprop0 : S != fset0 :> {fset _} by apply/fset0Pn; exists x.
suff: P [< \fbot_[< x; \ftop_S >]_S; y >]_[< x; \ftop_S >]_S.
  rewrite itvE0 ?mono_itv ?andbT ?mem_itvL ?intervalE
    ?yS ?xley ?mem_ftop ?lef1 //.
by apply: ind_decr; rewrite ?intervalE // ?xley ?lef1 ?yS ?mem_ftop.
Qed.
End Ind.

End IntervalTheory.

(* -------------------------------------------------------------------- *)
Module Morphism.
Section ClassDef.
Context (T : choiceType) (L : {preLattice T}) (S: {fset T}).

Definition axiom (f : T -> T) :=
  {in S&, {morph f : x y / premeet L S x y >-> premeet L (f @` S) x y}}
  /\ {in S&, {morph f : x y / prejoin L S x y >-> prejoin L (f @`S) x y}}.

Structure map (phS : phant S) :=
  Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.

Context (phS : phant S).
Context (f g : T -> T) (cF : map phS).

Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phS f fA.
End ClassDef.

Module Exports.
Notation fmorphism f := (axiom f).
Coercion apply : map >-> Funclass.
Notation FMorphism fM := (Pack (Phant _) fM).
Notation "{ 'fmorphism' S 'on' L }" := (map L (Phant S))
  (at level 0, L at level 0, format "{ 'fmorphism'  S  'on'  L }").
End Exports.
End Morphism.

Include Morphism.Exports.

(* -------------------------------------------------------------------- *)

Section FinLatticeMorphism.

Context {T : choiceType} {L : {preLattice T}}.
Context {S : {finLattice L}} (f : {fmorphism S on L}).

Notation finLatImg := (f @`(S : {fset _})).

Lemma finLatImg_prop0 : finLatImg != fset0.
Proof. 
case/fset0Pn : (finLattice_prop0 S) => x xS; apply/fset0Pn; exists (f x).
exact: in_imfset.
Qed.

Lemma fmorph_premeet :
  {in S&, {morph f : x y / premeet L S x y >-> premeet L finLatImg x y}}.
Proof. by case: f => ? []. Qed.

Lemma fmorph_prejoin :
  {in S&, {morph f : x y / prejoin L S x y >-> prejoin L finLatImg x y}}.
Proof. by case: f => ? []. Qed.


Lemma finLatImg_premeet_closed : premeet_closed L finLatImg.
Proof.
apply/premeet_closedP => x y /imfsetP + /imfsetP.
case => x' x'S -> [y' y'S ->].
rewrite -fmorph_premeet ?in_imfset //.
exact : (mem_fmeet x'S y'S).
Qed.

Lemma finLatImg_prejoin_closed : premeet_closed (L^~pl) finLatImg.
Proof.
apply/premeet_closedP => x y /imfsetP + /imfsetP /=.
case => x' x'S -> [y' y'S ->].
rewrite -fmorph_prejoin ?in_imfset //.
exact : (mem_fjoin x'S y'S).
Qed.

Lemma finLatImg_finLat :
  [&& premeet_closed L finLatImg,
  premeet_closed (L^~pl) finLatImg &
  finLatImg != fset0].
Proof.
by rewrite finLatImg_prop0 finLatImg_premeet_closed
  finLatImg_prejoin_closed.
Qed.

Canonical finLatImg_finLattice := FinLattice finLatImg_finLat.

End FinLatticeMorphism.

Notation "'\codom' f" := (@finLatImg_finLattice _ _ _ f)
  (at level 24, format "'\codom'  f").

Section MorphismTheory.
Context (T : choiceType).

Implicit Type (L : {preLattice T}).

Lemma fmorphismP L (S : {fset T}) (f : {fmorphism S on L}) :
  fmorphism L S f.
Proof. by case : f. Qed.


Lemma fmorphI L (S : {finLattice L}) (f : {fmorphism S on L}) :
  {in S &, {morph f : x y / \fmeet_S x y >-> \fmeet_(\codom f) x y}}.
Proof. by case: (fmorphismP f). Qed.

Lemma fmorphU L (S : {finLattice L}) (f : {fmorphism S on L}) :
  {in S &, {morph f : x y / \fjoin_S x y >-> \fjoin_(\codom f) x y}}.
Proof. by case: (fmorphismP f). Qed.

Lemma codomP L (S1 S2 : {finLattice L}) (f : {fmorphism S1 on L}) :
  f @` (S1 : {fset _}) = S2 -> \codom f = S2.
Proof. move=> ?; exact: val_inj. Qed.

(* ------------------------------------------------------------------- *)

(*Lemma meet_morph_homo L (S: {finLattice L}) f :
  {in S &, {morph f : x y / premeet L S x y >->
    premeet L (f @` (S : {fset _})) x y}} ->
  {in S &, {homo f : x y / x <=_L y}}.
Proof.
move=> f_morph x y xS yS xley.
suff <-: premeet L (f @` (S : {fset _})) (f x) (f y) = f x by
  rewrite premeet_minr // in_imfset.
rewrite -f_morph //; congr f; apply: (le_anti L).
by rewrite premeet_minl ?premeet_inf.
Qed.

Lemma meet_morph_mono L (S : {finLattice L}) f :
  {in S &, {morph f : x y / premeet L S x y >->
    premeet L (f @` (S : {fset _})) x y}} ->
  {in S &, injective f} -> {in S &, {mono f : x y / x <=_L y}}.
Proof.
move=> f_morph f_inj x y xS yS.
apply/(sameP idP)/(iffP idP); first exact: (meet_morph_homo f_morph).
move=> fxlefy.
suff: premeet L (f @` (S : {fset _})) (f x) (f y) == (f x).
- rewrite -f_morph ?(inj_in_eq f_inj) ?(mem_fmeet xS) //.
  move/eqP => <-; exact: premeet_minr.
by apply/eqP/(le_anti L); rewrite premeet_minl ?premeet_inf ?in_imfset.
Qed.

Lemma meet_fmorphism L (S : {finLattice L}) f :
  {in S &, {morph f : x y / premeet L S x y >->
    premeet L (f @` (S : {fset _})) x y}} ->
  {in S &, injective f} -> fmorphism L S f.
Proof.
move=> f_morph f_inj; rewrite /(fmorphism _).
have f_mono := (meet_morph_mono f_morph f_inj).
split; first exact: f_morph.
move=> x y xS yS; apply/(le_anti L)/andP; split.
Admitted.

(*Lemma meet_fmorphism L (S1 S2 : {finLattice L}) (f : T -> T) :
  {in S1, forall x, f x \in S2} ->
  {in S1&, {morph f : x y / \fmeet_S1 x y >-> \fmeet_S2 x y}} ->
  {in S1 & on S2, bijective f} -> fmorphism L S1 S2 f.
Proof.
move=> f_im f_morph [g] [g_im fgK gfK].
have f_mono := (meet_morph_mono f_im f_morph (can_in_inj fgK)).
split => //.
move=> x y xS yS.
apply/(le_anti L)/andP; split.
- rewrite -[X in (_ <=__ X)]gfK ?f_mono ?leUf ?g_im ?mem_fjoin ?f_im //.
  rewrite -f_mono ?g_im ?mem_fjoin ?f_im //.
  rewrite -[X in _ && X]f_mono ?g_im ?mem_fjoin ?f_im //.
  by rewrite gfK ?lefUl ?lefUr ?mem_fjoin ?f_im.
- by rewrite leUf ?f_mono ?lefUl ?lefUr ?f_im ?mem_fjoin.
(*+ apply/(le_anti L)/andP; split; rewrite ?le0f ?f_im ?mem_fbot //.
  by rewrite -[X in (_ <=__ X)]gfK ?f_mono ?le0f ?g_im ?mem_fbot.
+ apply/(le_anti L)/andP; split; rewrite ?lef1 ?f_im ?mem_fbot //.
  by rewrite -[X in (X <=__ _)]gfK ?f_mono ?lef1 ?g_im ?mem_fbot.*)
Qed.*)

Lemma dual_fmorphism L (S : {finLattice L}) (f : T -> T) :
  fmorphism L S f <-> fmorphism L S^~s f.
Proof. by split; case; split. Qed.

Lemma join_fmorphism L (S : {finLattice L}) (f : T -> T) :
  {in S &, {morph f : x y / prejoin L S x y >->
    prejoin L (f @` (S : {fset _})) x y}} ->
  {in S &, injective f} -> fmorphism L S f.
Proof.
move=> morph_join inj; apply/dual_fmorphism.
by move: (@meet_fmorphism _ S^~s f) => /(_ morph_join inj) [].
Qed.*)

(* ----------------------------------------------------------------- *)
(*Context (L : {preLattice T}) (S : {finLattice L}).
Context (f g : {fmorphism S on L}).*)



Lemma fmorph0 L (S : {finLattice L}) (f : {fmorphism S on L}):
  f \fbot_S = \fbot_(\codom f).
Proof.
symmetry; apply: fbot_id; first exact/in_imfset/mem_fbot.
move=> y /imfsetP [x xS ->].
have fxfS: f x \in (\codom f) by rewrite in_imfset.
by rewrite (leEfmeet _ fxfS) ?in_imfset -?fmorphI ?mem_fbot ?fmeet0f.
Qed.

Lemma fmorph1 L (S : {finLattice L}) (f : {fmorphism S on L}):
  f \ftop_S = \ftop_(\codom f).
Proof.
symmetry; apply: ftop_id; first exact/in_imfset/mem_fbot.
move=> y /imfsetP [x xS ->].
have fxfS: f x \in (\codom f) by rewrite in_imfset.
by rewrite (leEfmeet fxfS) ?in_imfset -?fmorphI ?mem_ftop ?fmeetf1.
Qed.

Lemma fmorph_homo L (S : {finLattice L}) (f : {fmorphism S on L}):
  {in S&, {homo f : x y / x <=_L y}}.
Proof.
move=> x y xS yS; rewrite (leEfjoin xS) // => /eqP.
move/(congr1 f); rewrite fmorphU // => <-.
by apply/lefUr; rewrite in_imfset.
Qed.

Lemma fmorph_mono L (S : {finLattice L}) (f : {fmorphism S on L}):
  {in S&, injective f} -> {in S&, {mono f : x y / x <=_L y}}.
Proof.
move=> f_inj x y xS yS; rewrite (leEfjoin xS) //.
rewrite (@leEfjoin _ _ (\codom f)) ?in_imfset //.
by rewrite -fmorphU //; apply/(inj_in_eq f_inj)=> //; apply: mem_fjoin.
Qed.

Lemma fmorph_monolt L (S : {finLattice L}) (f : {fmorphism S on L}):
  {in S&, injective f} -> {in S&, {mono f : x y / x <_L y}}.
Proof.
move=> f_inj x y xS yS; rewrite !lt_def; congr (_ && _).
- apply/(sameP idP)/(iffP idP); first exact/contra_neq/f_inj.
  by apply/contra_neq => ->.
- exact: fmorph_mono.
Qed.

Lemma mem_fmorphP L (S : {finLattice L}) (f : {fmorphism S on L}) x:
  reflect (exists2 y, y \in S & f y = x) (x \in (\codom f)).
Proof.
apply/(iffP idP).
- by case/imfsetP => y /= yS ->; exists y.
- by case => y yS <-; rewrite in_imfset.
Qed.

Lemma mem_fmorph L (S : {finLattice L}) (f : {fmorphism S on L}) x:
  x \in S -> f x \in (\codom f).
Proof. by move=> xS; rewrite in_imfset. Qed.

End MorphismTheory.

Section isoFMorph.

Context {T : choiceType} (L : {preLattice T}).
Context (S1 S2 : {fset T}).

Definition morphic_fmeet (f : T -> T) :=
  [forall x: S1, [forall y : S1,
  f (premeet L S1 (fsval x) (fsval y)) == 
  premeet L (f @` (S1 : {fset _})) (f (fsval x)) (f (fsval y))]].
  
Definition morphic_fjoin (f : T -> T) :=
  [forall x: S1, [forall y : S1,
  f (prejoin L S1 (fsval x) (fsval y)) == 
  prejoin L (f @` (S1 : {fset _})) (f (fsval x)) (f (fsval y))]].

Definition morphic (f : T -> T) := morphic_fmeet f && morphic_fjoin f.

Definition injf (f : T -> T) :=
  [forall x : S1, [forall y : S1,
  (f (fsval x) == f (fsval y)) ==> (fsval x == fsval y)]].

Definition surjf (f : T -> T) := f @` (S1 : {fset _}) == S2.

Definition misof f := [&& morphic f, injf f & surjf f].

(*Definition val_ffun (f : {ffun S1 -> S2}) :=
  fun x : T => fsval (f (insubd [`mem_fbot S1] x)).*)

Definition isof := exists f : T -> T, misof f.

Lemma morphicP (f : T -> T): reflect (fmorphism L S1 f) (morphic f).
Proof.
rewrite /morphic /morphic_fmeet /morphic_fjoin /(fmorphism _).
apply/andPP; apply/(iffP idP).
- move => + x y xS1 yS1.
  by move/forallP => /(_ [`xS1]) /forallP /(_ [`yS1]) /eqP.
- move=> morphmeet; apply/forallP => x; apply/forallP => y.
  by move: (morphmeet _ _ (fsvalP x) (fsvalP y)) => ->.
- move => + x y xS1 yS1.
  by move/forallP => /(_ [`xS1]) /forallP /(_ [`yS1]) /eqP.
- move=> morphjoin; apply/forallP => x; apply/forallP => y.
  by move: (morphjoin _ _ (fsvalP x) (fsvalP y)) => ->.
Qed.

Lemma injfP (f : T -> T): reflect ({in S1&, injective f}) (injf f).
Proof.
apply/(iffP idP).
- move=> f_inj x y xS yS /eqP f_eq.
  move/forallP : f_inj => /(_ [`xS]) /forallP /(_ [`yS]).
  by move/implyP/(_ f_eq)/eqP.
- move=> f_inj; apply/forallP => x; apply/forallP => y; apply/implyP.
  by move/eqP/(f_inj _ _ (fsvalP x) (fsvalP y)) => ->.
Qed.

Lemma misofP (f : T -> T):
  reflect
  ([/\ fmorphism L S1 f, {in S1&, injective f} & f @` (S1 : {fset _}) = S2])
  (misof f).
Proof. apply/and3PP; [exact/morphicP | exact/injfP |exact/eqP]. Qed.

Lemma misof_isof (f : T -> T):
  misof f -> isof.
Proof. by move=> ?; exists f. Qed.

Lemma misof_fmorph (f : {fmorphism S1 on L}) :
  {in S1&, injective f} -> f @` (S1 : {fset _}) = S2 ->
  misof f.
Proof. move=> f_inj f_surj; apply/misofP; split => //; exact: fmorphismP. Qed.


Lemma isofP :
  (exists2 f : {fmorphism S1 on L}, f @` S1 = S2 & {in S1&, injective f}) <->
  (isof).
Proof.
split.
- case => f f_surj f_inj; exists f; apply/misofP; split;
    [exact: (fmorphismP f) | exact: f_inj | exact: f_surj].
- case => f /misofP [fmorph f_inj f_surj].
  by exists (FMorphism fmorph).
Qed.

End isoFMorph.

Section ItvMorph.

Context (T : choiceType).
Implicit Type L : {preLattice T}.

Lemma fmorph_itv L (S : {finLattice L}) (f: {fmorphism S on L}) a b :
  a \in S -> b \in S -> a <=_L b -> {in S&, injective f} ->
  f @` ([< a; b>]_S : {fset _}) = [< f a; f b>]_(\codom f).
Proof.
move=> aS bS aleb f_inj; apply/eqP/fset_eqP => x.
apply/(sameP idP)/(iffP idP).
- rewrite intervalE ?mem_fmorph ?fmorph_homo //.
  case/and3P => /mem_fmorphP [y yS <-] fafy fyfb.
  rewrite in_imfset ?intervalE ?yS //=.
  by rewrite -(fmorph_mono f_inj) ?fafy //= -(fmorph_mono f_inj).
- case/imfsetP => x' /intervalP.
  case/(_ aS bS aleb) => x'S /andP [ax' x'b] ->.
  rewrite intervalE ?mem_fmorph ?fmorph_homo //.
Qed.

(*Lemma fmorph_itv_bij a b :
  a \in S1 -> b \in S1 -> a <=_L b ->
    {in S1 & on S2, bijective f} ->
    {in [<a; b>]_S1 & on [<f a; f b>]_S2, bijective f}.
Proof.
move=> aS1 bS1 a_le_b [f'] [f'_im fK f'K].
exists f'; split.
+ move=> x; case/intervalP; rewrite ?mem_fmorph ?fmorph_homo => // xS2.
  have {-3}->: x = f (f' x) by rewrite f'K.
  rewrite 2?fmorph_mono ?f'_im //; try by apply/(can_in_inj fK).
  by case/andP=>??; apply/mem_itv=>//; exact: f'_im.
+ move=> x /itv_subset /=; exact: fK.
+ move=> x /itv_subset /=; exact: f'K.
Qed.*)

Lemma itv_isomorph L (S1 S2 : {finLattice L})
  (f : {fmorphism S1 on L}) a b:
  a \in S1 -> b \in S1 -> a <=_L b ->
  misof L S1 S2 f ->
  misof L [<a ; b>]_S1 (f @` ([< a ; b >]_S1 : {fset _})) f.
Proof.
move=> aS1 bS1 aleb.
case/misofP => fmorphismf f_inj f_surj.
have f_itv: {in [<a; b>]_S1, forall x, (f x) \in [< f a; f b >]_(\codom f)} by
  move=> x xab; rewrite inE -fmorph_itv //; exact: in_imfset.
apply/misofP; split; first split.
- move=> x y xab yab; rewrite fmorph_itv //.
  rewrite -!fmeetE (fmeet_itvE xab yab) (fmeet_itvE (f_itv _ xab) (f_itv _ yab)).
  by apply/fmorphI; rewrite ?(itv_subset xab) ?(itv_subset yab).
- move=> x y xab yab; rewrite fmorph_itv // -!fjoinE.
  rewrite (fjoin_itvE xab yab) (fjoin_itvE (f_itv _ xab) (f_itv _ yab)).
  by apply/fmorphU; rewrite ?(itv_subset xab) ?(itv_subset yab).
- by move=> x y xab yab /f_inj; move/(_ (itv_subset xab) (itv_subset yab)).
- rewrite fmorph_itv //; apply/eqP/fset_eqP => x.
Qed.

Lemma fmorph_atom L (S1 S2 : {finLattice L})
  (f : {fmorphism S1 on L}) x :
  misof L S1 S2 f -> atom S1 x -> atom S2 (f x).
Proof.
case/misofP => f_morph f_inj f_surj /atomP [xS1 l0tx x_min].
have f_surjS : \codom f = S2 by exact: val_inj.
apply/atomP; split.
- by rewrite inE -f_surj in_imfset.
- move: l0tx; rewrite -f_surjS -fmorph0 !lt_def.
  case/andP => + /(fmorph_homo f (mem_fbot S1) xS1) ->; rewrite andbT.
  by apply/contra_neq/f_inj; rewrite ?mem_fbot.
- rewrite -f_surjS => y /mem_fmorphP [y' y'S1 <-]; rewrite -fmorph0.
  rewrite !fmorph_monolt ?mem_fbot //; exact: x_min.
Qed.


End ItvMorph.


Section BijMorphism.

Context {T : choiceType}.
Implicit Type (L : {preLattice T}).

Lemma isof_refl L (S : {finLattice L}): isof L S S.
Proof.
have idmorph: fmorphism L S id by
  split => x y xS yS /=; rewrite imfset_id.
apply/isofP; exists (FMorphism idmorph) => //=; by rewrite imfset_id.
Qed.

Lemma isof_sym L (S1 S2 : {finLattice L}):
  isof L S1 S2 -> isof L S2 S1.
Proof.
case/isofP => f f_surj f_inj.
have [g]: {in S1& on S2, bijective f}.
  apply: (@inj_surj_bij _ _ _ _ _ (f \fbot_S1)) => //.
  + by rewrite -f_surj in_imfset ?mem_fbot.
  + by move=> ??; rewrite -f_surj in_imfset.
  + by move=> y; rewrite -f_surj; case/imfsetP => x /= xS1 ->; exists x.
case=> gS1 cancel_l cancel_r; exists g.
have gfS1: (g \o f) @` (S1 : {fset _}) = S1.
  apply/eqP/fset_eqP => x; apply/(sameP idP)/(iffP idP).
  + by move=> xS1; apply/imfsetP; exists x => //=; rewrite cancel_l.
  + by case/imfsetP => x0 /= x0S1; rewrite cancel_l // => ->.
apply/misofP; split; first split.
- move=> x y xS2 yS2; apply: f_inj;
    rewrite ?gS1 ?mem_fmeet // -?f_surj -?imfset_comp /=
    ?gfS1 ?mem_fmeet ?gS1 //.
  rewrite cancel_r ?f_surj ?mem_fmeet ?fmorphI ?cancel_r ?gS1 //.
  by congr premeet; rewrite -f_surj.
- move=> x y xS2 yS2; apply: f_inj;
  rewrite ?gS1 ?mem_fmeet // -?f_surj -?imfset_comp /=
  ?gfS1 ?mem_fmeet ?gS1 //.
  rewrite cancel_r ?f_surj ?mem_fmeet ?fmorphU ?cancel_r ?gS1 //.
  by congr prejoin; rewrite -f_surj.
- by move=> x y xS2 yS2; move/(congr1 f); rewrite !cancel_r.
- by rewrite -f_surj -imfset_comp /=.
Qed.

Lemma isof_trans L (S1 S2 S3 : {finLattice L}) :
  isof L S1 S2 -> isof L S2 S3 -> isof L S1 S3.
Proof.
case/isofP => f f_surj f_inj /isofP [g g_surj g_inj].
exists (g \o f); apply/misofP; split; first split.
- move=> x y xS1 yS1 /=.
  rewrite fmorphI //= (codomP f_surj) fmorphI ?inE -?f_surj ?in_imfset //.
  congr premeet.
  by rewrite (codomP g_surj) imfset_comp /= -g_surj f_surj.
- move=> x y xS1 yS1 /=.
  rewrite fmorphU //= (codomP f_surj) fmorphU ?inE -?f_surj ?in_imfset //.
  congr prejoin.
  by rewrite (codomP g_surj) imfset_comp /= -g_surj f_surj.
- move=> x y xS1 yS1 gf_eq.
  by apply/f_inj/g_inj; rewrite -?f_surj ?in_imfset.
- by rewrite imfset_comp /= -g_surj f_surj.
Qed.

Lemma meet_isof L (S1 S2 : {finLattice L}) (f : T -> T) :
  {in S1&, injective f} -> f @` (S1 : {fset _}) = S2 ->
  {in S1&, {morph f : x y / \fmeet_S1 x y >-> \fmeet_S2 x y}} ->
  misof L S1 S2 f.
Proof.
move=> f_inj f_surj f_meetmorph; apply/misofP; split => //.
split; rewrite f_surj //.
move=> x y xS1 yS1; rewrite -!fjoinE.
rewrite !fjoin_meets ?inE -?f_surj ?in_imfset // f_surj big_seq_cond.
rewrite (big_morph_sub f_meetmorph);
  [ |by move=> ?; case/and3P |exact: mem_fmeet |exact: mem_ftop].
rewrite -f_surj.
have f_surj_perm : perm_eq (f @` (S1 : {fset _})) [seq f x | x <- S1] by
  exact: enum_imfset.
rewrite [RHS]big_seq_cond.
rewrite (big_perm_sub (fmeetC (S := S2)) (fmeetA (S := S2))
  (mem_fmeet (S := S2)) _ (mem_ftop S2) _ f_surj_perm); last first.
  by move=> ? /and3P []; rewrite f_surj.
rewrite big_map_id [RHS]big_seq_cond.
have <-: \ftop_S2 = f \ftop_S1.
- apply: ftop_id; rewrite ?inE -?f_surj ?in_imfset ?mem_ftop //.
  move=> z; rewrite inE -f_surj => /imfsetP [z' /= z'S1 ->].
  by apply/(fmeet_idPl (S := S2));
    rewrite ?inE -?f_surj ?in_imfset -?f_meetmorph ?mem_ftop ?fmeetf1.
apply: congr_big => //; move=> z; apply: andb_id2l => zS1.
by rewrite in_imfset //=; congr (_ && _);
  rewrite -[RHS](eq_fmeetl (S:=S2)) -?f_meetmorph
  ?(inj_in_eq f_inj) ?eq_fmeetl ?mem_fmeet ?inE -?f_surj ?in_imfset.
Qed.

(*Lemma comp_fmorphism L (S1 S2 S3 : {finLattice L})
      (f : {L : fmorphism S1 >-> S2}) (g : {L : fmorphism S2 >-> S3}) :
  fmorphism L S1 S2 f -> fmorphism L S2 S3 g -> fmorphism L S1 S3 (g \o f).
Proof.
move=> fm gm; split.
- by move=> x x_in; rewrite ?mem_fmorph.
- by move => x y x_in y_in; rewrite /= !fmorphI ?mem_fmorph.
- by move => x y x_in y_in; rewrite /= !fmorphU ?mem_fmorph.*)
(*- by rewrite /= !fmorph0.
- by rewrite /= !fmorph1.*)


(*Canonical fcomp L (S1 S2 S3 : {finLattice L})
  (f : {L : fmorphism S1 >-> S2}) (g : {L : fmorphism S2 >-> S3}) :=
  FMorphism (comp_fmorphism (fmorphismP f) (fmorphismP g)).*)

(*Lemma fmorphism_id L (S : {finLattice L}) :
  fmorphism L S S id.
Proof. by split. Qed.

Canonical fmorph_id L (S : {finLattice L}) := FMorphism (fmorphism_id S).*)

(*Section Test.
Definition fmorph_of L (S1 S2 : {finLattice L})
  (f : {L : fmorphism S1 >-> S2}) & (phantom (T -> T) f) :
  {L : fmorphism S1 >-> S2} := f.
Notation "f %:fmorph" := (fmorph_of (Phantom (T -> T) f)) (at level 0).

Variable (L : {preLattice T}) (S1 S2 S3 : {finLattice L}).
Variable (f : {L : fmorphism S1 >-> S2}) (g : {L : fmorphism S2 >-> S3}).

(*Check ((g \o f)%:fmorph : { L : fmorphism S1 >-> S3}).*)
(*Check (id %:fmorph : {fmorphism S1 >-> S1}).*)
End Test.*)

(*Lemma fcomp_bij L (S1 S2 S3 : {finLattice L})
      (f : {L : fmorphism S1 >-> S2}) (g : {L : fmorphism S2 >-> S3}) :
  {in S1 & on S2, bijective f} -> {in S2 & on S3, bijective g} ->
  {in S1 & on S3, bijective (fcomp f g)}.
Proof.
case=> f' [f'_im fK f'K]; case=> g' [g'_im gK g'K].
exists (f' \o g'); split.
- by move=> x x_in; apply/f'_im/g'_im.
- by move=> x x_in; rewrite /= gK ?fK ?mem_fmorph.
- by move=> x x_in; rewrite /= f'K ?g'K ?g'_im.
Qed.*)

End BijMorphism.

(*Section ImMorphism.
Context {T: choiceType} {L : {preLattice T}} (S1 S2 : {finLattice L}).
Context (f : {L : fmorphism S1 >-> S2}).

Definition fmorph_img := f @` (S1 : {fset _}).

Lemma fmorph_img_prop0 : fmorph_img != fset0 :> {fset _}.
Proof.
case/fset0Pn: (finLattice_prop0 S1) => x xS1; apply/fset0Pn; exists (f x).
exact: in_imfset.
Qed.

Lemma fmorph_img_sub : fmorph_img `<=` S2.
Proof. apply/fsubsetP => x /imfsetP [x' x'S1 ->]; exact/mem_fmorph. Qed.

Lemma fmorph_img_premeet_closed : premeet_closed L fmorph_img.
Proof.
apply/premeet_closedP => x y /imfsetP [x' /= x'S1 ->] /imfsetP [y' /= y'S1 ->].
have premeet_img: premeet L S2 (f x') (f y') \in fmorph_img.
- move: (fmorphI f x'S1 y'S1); rewrite /fmeet => <-.
  exact/in_imfset/mem_fmeet.
suff ->: premeet L fmorph_img (f x') (f y') =
  premeet L S2 (f x') (f y') by [].
apply/(le_anti L).
rewrite premeet_incr ?fmorph_img_sub ?in_imfset //=.
by apply: premeet_inf;
  rewrite ?in_imfset ?premeet_minl ?premeet_minr ?mem_fmorph.
Qed.

Lemma fmorph_img_prejoin_closed : premeet_closed L^~pl fmorph_img.
Proof.
apply/premeet_closedP => /= x y /imfsetP [x' /= x'S1 ->] /imfsetP [y' /= y'S1 ->].
have prejoin_img: prejoin L S2 (f x') (f y') \in fmorph_img.
- move: (fmorphU f x'S1 y'S1); rewrite /fjoin => <-.
  exact/in_imfset/mem_fmeet.
suff ->: prejoin L fmorph_img (f x') (f y') =
  prejoin L S2 (f x') (f y') by [].
apply/(le_anti L)/andP; split; last apply: prejoin_decr; 
  rewrite ?fmorph_img_sub ?in_imfset //.
by apply: prejoin_sumeet;
  rewrite ?in_imfset ?prejoin_maxl ?prejoin_maxr ?mem_fmorph.
Qed.

Lemma fmorph_img_finLattice_r :
  [&& premeet_closed L fmorph_img,
  premeet_closed L^~pl fmorph_img &
  fmorph_img != fset0 :> {fset _}].
Proof.
by rewrite fmorph_img_prejoin_closed fmorph_img_premeet_closed
  fmorph_img_prop0.
Qed.

Canonical fmorph_img_finLattice := FinLattice fmorph_img_finLattice_r.

End ImMorphism.*)


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
Context (f : {fmorphism S1 on L}) (rk1 : {rank S1}) (rk2 : {rank S2}).

Lemma rank_morph x :
  x \in S1 -> misof L S1 S2 f ->  (rk1 x <= rk2 (f x))%N.
Proof.
move=> + /misofP [f_morph f_inj f_surj].
move: x; apply: (rank_ind rk1) => x xS1 ih.
case: (x =P \fbot_S1) => [->|]; first by rewrite rank0.
move/eqP; rewrite -(rank_eq0 rk1) // -lt0n => /graded_rankS -/(_ xS1).
case=> y [yS1 lt_yx <-]; apply: (leq_ltn_trans (ih _ _ _)) => //.
+ by apply: homo_rank_lt.
by apply/homo_rank_lt; rewrite ?inE -?f_surj ?in_imfset ?fmorph_monolt.
Qed.
End FMorphismRank.

(* -------------------------------------------------------------------- *)
Section Atomistic.
Context (T : choiceType) (L : {preLattice T}) (S : {finLattice L}).

Definition atomistic_r (a : S) :=
  [exists A : {fset S},
       [forall x in A, atom S (val x)]
    && (a == (\big[join S/bottom S]_(x in A) x))].

Definition atomistic (a : T) :=
  if @idP (a \in S) is  ReflectT h then atomistic_r [` h] else false.

Definition coatomistic_r (a : S) :=
  [exists A : {fset S},
       [forall x in A, coatom S (val x)]
    && (a == (\big[meet S/top S]_(x in A) x))].

Definition coatomistic (a : T) :=
  if @idP (a \in S) is  ReflectT h then coatomistic_r [` h] else false.


End Atomistic.
