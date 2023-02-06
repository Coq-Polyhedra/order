From mathcomp Require Import all_ssreflect finmap.
Require Import xbigop extra_misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.
Local Open Scope order_scope.

Import RelOrder.Theory Order.LTheory.

(* -------------------------------------------------------------------- *)
Section FsetOrderTheory.

Context {T : choiceType} (L : {pOrder T}).

Implicit Types (K : {fset T}).

Lemma ex_min_elt K : K != fset0 ->
  exists2 m, m \in K & forall x, x \in K -> ~~ (x <_L m).
Proof.
elim/fset_ind: K => //= [x S _ _ _]; elim/fset_ind: S => /= [|y S _ ih].
- exists x; first by rewrite !in_fsetE eqxx.
  by move=> y; rewrite !in_fsetE orbF => /eqP->; rewrite rltxx.
case: ih => m m_in_xS min_m; exists (if y <_L m then y else m).
- case: ifP => _; first by rewrite !in_fsetE eqxx !Monoid.simpm.
  by rewrite fsetUCA in_fsetU m_in_xS orbT.
move=> z; rewrite fsetUCA in_fsetU in_fset1 => /orP[].
- by move/eqP=> ->; case: ifP =>[|/negbT//]; rewrite rltxx.
move=> z_in_xS; case: ifPn => [le_ym|leN_ym].
- by apply: contra (min_m _ z_in_xS) => /rlt_trans; apply.
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

(* -------------------------------------------------------------------- *)
(* TODO: move this section to relorder.v                                *)
(* -------------------------------------------------------------------- *)
Section POrderMonotonyTheoryCodom.
Context (T : choiceType) (r : {pOrder T}).
Context (d : Order.disp_t) (T' : porderType d).
Context (D D' : pred T) (f : T -> T').

Hint Resolve rlt_neqAle rle_anti : core.

Lemma ltW_homo_as :
  {homo f : x y / x <_r  y >-> x <  y} -> {homo f : x y / x <=_r y >-> x <= y}.
Proof. by apply: homoW. Qed.

Lemma inj_homo_lt_as :
  injective f ->
  {homo f : x y / x <=_r y >-> x <= y} -> {homo f : x y / x <_r  y >-> x < y}.
Proof. exact: inj_homo. Qed.

Lemma inc_inj_as : {mono f : x y / x <=_r y >-> x <= y} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma leW_mono_as :
  {mono f : x y / x <=_r y >-> x <= y} -> {mono f : x y / x <_r  y >-> x < y}.
Proof. exact: anti_mono. Qed.

Lemma ltW_homo_in_as :
  {in D & D', {homo f : x y / x <_r  y >-> x <  y}} ->
  {in D & D', {homo f : x y / x <=_r y >-> x <= y}}.
Proof. exact: homoW_in. Qed.

Lemma inj_homo_lt_in_as :
  {in D & D', injective f} ->
  {in D & D', {homo f : x y / x <=_r y >-> x <= y}} ->
  {in D & D', {homo f : x y / x <_r  y >-> x < y}}.
Proof. exact: inj_homo_in. Qed.

Lemma inc_inj_in_as :
  {in D &, {mono f : x y / x <=_r y >-> x <= y}} ->
  {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma leW_mono_in_as :
  {in D &, {mono f : x y / x <=_r y >-> x <= y}} ->
  {in D &, {mono f : x y / x <_r  y >-> x < y}}.
Proof. exact: anti_mono_in. Qed.

End POrderMonotonyTheoryCodom.

(* -------------------------------------------------------------------- *)
Module PreLattice.
Section ClassDef.

Set Primitive Projections.

Record mixin_of (T0 : Type) (b : Order.POrder.class_of T0)
                (T := Order.POrder.Pack Order.disp_tt b) := Mixin {
  witness : T;
  premeet : {fset T} -> T -> T -> T;
  prejoin : {fset T} -> T -> T -> T;
  premeet_min    : forall S x y, x \in S -> y \in S ->
    premeet S x y <= x /\ premeet S x y <= y;
  premeet_inf    : forall S x y z, x \in S -> y \in S -> z \in S ->
    z <= x -> z <= y -> z <= premeet S x y;
  premeet_incr   : forall S S' x y, S `<=` S' -> x \in S -> y \in S ->
    premeet S x y <= premeet S' x y;
  prejoin_max    : forall S x y, x \in S -> y \in S ->
    prejoin S x y >= x /\ prejoin S x y >= y;
  prejoin_sumeet : forall S x y z, x \in S -> y \in S -> z \in S ->
    z >= x -> z >= y -> z >= prejoin S x y;
  prejoin_decr : forall S S' x y, S `<=` S' -> x \in S -> y \in S ->
    prejoin S x y >= prejoin S' x y
}.

Record class_of (T : Type) := Class {
  base : Order.POrder.class_of T;
  mixin : mixin_of base;
}.

Local Coercion base : class_of >-> Order.POrder.class_of.

Structure type (disp : Order.disp_t) := Pack { sort; _ : class_of sort }.

Unset Primitive Projections.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : Order.disp_t) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@Order.POrder.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @Order.POrder.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Order.POrder.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion class : type >-> class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Notation prelatticeType := type.
Notation PrelatticeType T m := (@pack T _ _ _ id m).
Notation "[ 'prelatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'prelatticeType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'prelatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0, format "[ 'prelatticeType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'prelatticeType' 'of' T ]" := [prelatticeType of T for _]
  (at level 0, format "[ 'prelatticeType'  'of'  T ]") : form_scope.
Notation "[ 'prelatticeType' 'of' T 'with' disp ]" :=
  [prelatticeType of T for _ with disp]
  (at level 0, format "[ 'prelatticeType'  'of'  T  'with' disp ]") : form_scope.
End Exports.

End PreLattice.
Export PreLattice.Exports.

Section PreLatticeDef.
Context {disp : Order.disp_t} {T : prelatticeType disp}.
Definition witness : T := PreLattice.witness (PreLattice.class T).
Definition premeet : {fset T} -> T -> T -> T :=
  PreLattice.premeet (PreLattice.class T).
Definition prejoin : {fset T} -> T -> T -> T :=
  PreLattice.prejoin (PreLattice.class T).
End PreLatticeDef.

Section PreLatticeTheory.

Context {disp : Order.disp_t} {T : prelatticeType disp}.
Implicit Type (S : {fset T}) (x y : T).


(* TO IMPROVE *)
(*Definition mixin L := (PreLattice.mixin (PreLattice.class L)).*)

Lemma premeet_minlr S:
  {in S &, forall x y, premeet S x y <= x /\ premeet S x y <= y}.
Proof. exact: PreLattice.premeet_min. Qed.

Lemma premeet_minl S:
  {in S &, forall x y, premeet S x y <= x}.
Proof. by move=> x y xS yS; case: (premeet_minlr xS yS). Qed.

Lemma premeet_minr S:
  {in S &, forall x y, premeet S x y <= y}.
Proof. by move=> x y xS yS; case: (premeet_minlr xS yS). Qed.

Definition premeet_min := (premeet_minl, premeet_minr).

Lemma premeet_inf S:
  {in S & &, forall x y z, z <= x -> z <= y -> z <= premeet S x y}.
Proof. exact: PreLattice.premeet_inf. Qed.

Lemma premeet_incr S S': S `<=` S' ->
  {in S &, forall x y, premeet S x y <= premeet S' x y}.
Proof. move=> ?????; exact: PreLattice.premeet_incr. Qed.

Lemma prejoin_max S:
  {in S &, forall x y, x <= prejoin S x y /\ y <= prejoin S x y}.
Proof. exact: PreLattice.prejoin_max. Qed.

Lemma prejoin_maxl S:
  {in S &, forall x y, x <= prejoin S x y}.
Proof. by move=> x y xS yS; case: (prejoin_max xS yS). Qed.

Lemma prejoin_maxr S:
  {in S &, forall x y, y <= prejoin S x y}.
Proof. by move=> x y xS yS; case: (prejoin_max xS yS). Qed.

Lemma prejoin_sumeet S:
  {in S & &, forall x y z, x <= z -> y <= z -> prejoin S x y <= z}.
Proof. exact: PreLattice.prejoin_sumeet. Qed.

Lemma prejoin_decr S S': S `<=` S' ->
  {in S &, forall x y, prejoin S' x y <= prejoin S x y}.
Proof. move=> ?????; exact: PreLattice.prejoin_decr. Qed.

End PreLatticeTheory.

Module Import DualPreLattice.
Section DualPreLattice.

Context {disp : Order.disp_t} {T : prelatticeType disp}.

Definition DualPreLatticeMixin :=
  @PreLattice.Mixin _ (Order.POrder.class [porderType of T^d]) witness
                    (@prejoin _ T) (@premeet _ T)
                    (@PreLattice.prejoin_max _ _ (PreLattice.class T))
                    (@PreLattice.prejoin_sumeet _ _ (PreLattice.class T))
                    (@PreLattice.prejoin_decr _ _ (PreLattice.class T))
                    (@PreLattice.premeet_min _ _ (PreLattice.class T))
                    (@PreLattice.premeet_inf _ _ (PreLattice.class T))
                    (@PreLattice.premeet_incr _ _ (PreLattice.class T)).

Canonical DualPreLatticeType := PrelatticeType T^d DualPreLatticeMixin.

Notation dual_premeet := (@premeet (Order.dual_display _) _).
Notation dual_prejoin := (@prejoin (Order.dual_display _) _).
Notation "premeet^d" := dual_premeet.
Notation "prejoin^d" := dual_prejoin.

Lemma prejoinEdual (S : {fset T}) (x y : T) :
  prejoin^d (S : {fset T^d}) x y = premeet S x y.
Proof. by []. Qed.

Lemma premeetEdual (S : {fset T}) (x y : T) :
  premeet^d (S : {fset T^d}) x y = prejoin S x y.
Proof. by []. Qed.

End DualPreLattice.
End DualPreLattice.

Notation dual_premeet := (@premeet (Order.dual_display _) _).
Notation dual_prejoin := (@prejoin (Order.dual_display _) _).
Notation "premeet^d" := dual_premeet.
Notation "prejoin^d" := dual_prejoin.

(* ================================================================== *)
Section MeetToPreLattice.

Context {disp : Order.disp_t} {T : tMeetSemilatticeType disp}.

Definition mpremeet & {fset T} := @Order.meet _ T.

Definition mprejoin (S : {fset T}) x y := \meet_(i <- S | (x <= i) && (y <= i)) i.

Lemma mpremeet_min S x y : x \in S -> y \in S ->
  mpremeet S x y <= x /\ mpremeet S x y <= y.
Proof. by move=> xS yS; rewrite leIl leIr. Qed.

Lemma mpremeet_inf S x y z :
  x \in S -> y \in S -> z \in S -> z <= x -> z <= y -> z <= mpremeet S x y.
Proof. by move=> xS yS zS; rewrite lexI => -> ->. Qed.

Lemma mpremeet_incr S S' x y :
  S `<=` S' -> x \in S -> y \in S -> mpremeet S x y <= mpremeet S' x y.
Proof. by []. Qed.

Lemma mprejoin_max S x y :
  x \in S -> y \in S ->
  x <= mprejoin S x y /\ y <= mprejoin S x y.
Proof. by move=> xS yS; split; apply/meetsP_seq => ?? /andP []. Qed.

Lemma mprejoin_sumeet S x y z :
  x \in S -> y \in S -> z \in S ->
  x <= z -> y <= z -> mprejoin S x y <= z.
Proof. by move=> xS yS zS xlez ylez; apply: meet_inf_seq => //; apply/andP. Qed.

Lemma mprejoin_decr S S' x y :
  S `<=` S' -> x \in S -> y \in S ->
  mprejoin S' x y <= mprejoin S x y.
Proof.
move=> /fsubsetP Ssub xS yS; apply/meetsP_seq => z zS /andP [xlez ylez].
apply: meet_inf_seq; rewrite ?xlez ?ylez //.
exact: Ssub.
Qed.

Definition tMeetSemilatticeType_prelattice :=
  @PreLattice.Mixin _ (Order.POrder.class T) Order.top
                    _ _ mpremeet_min mpremeet_inf mpremeet_incr
                    mprejoin_max mprejoin_sumeet mprejoin_decr.

(* FIXME: introduce a tag for T (non-forgetful inheritance) *)
Canonical tMeetSemilatticeType_prelatticeType :=
  PrelatticeType T tMeetSemilatticeType_prelattice.

End MeetToPreLattice.

Section JoinToPreLattice.

Context {disp : Order.disp_t} {T : bJoinSemilatticeType disp}.

Definition bJoinSemilatticeType_prelattice :=
  @tMeetSemilatticeType_prelattice _ [tMeetSemilatticeType of T^d].
(* FIXME: introduce a tag for T (non-forgetful inheritance) *)
Canonical JoinPreLattice :=
  [prelatticeType of T for PrelatticeType T^d bJoinSemilatticeType_prelattice].

End JoinToPreLattice.

(* ========================================================================== *)

Definition is_premeet_closed
  {disp : Order.disp_t} {T : prelatticeType disp} (S : {fset T}) :=
  [forall x : S, [forall y : S, premeet S (fsval x) (fsval y) \in S]].

Definition is_prejoin_closed
  {disp : Order.disp_t} {T : prelatticeType disp} (S : {fset T}) :=
  [forall x : S, [forall y : S, prejoin S (fsval x) (fsval y) \in S]].

(*TODO : Change S by a predicate*)
Lemma premeet_closedP
  {disp : Order.disp_t} {T : prelatticeType disp} (S : {fset T}) :
  reflect (forall x y, x \in S -> y \in S -> premeet S x y \in S)
          (is_premeet_closed S).
Proof.
apply: (iffP idP) => [+ x y xS yS|].
- by move/forallP/(_ [`xS])/forallP/(_ [`yS]).
- by move=> premeet_closedH; do 2 apply/forallP => ?; exact: premeet_closedH.
Qed.

Lemma prejoin_closedP
  {disp : Order.disp_t} {T : prelatticeType disp} (S : {fset T}) :
  reflect (forall x y, x \in S -> y \in S -> prejoin S x y \in S)
          (is_prejoin_closed S).
Proof. exact: (@premeet_closedP _ [prelatticeType of T^d]). Qed.

Module FinLattice.
Section ClassDef.

Set Primitive Projections.
Record finLattice_ (T0 : Type) (b : PreLattice.class_of T0)
                   (T := PreLattice.Pack Order.disp_tt b) := FinLattice {
  elements_ : {fset T};
  premeet_closed : is_premeet_closed elements_;
  prejoin_closed : is_prejoin_closed elements_;
  fl_inhabited : elements_ != fset0;
}.
Unset Primitive Projections.

Context {disp : Order.disp_t} {T : prelatticeType disp}.

Definition finLattice (_ : phant T) : Type :=
  @finLattice_ T (PreLattice.class T).

Context (phT : phant T).

Definition elements (S : finLattice phT) : {fset T} := elements_ S.

Definition pred_finLattice (S : {fset T}) : bool :=
  [&& is_premeet_closed S, is_prejoin_closed S & S != fset0].

Definition sub_finLattice (S : {fset T}) (w : pred_finLattice S) :
  finLattice phT :=
  @FinLattice _ _ S (proj1 (andP w))
    (proj1 (andP (proj2 (andP w)))) (proj2 (andP (proj2 (andP w)))).

Lemma finLattice_rec (K : finLattice phT -> Type) :
  (forall (x : {fset T}) (Px : pred_finLattice x), K (sub_finLattice Px)) ->
  forall u : finLattice phT, K u.
Proof.
move=> HK [S HS1 HS2 HS3].
have HS: pred_finLattice S by apply/and3P.
by congr (K (FinLattice _ _ _)): (HK S HS); apply: bool_irrelevance.
Qed.

Local Canonical finLattice_subType :=
  SubType (finLattice phT) elements sub_finLattice finLattice_rec vrefl_rect.

Definition finLattice_eqMixin := [eqMixin of finLattice phT by <:].
Local Canonical finLattice_eqType := EqType (finLattice phT) finLattice_eqMixin.

Definition finLattice_choiceMixin := [choiceMixin of finLattice phT by <:].
Local Canonical finLattice_choiceType :=
  ChoiceType (finLattice phT) finLattice_choiceMixin.

Definition mem_finLattice (S: finLattice phT) : {pred T} :=
  fun x : T => x \in elements S.
Local Canonical finLattice_predType := PredType mem_finLattice.

Local Canonical finLattice_finPredType :=
  mkFinPredType (finLattice phT) elements
    (fun S => fset_uniq (elements S)) (fun _ _ => erefl).

End ClassDef.

Module Exports.
Notation finLattice := finLattice.
Notation FinLattice := FinLattice.
Notation elements := elements.
Coercion elements : finLattice >-> finset_of.
Canonical finLattice_subType.
Canonical finLattice_eqType.
Canonical finLattice_choiceType.
Canonical finLattice_predType.
Canonical finLattice_finPredType.
Notation "{ 'finLattice' T }" :=
  (@finLattice _ _ (Phant T)) (at level 0, format "{ 'finLattice'  T }").
End Exports.

End FinLattice.
Export FinLattice.Exports.

Lemma in_finLatticeE {disp : Order.disp_t} {T : prelatticeType disp}
  (S : {finLattice T}) x : (x \in S) = (x \in elements S).
Proof. by []. Qed.

Lemma finLattice_eqP {disp : Order.disp_t} {T : prelatticeType disp}
  (S S' : {finLattice T}): S = S' <-> S =i S'.
Proof. split; [by move=>->|by move=> ?; apply/val_inj/fsetP]. Qed.

Definition inE := (@in_finLatticeE, inE).

(*
Section Test.

Context {disp : Order.disp_t} {T : prelatticeType disp} {S : {finLattice T}}.
Goal forall (f : T -> T), f @` S = S. Abort.

Context (S1 S2 : {finLattice T}) (P : T -> Prop).
Goal forall x y z, premeet S1 x y = z. Abort.

End Test.
*)

Section FinLatticeDual.

Context {disp : Order.disp_t} {T : prelatticeType disp} (S : {finLattice T}).

(* FIXME: introduce a key *)
Canonical FinLatticeDual : {finLattice T^d} :=
  @FinLattice.FinLattice _
    (PreLattice.class [prelatticeType of T^d]) _
    (FinLattice.prejoin_closed S) (FinLattice.premeet_closed S)
    (FinLattice.fl_inhabited S).

Lemma dual_fjoinE: prejoin FinLatticeDual = premeet S.
Proof. by []. Qed.

Lemma dual_fmeetE: premeet FinLatticeDual = prejoin S.
Proof. by []. Qed.

End FinLatticeDual.

Notation "S ^~s" := (FinLatticeDual S) (at level 8, format "S ^~s").

(* TODO: Module FinLatticeStructure *)
(* use a lifting function :
   fun_val f x := f (val x)
   fun2_val f x y := f (val x) (val y)
   \big[\meetS/ \top_S]_(i <- S | P i) f i = \big[val_fun \meet_S]_(i : S | fun_val P i) fun_val f i
 TO BE DEVELOPED in a separate file *)

Module FinLatticeStructure.
Section FinLatticeStructure.

Context {disp : Order.disp_t} {T : prelatticeType disp} (S : {finLattice T}).

Lemma finLattice_prop0 : S != fset0 :> {fset _}.
Proof. by case: S. Qed.

Definition witness := [`xchooseP (fset0Pn S finLattice_prop0)].

Lemma mem_meet : forall x y, x \in S -> y \in S -> premeet S x y \in S.
Proof. by case: S => S0 ? ? ?; apply/premeet_closedP. Qed.

Lemma mem_join : forall x y, x \in S -> y \in S -> prejoin S x y \in S.
Proof. by case: S => S0 ? ? ?; apply/prejoin_closedP. Qed.

(* ------------------------------------------------------------------ *)

Definition finle (x y : S) := (val x <= val y).
Definition finlt (x y : S) := (val x < val y).

Lemma finlexx : reflexive finle.
Proof. by rewrite /finle. Qed.

Lemma finle_anti : antisymmetric finle.
Proof. by move=> x y ?; apply/val_inj/le_anti. Qed.

Lemma finle_trans : transitive finle.
Proof. by move=> y x z; rewrite /finle; exact: le_trans. Qed.

Lemma finlt_def : forall (x y : S), finlt x y = (y != x) && finle x y.
Proof. by move=> x y; rewrite /finle /finlt lt_def; congr (_ && _). Qed.

Definition finle_mixin :=
  LePOrderMixin finlt_def finlexx finle_anti finle_trans.

Local Canonical fin_porderType := POrderType disp S finle_mixin.

(* --------------------------------------------------------------- *)

Definition finmeet (x y : S) := fun2_val witness (premeet S) x y.
Definition finjoin (x y : S) := fun2_val witness (prejoin S) x y.

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
  rewrite !finmeet_inf ?finmeet_minl ?finmeet_minr.
Qed.

Lemma finmeetAl : forall (x y z t : S), t \in [fset x; y; z] ->
  finle (finmeet x (finmeet y z)) t.
Proof.
move=> x y z t; rewrite !in_fsetE -orbA; case/or3P => /eqP ->.
+ exact: finmeet_minl.
+ exact/(finle_trans _ (finmeet_minl y z))/finmeet_minr.
+ exact/(finle_trans _ (finmeet_minr y z))/finmeet_minr.
Qed.

Lemma finmeetAr : forall (x y z t : S), t \in [fset x; y; z] ->
  finle (finmeet (finmeet x y) z) t.
Proof.
move=> x y z t; rewrite !in_fsetE -orbA; case/or3P => /eqP ->.
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
move=> x y; apply/idP/eqP => [lexy | <-]; last exact: finmeet_minr.
by apply/finle_anti; rewrite finmeet_minl finmeet_inf ?finlexx.
Qed.

(* ----------------------------------------------------------------- *)

Lemma finjoinC : commutative finjoin.
Proof.
by move=> x y; apply: finle_anti;
  rewrite !finjoin_sup ?finjoin_maxl ?finjoin_maxr.
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

Lemma lefinjoin : forall x y : S, rdual_rel finle x y = (finjoin x y == x).
Proof.
move=> x y; apply/idP/eqP => [leyx | <-]; last by exact: finjoin_maxr.
by apply/finle_anti; rewrite finjoin_maxl finjoin_sup ?finlexx.
Qed.

(* TODO: Would using MeetJoinMixin be better? *)
Definition fin_meetMixin := MeetMixin finmeetC finmeetA lefinmeet.
Definition fin_joinMixin := JoinMixin finjoinC finjoinA lefinjoin.

Local Canonical fin_meetSemilatticeType := MeetSemilatticeType S fin_meetMixin.
Local Canonical fin_joinSemilatticeType := JoinSemilatticeType S fin_joinMixin.
Local Canonical fin_latticeType := [latticeType of S].

End FinLatticeStructure.
Module Exports.
Arguments finle {disp T S} x y.
Arguments finlt {disp T S} x y.
Arguments finmeet {disp T S} x y.
Arguments finjoin {disp T S} x y.
Notation finle := finle.
Notation finlt := finlt.
Notation finmeet := finmeet.
Notation finjoin := finjoin.
(* FIXME: non-uniform coercion *)
(* FIXME: these instances should be reimplemented as builders *)
Coercion fin_porderType : finLattice >-> Order.POrder.type.
Coercion fin_meetSemilatticeType : finLattice >-> Order.MeetSemilattice.type.
Coercion fin_joinSemilatticeType : finLattice >-> Order.JoinSemilattice.type.
Coercion fin_latticeType : finLattice >-> Order.Lattice.type.
Canonical fin_porderType.
Canonical fin_meetSemilatticeType.
Canonical fin_joinSemilatticeType.
Canonical fin_latticeType.
End Exports.
End FinLatticeStructure.
Import FinLatticeStructure.Exports.

(* ========================================================================= *)
(* DONE UP TO HERE                                                           *)
(* ========================================================================= *)

Section FinLatticeTheory.

(* TODO: move it *)
Lemma sub_pred1 (T : choiceType) (K : {fset T}) (P : T -> Prop) :
  (forall x : K, P (fsval x)) -> {in K, forall x, P x}.
Proof. move=> Pval x xK; exact: (Pval [`xK]). Qed.

Lemma sub_pred2 (T : choiceType) (K : {fset T}) (P : T -> T -> Prop) :
  (forall x y : K, P (fsval x) (fsval y)) -> {in K &, forall x y, P x y}.
Proof. move=> Pval x y xS yS; exact: (Pval [`xS] [`yS]). Qed.

Lemma sub_pred3 (T : choiceType) (K : {fset T}) (P : T -> T -> T -> Prop) :
  (forall x y z: K, P (fsval x) (fsval y) (fsval z)) ->
  {in K & &, forall x y z, P x y z}.
Proof. move=> Pval x y z xS yS zS; exact: (Pval [`xS] [`yS] [`zS]). Qed.

(* Lemma fmeetE (disp : Order.disp_t) (T : prelatticeType disp) (S : {finLattice T}) :
  premeet S =2 premeet S.
Proof. by []. Qed.

Lemma fjoinE (disp : Order.disp_t) (T : prelatticeType disp) (S : {finLattice T}) :
  prejoin S =2 prejoin S.
Proof. by []. Qed. *)

Lemma mem_fmeet (disp : Order.disp_t) (T : prelatticeType disp) (S : {finLattice T}) :
  {in S &, forall x y, premeet S x y \in S}.
Proof.
case: S => S premeet_closed ?? x y; rewrite !inE /=.
exact/premeet_closedP.
Qed.

Lemma mem_fjoin (disp : Order.disp_t) (T : prelatticeType disp) (S: {finLattice T}) :
  {in S &, forall x y, prejoin S x y \in S}.
Proof. exact: mem_fmeet S^~s. Qed.

Lemma finLattice_prop0 (disp : Order.disp_t) (T : prelatticeType disp) (S : {finLattice T}): S != fset0 :> {fset _}.
Proof. by case: S. Qed.

Lemma finLattice_leE (disp : Order.disp_t) (T : prelatticeType disp) (S : {finLattice T}) : forall x y : S,
  x <= y = (fsval x <= fsval y).
Proof. by []. Qed.

Lemma finLattice_meetE (disp : Order.disp_t) (T : prelatticeType disp) (S : {finLattice T}) : forall x y : S,
  fsval (Order.meet x y) = premeet S (fsval x) (fsval y).
Proof. by move=> x y; rewrite insubdK ?mem_fmeet ?fsvalP. Qed.

Lemma finLattice_joinE (disp : Order.disp_t) (T : prelatticeType disp) (S : {finLattice T}) : forall x y : S,
  fsval (Order.join x y) = prejoin S (fsval x) (fsval y).
Proof. by move=> x y; rewrite insubdK ?mem_fjoin ?fsvalP. Qed.

(*Goal forall L, forall S : {finLattice L}, forall x y, join S x y = meet (S^~s) x y.
Proof. by move=> L S x y; apply/val_inj; rewrite !insubdK ?mem_fmeet ?fsvalP.*)

Section FMeetTheory.

Context {disp : Order.disp_t} {T : prelatticeType disp}.

Lemma leIfl (S : {finLattice T}) : {in S &, forall x y, premeet S x y <= x}.
Proof.
apply: sub_pred2 => x y; move: (@leIl _ S x y).
by rewrite finLattice_leE finLattice_meetE.
Qed.

Lemma leIfr (S : {finLattice T}) : {in S &, forall x y, premeet S y x <= x}.
Proof.
apply: sub_pred2 => x y; move: (@leIr _ S x y).
by rewrite finLattice_leE finLattice_meetE.
Qed.

Lemma lefI (S : {finLattice T}) :
  {in S & &, forall x y z, (x <= premeet S y z) = (x <= y) && (x <= z)}.
Proof.
apply: sub_pred3 => x y z; move: (@lexI _ S x y z).
by rewrite !finLattice_leE finLattice_meetE.
Qed.

Lemma fmeetC (S : {finLattice T}) : {in S &, commutative (premeet S)}.
Proof.
apply: sub_pred2=> x y; move: (@meetC _ S x y).
by move/(@congr1 _ _ (@fsval _ S)); rewrite !finLattice_meetE.
Qed.

Lemma lefIl (S : {finLattice T}) :
  {in S & &, forall x y z, y <= x -> premeet S y z <= x}.
Proof.
apply: sub_pred3 => x y z; move: (@leIxl _ S x y z).
by rewrite !finLattice_leE !finLattice_meetE.
Qed.

Lemma lefIr (S : {finLattice T}) :
  {in S & &, forall x y z, z <= x -> premeet S y z <= x}.
Proof. move=> x y z xS yS zS zlex; rewrite fmeetC //; exact: lefIl. Qed.

Lemma fmeetA (S : {finLattice T}) : {in S & &, associative (premeet S) }.
Proof.
apply: sub_pred3=> x y z; move:(@meetA _ S x y z).
by move/(@congr1 _ _ (@fsval _ S)); rewrite !finLattice_meetE.
Qed.

Lemma fmeetxx (S : {finLattice T}) : {in S, idempotent (premeet S)}.
Proof.
apply: sub_pred1=> x; move:(@meetxx _ S x).
by move/(@congr1 _ _ (@fsval _ S)); rewrite finLattice_meetE.
Qed.

Lemma leEfmeet (S : {finLattice T}) :
  {in S &, forall x y, (x <= y) = (premeet S x y == x)}.
Proof.
apply: sub_pred2 => x y; move:(@leEmeet _ S x y).
by rewrite finLattice_leE -val_eqE /= finLattice_meetE.
Qed.

Lemma fmeetAC (S : {finLattice T}) :
  {in S & &, right_commutative (premeet S)}.
Proof.
apply: sub_pred3=> x y z; move:(@meetAC _ S x y z).
by move/(@congr1 _ _ (@fsval _ S)); rewrite !finLattice_meetE.
Qed.

Lemma fmeetCA (S : {finLattice T}) :
  {in S & &, left_commutative (premeet S)}.
Proof.
apply: sub_pred3=> x y z; move:(@meetCA _ S x y z).
by move/(@congr1 _ _ (@fsval _ S)); rewrite !finLattice_meetE.
Qed.

Lemma fmeetACA (S : {finLattice T}) x y z t:
  x \in S -> y \in S -> z \in S -> t \in S ->
  premeet S (premeet S x y) (premeet S z t) =
  premeet S (premeet S x z) (premeet S y t).
Proof.
move=> xS yS zS tS; move:(@meetACA _ S [`xS] [`yS] [`zS] [`tS]).
by move/(@congr1 _ _ (@fsval _ S)); rewrite ?finLattice_meetE.
Qed.

Lemma fmeetKI (S : {finLattice T}) :
  {in S &, forall x y, premeet S x (premeet S x y) = premeet S x y}.
Proof. by move=> x y xS yS; rewrite fmeetA ?fmeetxx. Qed.

Lemma fmeetIK (S : {finLattice T}) :
  {in S &, forall x y, premeet S (premeet S x y) y = premeet S x y}.
Proof. by move=> x y xS yS; rewrite -fmeetA ?fmeetxx. Qed.

Lemma fmeetKIC (S : {finLattice T}) :
  {in S &, forall x y, premeet S x (premeet S y x) = premeet S x y}.
Proof. by move=> ? ? ? ?; rewrite fmeetC ?mem_fmeet ?fmeetIK // fmeetC. Qed.

Lemma fmeetIKC (S : {finLattice T}) :
  {in S &, forall x y, premeet S (premeet S y x) y = premeet S x y}.
Proof. by move=> ? ? ? ?; rewrite fmeetC ?mem_fmeet ?fmeetKI // fmeetC. Qed.

Lemma leIf2 (S : {finLattice T}) :
  {in S & &, forall x y z, (y <= x) || (z <= x) ->
  premeet S y z <= x}.
Proof.
move=> x y z xS yS zS /orP [ylex | zlex]; [exact: lefIl | exact: lefIr].
Qed.

Lemma fmeet_idPl (S : {finLattice T}) {x y} : x \in S -> y \in S ->
  reflect (premeet S x y = x) (x <= y).
Proof. move=> xS yS; rewrite (leEfmeet xS yS) //; exact: eqP. Qed.

Lemma fmeet_idPr (S : {finLattice T}) {x y} : x \in S -> y \in S ->
  reflect (premeet S y x = x) (x <= y).
Proof. by move=> xS yS; rewrite fmeetC //; apply/fmeet_idPl. Qed.

Lemma fmeet_l (S : {finLattice T}) :
  {in S &, forall x y, x <= y -> premeet S x y = x}.
Proof. move=> x y xS yS; exact/fmeet_idPl. Qed.

Lemma fmeet_r (S : {finLattice T}) :
  {in S &, forall x y, y <= x -> premeet S x y = y}.
Proof. move=> x y xS yS; exact/fmeet_idPr. Qed.

Lemma lefIidl (S : {finLattice T}) :
  {in S &, forall x y, (x <= premeet S x y) = (x <= y)}.
Proof. by move=> x y xS yS; rewrite !(leEfmeet xS) ?mem_fmeet ?fmeetKI. Qed.

Lemma lefIidr (S : {finLattice T}) :
  {in S &, forall x y, (x <= premeet S y x) = (x <= y)}.
Proof. by move=> x y xS yS; rewrite !(leEfmeet xS) ?mem_fmeet ?fmeetKIC. Qed.

Lemma eq_fmeetl (S : {finLattice T}) :
  {in S &, forall x y, (premeet S x y == x) = (x <= y)}.
Proof. by move=> ????; apply/esym/leEfmeet. Qed.

Lemma eq_fmeetr (S: {finLattice T}) :
  {in S &, forall x y, (premeet S x y == y) = (y <= x)}.
Proof. by move=> ????; rewrite fmeetC ?eq_fmeetl. Qed.

Lemma lefI2 (S : {finLattice T}) x y z t :
  x \in S -> y \in S -> z \in S -> t \in S ->
  x <= z -> y <= t -> premeet S x y <= premeet S z t.
Proof.
move=> xS yS zS tS; move:(@leI2 _ S [`xS] [`yS] [`zS] [`tS]).
by rewrite !finLattice_leE !finLattice_meetE.
Qed.

End FMeetTheory.

(* -------------------------------------------------------------------- *)
Section FJoinTheory.

Context {disp : Order.disp_t} {T : prelatticeType disp}.

Lemma fjoinC (S : {finLattice T}) : {in S &, commutative (prejoin S)}.
Proof. exact: (@fmeetC _ _ S^~s). Qed.

Lemma lefUr (S: {finLattice T}) : {in S &, forall x y, x <= prejoin S y x}.
Proof. exact: (@leIfr _ _ S^~s). Qed.

Lemma lefUl (S : {finLattice T}) : {in S &, forall x y, x <= prejoin S x y}.
Proof. exact: (@leIfl _ _ S^~s). Qed.

Lemma leUf (S : {finLattice T}) : {in S & &, forall x y z,
  (prejoin S y z <= x) = (y <= x) && (z <= x)}.
Proof. exact: (@lefI _ _ S^~s). Qed.

Lemma fjoinA (S : {finLattice T}) : {in S & &, associative (prejoin S)}.
Proof. exact: (@fmeetA _ _ S^~s). Qed.

Lemma fjoinxx (S : {finLattice T}) : {in S, idempotent (prejoin S)}.
Proof. exact: (@fmeetxx _ _ S^~s). Qed.

Lemma leEfjoin (S : {finLattice T}) :
  {in S &, forall x y, (x <= y) = (prejoin S y x == y)}.
Proof.
move=> ????; exact: (@leEfmeet _ _ S^~s).
Qed.

Lemma fjoinAC (S : {finLattice T}) :
  {in S & &, right_commutative (prejoin S)}.
Proof. exact: (@fmeetAC _ _ S^~s). Qed.

Lemma fjoinCA (S : {finLattice T}) :
  {in S & &, left_commutative (prejoin S)}.
Proof. exact: (@fmeetCA _ _ S^~s). Qed.

Lemma fjoinACA (S : {finLattice T}) x y z t :
  x \in S -> y \in S -> z \in S -> t \in S ->
  prejoin S (prejoin S x y) (prejoin S z t) =
  prejoin S (prejoin S x z) (prejoin S y t).
Proof. exact: (@fmeetACA _ _ S^~s). Qed.

Lemma fjoinKU (S: {finLattice T}) :
  {in S &, forall x y, prejoin S x (prejoin S x y) = prejoin S x y}.
Proof. exact: (@fmeetKI _ _ S^~s). Qed.

Lemma fjoinUK (S : {finLattice T}) :
  {in S &, forall x y, prejoin S (prejoin S x y) y = prejoin S x y}.
Proof. exact: (@fmeetIK _ _ S^~s). Qed.

Lemma fjoinKUC (S : {finLattice T}) :
  {in S &, forall x y, prejoin S x (prejoin S y x) = prejoin S x y}.
Proof. exact: (@fmeetKIC _ _ S^~s). Qed.

Lemma fjoinUKC (S : {finLattice T}) :
  {in S &, forall x y, prejoin S (prejoin S y x) y = prejoin S x y}.
Proof. exact: (@fmeetIKC _ _ S^~s). Qed.

Lemma leUfl (S: {finLattice T}) :
  {in S & &, forall x y z, x <= y -> x <= prejoin S y z}.
Proof. exact: (@lefIl _ _ S^~s). Qed.

Lemma leUfr (S : {finLattice T}) :
  {in S & &, forall x y z, x <= z -> x <= prejoin S y z}.
Proof. exact: (@lefIr _ _ S^~s). Qed.

Lemma lefU2 (S : {finLattice T}) :
  {in S & &, forall x y z, (x <= y) || (x <= z) ->
  x <= prejoin S y z}.
Proof. exact: (@leIf2 _ _ S^~s). Qed.

Lemma fjoin_idPr (S : {finLattice T}) {x y}: x \in S -> y \in S ->
  reflect (prejoin S y x = x) (y <= x).
Proof. exact: (@fmeet_idPr _ _ S^~s). Qed.

Lemma fjoin_idPl (S: {finLattice T}) {x y} : x \in S -> y \in S ->
  reflect (prejoin S x y = x) (y <= x).
Proof. exact: (@fmeet_idPl _ _ S^~s). Qed.

Lemma fjoin_l (S : {finLattice T}) :
  {in S &, forall x y, y <= x -> prejoin S x y = x}.
Proof. exact: (@fmeet_l _ _ S^~s). Qed.

Lemma fjoin_r (S : {finLattice T}) :
  {in S &, forall x y, x <= y -> prejoin S x y = y}.
Proof. exact: (@fmeet_r _ _ S^~s). Qed.

Lemma leUfidl (S: {finLattice T}) :
  {in S &, forall x y, (prejoin S x y <= x) = (y <= x)}.
Proof. exact: (@lefIidl _ _ S^~s). Qed.

Lemma leUfidr (S : {finLattice T}) :
  {in S &, forall x y, (prejoin S y x <= x) = (y <= x)}.
Proof. exact: (@lefIidr _ _ S^~s). Qed.

Lemma eq_fjoinl (S : {finLattice T}) :
  {in S &, forall x y, (prejoin S x y == x) = (y <= x)}.
Proof. exact: (@eq_fmeetl _ _ S^~s). Qed.

Lemma eq_fjoinr (S : {finLattice T}) :
  {in S &, forall x y, (prejoin S x y == y) = (x <= y)}.
Proof. exact: (@eq_fmeetr _ _ S^~s). Qed.

Lemma leUf2 (S: {finLattice T}) x y z t :
  x \in S -> y \in S -> z \in S -> t \in S ->
  x <= z -> y <= t -> prejoin S x y <= prejoin S z t.
Proof.
move=> ????; exact: (@lefI2 _ _ S^~s).
Qed.

End FJoinTheory.

Section FMeetJoinTheory.

Section FMeet.
Context {disp : Order.disp_t} {T : prelatticeType disp}.

Lemma fmeetUK (S : {finLattice T}) :
  {in S &, forall x y, prejoin S (premeet S x y) y = y}.
 Proof. by move=> x y xS yS; apply/eqP; rewrite eq_fjoinr ?leIfr ?mem_fmeet. Qed.

Lemma fmeetUKC (S : {finLattice T}) :
  {in S &, forall x y, prejoin S (premeet S y x) y = y}.
Proof. by move=> ????; rewrite fmeetC ?fmeetUK. Qed.

Lemma fmeetKUC (S : {finLattice T}) :
  {in S &, forall x y, prejoin S x (premeet S y x) = x}.
Proof. by move=> ????; rewrite fjoinC ?fmeetUK ?mem_fmeet. Qed.

Lemma fmeetKU (S : {finLattice T}) :
  {in S &, forall x y, prejoin S x (premeet S x y) = x}.
Proof. by move=> ????; rewrite fmeetC ?fmeetKUC. Qed.

End FMeet.

Section FJoin.
Context {disp : Order.disp_t} {T : prelatticeType disp}.

Lemma fjoinIK (S : {finLattice T}) :
  {in S &, forall x y, premeet S (prejoin S x y) y = y}.
Proof. exact: (@fmeetUK _ _ S^~s). Qed.

Lemma fjoinIKC (S : {finLattice T}) :
  {in S &, forall x y, premeet S (prejoin S y x) y = y}.
Proof. exact: (@fmeetUKC _ _ S^~s). Qed.

Lemma fjoinKIC (S : {finLattice T}) :
  {in S &, forall x y, premeet S x (prejoin S y x) = x}.
Proof. exact: (@fmeetKUC _ _ S^~s). Qed.

Lemma fjoinKI (S : {finLattice T}) :
  {in S &, forall x y, premeet S x (prejoin S x y) = x}.
Proof. exact: (@fmeetKU _ _ S^~s). Qed.

End FJoin.
End FMeetJoinTheory.

(*Section FBigTheory.

Lemma mem_bigfmeet (S: {finLattice L})
  (r : seq T) (P : pred T) (F : T -> T) x :
  x \in r -> {in S, forall y, F y \in S} -> {in r, forall y, y \in S} ->
  \big[premeet S / x]_(i <- r | P i) F i \in S.
Proof.
move=> xr FS rS; rewrite big_seq_cond; apply: (big_ind (fun x => x \in S)).
- exact: rS.
- exact: mem_fmeet.
- by move=> i /andP [/rS /FS].
Qed.

Lemma mem_bigfjoin (S: {finLattice L})
  (r : seq T) (P : pred T) (F : T -> T) x :
  x \in r -> {in S, forall y, F y \in S} -> {in r, forall y, y \in S} ->
  \big[prejoin S / x]_(i <- r | P i) F i \in S.
Proof.
exact: (@mem_bigfmeet _ S^~s).
Qed.

(* TODO : new lemma names *)

Lemma fmeet_inf_seq_idx (S : {finLattice L})
  (r : seq T) (P : {pred T}) (F : T -> T) x :
  x \in r -> P x -> {in S, forall y, F y \in S} -> {in r, forall y, y \in S} ->
  \big[premeet S / F x]_(i <- r | P i) F i <=_L F x.
Proof.
move=> xr Px FS rS.
suff: (\big[premeet S / F x]_(i <- r | P i) F i <=_L F x) &&
(\big[premeet S / F x]_(i <- r | P i) F i \in S) by case/andP.
rewrite big_seq_cond; apply: (big_rec (fun y => (y <=_L F x) && (y \in S))).
- by rewrite lexx FS ?rS.
- move=> a b /andP [/rS aS _] /andP [bleFx bS].
  by rewrite lefIr ?mem_fmeet ?FS // rS.
Qed.

Lemma fmeet_max_seq (S : {finLattice L})
  (r : seq T) (P : {pred T}) (F : T -> T) x u:
  x \in r -> P x -> {in S, forall y, F y \in S} -> {in r, forall y, y \in S} ->
  F x <=_L u -> u \in S ->
  \big[premeet S / F x]_(i <- r | P i) F i <=_L u.
Proof.
move=> xr Px FS rS Fxleu uS.
suff: (\big[premeet S / F x]_(i <- r | P i) F i <=_L u) &&
(\big[premeet S / F x]_(i <- r | P i) F i \in S) by case/andP.
rewrite big_seq_cond; apply: (big_rec (fun y => (y <=_L u) && (y \in S))).
- by rewrite Fxleu FS ?rS.
- move=> a b /andP [/rS aS _] /andP [bleFx bS].
  by rewrite lefIr ?mem_fmeet ?FS //.
Qed.

Lemma fjoin_sumeet_seq (S : {finLattice L})
  (r : seq T) (P : {pred T}) (F : T -> T) x :
  x \in r -> P x -> {in S, forall y, F y \in S} -> {in r, forall y, y \in S} ->
  \big[prejoin S / F x]_(i <- r | P i) F i >=_L F x.
Proof. exact : (@fmeet_inf_seq _ S^~s). Qed.

Lemma fjoin_min_seq (S : {finLattice L})
  (r : seq T) (P : {pred T}) (F : T -> T) x u:
  x \in r -> P x -> {in S, forall y, F y \in S} -> {in r, forall y, y \in S} ->
  F x >=_L u -> u \in S ->
  \big[prejoin S / F x]_(i <- r | P i) F i >=_L u.
Proof. exact: (@fmeet_max_seq _ S^~s). Qed.

End FBigTheory.*)

End FinLatticeTheory.

(* -------------------------------------------------------------------- *)
Section TBDefs.

Section FPick.

Context {T : choiceType}.

(* TODO: move it *)
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

End FPick.

Definition fbot {disp : Order.disp_t} {T : prelatticeType disp} (S : {finLattice T}) : T :=
  if fpick S is Some x0 then
    \big[premeet S/x0]_(x <- S) x
  else
    witness.

Definition ftop {disp : Order.disp_t} {T : prelatticeType disp} (S : {finLattice T}) : T :=
  if fpick S is Some x0 then
    \big[prejoin S/x0]_(x <- S) x
  else
    witness.

End TBDefs.

Notation "\fbot_ S" := (@fbot _ _ S) (at level 2, S at next level, format "\fbot_ S").
Notation "\ftop_ S" := (@ftop _ _ S) (at level 2, S at next level, format "\ftop_ S").

Section TBFinLatticeTheory.

Implicit Type (disp : Order.disp_t).

Lemma fbot_def {disp} {T : prelatticeType disp} (S : {finLattice T}) x0 :
  x0 \in S -> \fbot_S = \big[premeet S/x0]_(x <- S) x.
Proof.
rewrite inE /fbot; case: fpickP => [->//|y0 y0_in_S x0_in_S].
rewrite big_seq [RHS]big_seq; apply: (big_idxx (Q := mem S)) => //;
  [exact: fmeetC| exact: fmeetA| exact: mem_fmeet| exact: fmeetxx].
Qed.

Lemma ftop_def {disp} {T : prelatticeType disp} (S : {finLattice T}) x0 :
  x0 \in S -> \ftop_S = \big[prejoin S/x0]_(x <- S) x.
Proof. exact: (@fbot_def _ _ S^~s). Qed.

Lemma mem_fbot {disp} {T : prelatticeType disp} (S : {finLattice T}) : \fbot_S \in S.
Proof.
case/fset0Pn: (finLattice_prop0 S)  => x0 x0S.
rewrite (fbot_def x0S) big_seq.
by apply/big_stable => //; apply/mem_fmeet.
Qed.

Lemma mem_ftop {disp} {T : prelatticeType disp} (S : {finLattice T}) : \ftop_S \in S.
Proof. exact: (@mem_fbot _ _ S^~s). Qed.

Lemma fbotE {disp} {T : prelatticeType disp} (S: {finLattice T}) :
  \fbot_S = \big[premeet S / \ftop_S]_(i <- S) i.
Proof. by rewrite (fbot_def (mem_ftop S)). Qed.

Lemma ftopE {disp} {T : prelatticeType disp} (S: {finLattice T}) :
  \ftop_S = \big[prejoin S / \fbot_S]_(i <- S) i.
Proof. exact: (@fbotE _ _ S^~s). Qed.

(* ----------------------------------------------------------------- *)

Lemma le0f {disp} {T : prelatticeType disp} (S : {finLattice T}) : {in S, forall x, \fbot_S <= x}.
Proof.
move => x xS; rewrite (fbot_def xS) big_seq.
rewrite (big_mem_sub _ _ _ _ xS xS)  ?leIfl //. (* TODO: FIX IT *)
apply/big_stable => //; apply/mem_fmeet.
- exact: fmeetC.
- exact: fmeetA.
- exact: mem_fmeet.
Qed.

Lemma fjoinf0 {disp} {T : prelatticeType disp} (S : {finLattice T}) : {in S, right_id \fbot_S (prejoin S)}.
Proof. by move=> x xS; apply/eqP; rewrite eq_fjoinl ?le0f ?mem_fbot. Qed.

Lemma fjoin0f {disp} {T : prelatticeType disp} (S : {finLattice T}): {in S, left_id \fbot_S (prejoin S)}.
Proof. by move=> x xS; apply/eqP; rewrite eq_fjoinr ?le0f ?mem_fbot. Qed.

Lemma lef1 {disp} {T : prelatticeType disp} (S : {finLattice T}) : {in S, forall x, x <= \ftop_S}.
Proof. move=> ??; exact: (@le0f _ _ S^~s). Qed.

Lemma fmeetf1 {disp} {T : prelatticeType disp} (S : {finLattice T}) : {in S, right_id \ftop_S (premeet S)}.
Proof. exact: (@fjoinf0 _ _ S^~s). Qed.

Lemma fmeet1f {disp} {T : prelatticeType disp} (S : {finLattice T}) : {in S, left_id \ftop_S (premeet S)}.
Proof. exact: (@fjoin0f _ _ S^~s). Qed.

Lemma ltf1 {disp} {T : prelatticeType disp} (S : {finLattice T}) :
  {in S, forall x, (x < \ftop_S) = (x != \ftop_S)}.
Proof. by move=> x xS; rewrite lt_neqAle ?lef1 ?andbT. Qed.

Lemma lt0f {disp} {T : prelatticeType disp} (S : {finLattice T}) :
  {in S, forall x, (\fbot_S < x) = (x != \fbot_S)}.
Proof. by move=> x xS; rewrite lt_def ?le0f ?andbT // eq_sym. Qed.

Lemma ftop_id {disp} {T : prelatticeType disp} (S: {finLattice T}) :
  {in S, forall t, (forall x, x \in S -> x <= t) -> \ftop_S = t}.
Proof.
move=> t tS ttop; apply/le_anti.
by rewrite lef1 //= andbT; apply/ttop; rewrite mem_ftop.
Qed.

Lemma fbot_id {disp} {T : prelatticeType disp} (S: {finLattice T}) :
  {in S, forall t, (forall x, x \in S -> x >= t) -> \fbot_S = t}.
Proof. exact: (@ftop_id _ _ S^~s). Qed.

Lemma fmeet0f {disp} {T : prelatticeType disp} (S : {finLattice T}) :
  {in S, left_zero \fbot_S (premeet S)}.
Proof. by move=> x xS; apply/eqP; rewrite -leEfmeet ?le0f ?mem_fbot. Qed.

Lemma fmeetf0 {disp} {T : prelatticeType disp} (S : {finLattice T}) :
  {in S, right_zero \fbot_S (premeet S)}.
Proof. by move=> x xS; apply/eqP; rewrite fmeetC -?leEfmeet ?le0f ?mem_fbot. Qed.

Lemma fjoin1f {disp} {T : prelatticeType disp} (S : {finLattice T}) :
  {in S, left_zero \ftop_S (prejoin S)}.
Proof. exact: (@fmeet0f _ _ S^~s). Qed.

Lemma fjoinf1 {disp} {T : prelatticeType disp} (S : {finLattice T}) :
  {in S, right_zero \ftop_S (prejoin S)}.
Proof. exact: (@fmeetf0 _ _ S^~s). Qed.

(* ------------------------------------------------------------------ *)

Section BigOpFinLattice.

Lemma mem_bigfmeet {disp : Order.disp_t} {T : prelatticeType disp} (S: {finLattice T})
  (r : seq T) (P : pred T) (F : T -> T):
  {in S, forall y, F y \in S} -> {subset r <= S} ->
  \big[premeet S / \ftop_S]_(i <- r | P i) F i \in S.
Proof.
move=> FS rS; rewrite big_seq_cond; apply: (big_ind (fun x => x \in S)).
- exact: mem_ftop.
- exact: mem_fmeet.
- by move=> i /andP [/rS /FS].
Qed.

Lemma mem_bigfjoin {disp} {T : prelatticeType disp} (S: {finLattice T})
  (r : seq T) (P : pred T) (F : T -> T):
  {in S, forall y, F y \in S} -> {subset r <= S} ->
  \big[prejoin S / \fbot_S]_(i <- r | P i) F i \in S.
Proof. exact: (@mem_bigfmeet _ _ S^~s). Qed.

Lemma fmeet_inf_seq {disp} {T : prelatticeType disp} (S: {finLattice T})
  (r: seq T) (P : pred T) (F : T -> T) x :
  {subset r <= S} -> {in S, forall y, F y \in S} -> x \in r -> P x ->
     \big[premeet S / \ftop_S]_(i <- r | P i) F i <= F x.
Proof.
move=> rS FS xr Px; rewrite big_map_fun.
have FxS: F x \in [seq F j | j <- r & P j] by
  apply/map_f; rewrite mem_filter Px xr.
rewrite big_seq.
have filtS: forall i, i \in [seq F j | j <- r & P j] -> i \in S by
  move=> i /mapP [j]; rewrite mem_filter => /andP [_ jS] ->; exact/FS/rS.
rewrite (big_mem_sub _ _ _ filtS _ FxS) ?lefIl
        ?(@big_stable _ _ _ _ _ filtS) ?mem_ftop ?mem_fmeet ?FS ?rS //. (* TODO: UGLY *)
- exact: mem_fmeet.
- exact: fmeetC.
- exact: fmeetA.
- exact: mem_fmeet.
Qed.

Lemma fjoin_sumeet_seq {disp} {T : prelatticeType disp} (S: {finLattice T})
  (r : seq T) (P : pred T) (F : T -> T) x :
  {subset r <= S} -> {in S, forall y, F y \in S} -> x \in r -> P x ->
     F x <= \big[prejoin S / \fbot_S]_(i <- r | P i) F i.
Proof. exact: (@fmeet_inf_seq _ _ S^~s). Qed.

Lemma fmeetsP {disp} {T : prelatticeType disp} (S : {finLattice T}) (P : pred T) (F : T -> T) x :
  {in S, forall y, P y -> x <= F y} -> x <= \big[premeet S / \ftop_S]_(y <- S | P y) F y.
Admitted.

Lemma fjoin_meets {disp} {T : prelatticeType disp} (S: {finLattice T}) x y :
  x \in S -> y \in S ->
  prejoin S x y = \big[premeet S / \ftop_S]_(i <- S | (x <= i) && (y <= i)) i.
Proof.
move=> xS yS; apply/le_anti/andP; split; last first.
- apply/fmeet_inf_seq; rewrite ?mem_fjoin //.
  by apply/andP; split; rewrite ?lefUl ?lefUr.
- by apply/fmeetsP=> ???; rewrite leUf.
Qed.

Lemma fjoinsP {disp} {T : prelatticeType disp} (S : {finLattice T}) (P : pred T) (F : T -> T) x :
  {in S, forall y, P y -> F y <= x} -> \big[prejoin S / \fbot_S]_(y <- S | P y) F y <= x.
Proof. exact: (@fmeetsP _ _ S^~s). Qed.

Lemma fmeet_joins {disp} {T : prelatticeType disp} (S: {finLattice T}) x y :
  x \in S -> y \in S ->
  premeet S x y = \big[prejoin S / \fbot_S]_(i <- S | (x >= i) && (y >= i)) i.
Proof. exact: (@fjoin_meets _ _ S^~s). Qed.

End BigOpFinLattice.
End TBFinLatticeTheory.

Module FinTBLatticeStructure.
Section FinTBLatticeStructure.

Context {disp : Order.disp_t} {T : prelatticeType disp} (S : {finLattice T}) (x0 : S).

Definition finbot := [`mem_fbot S].
Lemma finle0x : forall x, finbot <= x.
Proof. move=> x; exact/le0f/fsvalP. Qed.

Definition finBottomMixin := BottomMixin finle0x.

Definition fintop := [`mem_ftop S].
Lemma finlex1 : forall x, x <= fintop.
Proof. move=> x; exact/lef1/fsvalP. Qed.

Definition finTopMixin := TopMixin finlex1.

Local Canonical bPOrderType := BPOrderType S finBottomMixin.
Local Canonical tPOrderType := TPOrderType S finTopMixin.
Local Canonical bMeetSemilatticeType := [bMeetSemilatticeType of S].
Local Canonical tMeetSemilatticeType := [tMeetSemilatticeType of S].
Local Canonical tbMeetSemilatticeType := [tbMeetSemilatticeType of S].
Local Canonical bJoinSemilatticeType := [bJoinSemilatticeType of S].
Local Canonical tJoinSemilatticeType := [tJoinSemilatticeType of S].
Local Canonical tbJoinSemilatticeType := [tbJoinSemilatticeType of S].
Local Canonical bLatticeType := [bLatticeType of S].
Local Canonical tLatticeType := [tLatticeType of S].
Local Canonical tbLatticeType := [tbLatticeType of S].

Local Canonical finPOrderType := [finPOrderType of S].
Local Canonical finBPOrderType := [finBPOrderType of S].
Local Canonical finTPOrderType := [finTPOrderType of S].
Local Canonical finMeetSemilatticeType := [finMeetSemilatticeType of S].
Local Canonical finBMeetSemilatticeType := [finBMeetSemilatticeType of S].
Local Canonical finJoinSemilatticeType := [finJoinSemilatticeType of S].
Local Canonical finTJoinSemilatticeType := [finTJoinSemilatticeType of S].
Local Canonical finLatticeType := [finLatticeType of S].
Local Canonical finTBLatticeType := [finTBLatticeType of S].

End FinTBLatticeStructure.
Module Exports.
Notation finbot := finbot.
Notation fintop := fintop.
Coercion tbLatticeType : finLattice >-> Order.TBLattice.type.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical tbLatticeType.

Canonical finPOrderType.
Canonical finBPOrderType.
Canonical finTPOrderType.
Canonical finMeetSemilatticeType.
Canonical finBMeetSemilatticeType.
Canonical finJoinSemilatticeType.
Canonical finTJoinSemilatticeType.
Canonical finLatticeType.
Canonical finTBLatticeType.
End Exports.

End FinTBLatticeStructure.
Import FinTBLatticeStructure.Exports.

Section TestTBFinLattice.

Context {disp : Order.disp_t} {T : prelatticeType disp} {S : {finLattice T}}.
Context (a : S).
Context (I : Type) (F : I -> S).
Context (P : pred I).

Goal forall (r : seq I),
  val (\meet_(i <- r | P i) F i) =
  \big[premeet S / \ftop_S]_(i <- r | P i) val (F i).
Proof.
move=> r0; rewrite big_val_foo.
have ->: val (@Order.top _ S) = \ftop_S :> T by [].
apply: (eq_big_op (fun x => x \in S)); rewrite ?mem_ftop //.
- move=> ????; exact: fsvalP.
- by move=> x y xS yS; rewrite /val_fun2 !insubdK ?mem_fmeet.
- move=> ??; exact: fsvalP.
Qed.

End TestTBFinLattice.

(* ================================================================== *)
Section FinLattice1.

Lemma premeet_closed1 {disp} {T : prelatticeType disp} (a : T) :
  is_premeet_closed [fset a].
Proof.
apply/premeet_closedP=> ?? /fset1P-> /fset1P->; apply/fset1P.
apply/le_anti/andP; split.
- by apply/premeet_minl; rewrite fset11.
- by apply/premeet_inf; rewrite ?fset11.
Qed.

Lemma prejoin_closed1 {disp} {T : prelatticeType disp} (a : T) :
  is_prejoin_closed [fset a].
Proof. exact: (@premeet_closed1 _ [prelatticeType of T^d]). Qed.

Context {disp : Order.disp_t} {T : prelatticeType disp} (a : T).

(* Lemma is_lat1 : [&& premeet_closed [fset a],
                    prejoin_closed [fset a] & [fset a] != fset0].
Proof. by rewrite premeet_closed1 prejoin_closed1 -cardfs_eq0 cardfs1. Qed. *)

Program Definition lat1 := FinLattice (premeet_closed1 a) (prejoin_closed1 a) _.
Next Obligation. by rewrite -cardfs_gt0 cardfs1. Qed.

End FinLattice1.

Notation "[ 'finlattice' a 'for' T ]" := (@lat1 _ T a).

(* ==================================================================== *)
Section Atom.

Definition atom {disp} {T : prelatticeType disp} (S : {finLattice T}) a :=
  [&& a \in S, (\fbot_S < a) &
               ~~[exists x : S, (\fbot_S < val x) && (val x < a)]].

Definition coatom {disp} {T : prelatticeType disp} (S : {finLattice T}) a :=
  atom S^~s a.

Lemma atomP {disp} {T : prelatticeType disp} {S : {finLattice T}} {a} :
  reflect
    ([/\ a \in S, \fbot_S < a &
        forall x, x \in S -> \fbot_S < x -> ~~ (x < a)])
    (atom S a).
Proof.
apply/(iffP idP).
- case/and3P => /= -> -> /existsPn atomic; split => // y y_in_S bot_lt_y.
  by move: (atomic [`y_in_S]%fset); rewrite negb_and bot_lt_y /=.
- rewrite /atom; case=> [-> -> atomic]; apply/existsPn => x.
  by rewrite negb_and -implybE; apply/implyP/atomic/fsvalP.
Qed.

Lemma coatomP {disp} {T : prelatticeType disp} {S : {finLattice T}} {a} :
  reflect
    ([/\ a \in S, (a < \ftop_S) &
        forall x, x \in S -> x < \ftop_S -> ~~ (a < x)])
    (coatom S a).
Proof. exact: (@atomP _ [prelatticeType of T^d] S^~s). Qed.

Lemma mem_atom {disp} {T : prelatticeType disp} (S : {finLattice T}) x :
  atom S x -> x \in S.
Proof. by case/atomP. Qed.

Lemma mem_coatom {disp} {T : prelatticeType disp} (S : {finLattice T}) x :
  coatom S x -> x \in S.
Proof. by case/coatomP. Qed.

End Atom.

(* ==================================================================== *)
Module Interval.
Section Interval.

Definition umeet {disp} {T : prelatticeType disp} (S : {finLattice T}) a :=
  \big[premeet S / \ftop_S]_(i <- S | i >= a) i.

Definition djoin {disp} {T : prelatticeType disp} (S : {finLattice T}) b :=
  \big[prejoin S / \fbot_S]_(i <- S | i <= b) i.

Definition interval {disp} {T : prelatticeType disp} (S : {finLattice T}) (a b : T) :=
  [fset x | x in S &
    premeet S (umeet S a) (djoin S b) <= x <= prejoin S (umeet S a) (djoin S b)].

(* TODO: interval -> itv in the name of lemmas
 *
 *)

Lemma mem_itv {disp} {T : prelatticeType disp} (S : {finLattice T}) a b x :
  x \in S -> a <= x -> x <= b -> x \in interval S a b.
Proof.
move=> xS alex xleb; rewrite !inE xS /=.
apply/andP; split.
- apply : lefIl => //;
    [exact: mem_bigfmeet |exact: mem_bigfjoin |exact: fmeet_inf_seq].
- apply : leUfr => //;
    [exact: mem_bigfmeet |exact: mem_bigfjoin |exact: fjoin_sumeet_seq].
Qed.

Lemma umeetE {disp} {T : prelatticeType disp} (S : {finLattice T}) a : a \in S -> umeet S a = a.
Proof.
move=> aS; apply/le_anti; rewrite fmeet_inf_seq //=.
suff : ((\big[premeet S/ \ftop_S]_(i <- S | a <= i) i) \in S) &&
  (a <= (\big[premeet S/ \ftop_S]_(i <- S | a <= i) i)) by
  case/andP.
rewrite big_seq_cond.
rewrite (@big_stable _ _ _ (fun i => (i \in S) && (a <= i))) //.
- move=> x y /andP [xS alex] /andP [yS aley].
  by rewrite mem_fmeet //= lefI ?alex ?aley.
- by rewrite mem_ftop lef1.
Qed.

Lemma djoinE {disp} {T : prelatticeType disp} (S : {finLattice T}) b : b \in S -> djoin S b = b.
Proof. exact: (@umeetE _ _ S^~s). Qed.

Lemma mem_umeet {disp} {T : prelatticeType disp} (S : {finLattice T}) a : umeet S a \in S.
Proof. exact: mem_bigfmeet. Qed.

Lemma mem_djoin {disp} {T : prelatticeType disp} (S : {finLattice T}) b : djoin S b \in S.
Proof. exact: mem_bigfjoin. Qed.

Lemma itv_prop0 {disp} {T : prelatticeType disp} (S : {finLattice T}) a b :
  interval S a b != fset0.
Proof.
apply/fset0Pn; exists (premeet S (umeet S a) (djoin S b)).
rewrite !inE; apply/and3P; split => //.
- apply: mem_fmeet; [exact: mem_bigfmeet |exact: mem_bigfjoin].
- by rewrite lefIl ?mem_fjoin ?lefUl ?mem_umeet ?mem_djoin.
Qed.

Lemma intervalE {disp} {T : prelatticeType disp} (S : {finLattice T}) a b x :
  a \in S -> b \in S -> a <= b ->
  x \in interval S a b = (x \in S) && (a <= x <= b).
Proof.
move=> aS bS aleb; rewrite !inE umeetE ?djoinE //.
by move: (fmeet_l aS bS aleb) (fjoin_r aS bS aleb) => -> ->.
Qed.

Lemma intervalP {disp} {T : prelatticeType disp} (S : {finLattice T}) a b x :
  a \in S -> b \in S -> a <= b ->
  reflect
    (x \in S /\ a <= x <= b)
    (x \in interval S a b).
Proof. by move=> aS bS aleb; rewrite intervalE //; apply/andP. Qed.

Lemma itv_subset {disp} {T : prelatticeType disp} (S : {finLattice T}) a b :
  {subset interval S a b <= S}.
Proof. move=>?; by rewrite in_fsetE; case/and3P. Qed.

Lemma itv_bound {disp} {T : prelatticeType disp} (S : {finLattice T}) a b x:
  a \in S -> b \in S -> a <= b -> x \in interval S a b ->
  a <= x <= b.
Proof. by move => aS bS aleb /intervalP []. Qed.

Lemma dual_itv_fset_eq {disp} {T : prelatticeType disp} (S: {finLattice T}) a b:
  interval S a b = interval S^~s b a :> {fset T^d}.
Proof.
apply/eqP/fset_eqP=> x; rewrite !in_fsetE !inE [X in _ && X]andbC.
by rewrite fmeetC ?mem_umeet ?mem_djoin // fjoinC ?mem_umeet ?mem_djoin.
Qed.

Lemma itv_premeet_closed {disp} {T : prelatticeType disp} (S : {finLattice T}) x y a b:
  x \in interval S a b -> y \in interval S a b ->
  premeet S x y \in interval S a b.
Proof.
rewrite !in_fsetE => /and3P[xS alex xleb] /and3P[yS aley yleb].
apply/and3P; split.
- exact: mem_fmeet.
- by apply/premeet_inf=> //; apply/mem_fmeet; rewrite ?mem_umeet ?mem_djoin.
- by apply:(le_trans _ xleb); rewrite premeet_min.
Qed.

Lemma premeet_itvE {disp} {T : prelatticeType disp} (S : {finLattice T}) a b x y:
  x \in interval S a b -> y \in interval S a b ->
  premeet S x y = premeet (interval S a b) x y.
Proof.
move=> x_in y_in.
move: (x_in); rewrite in_fsetE // => /and3P[xS alex xleb].
move: (y_in); rewrite in_fsetE // => /and3P[yS aley yleb].
apply/le_anti/andP; split.
- by apply: premeet_inf=> //; first exact: itv_premeet_closed;
    rewrite premeet_min.
- apply: premeet_incr=> //; apply/fsubsetP=> ?; exact: itv_subset.
Qed.

Lemma itv_prejoin_closed {disp} {T : prelatticeType disp} (S : {finLattice T}) x y a b:
  x \in interval S a b -> y \in interval S a b ->
  prejoin S x y \in interval S a b.
Proof. rewrite dual_itv_fset_eq -premeetEdual; exact: (@itv_premeet_closed _ _ S^~s). Qed.

Lemma prejoin_itvE {disp} {T : prelatticeType disp} (S: {finLattice T}) a b x y:
  x \in interval S a b -> y \in interval S a b ->
  prejoin S x y = prejoin (interval S a b) x y.
Proof. rewrite dual_itv_fset_eq -premeetEdual; exact: (@premeet_itvE _ _ S^~s). Qed.

(* Lemma closed_itv {T0} {cls : PreLattice.class_of T0}
      (T := PreLattice.Pack Order.disp_tt cls) (S:{finLattice T}) a b :
  [&& premeet_closed (interval S a b),
      prejoin_closed (interval S a b) & interval S a b != fset0].
Proof.
apply/and3P; split.
- apply/premeet_closedP => ? ? ? ?.
  by rewrite -premeet_itvE // itv_premeet_closed.
- apply/prejoin_closedP => ? ? ? ?.
  by rewrite -prejoin_itvE // itv_prejoin_closed.
- exact: itv_prop0.
Qed. *)

Lemma itv_closed_meet {disp} {T : prelatticeType disp} (S: {finLattice T}) a b:
  is_premeet_closed (interval S a b).
Proof. 
apply/premeet_closedP=> /= ????. 
by rewrite -premeet_itvE // itv_premeet_closed.
Qed.

Lemma itv_closed_join {disp} {T : prelatticeType disp} (S: {finLattice T}) a b:
  is_prejoin_closed (interval S a b).
Proof. 
apply/prejoin_closedP=> /= ????. 
by rewrite -prejoin_itvE // itv_prejoin_closed.
Qed.


Definition FinLatInterval {disp} {T : prelatticeType disp} (S: {finLattice T}) a b :
  {finLattice T} :=
  (* TODO: lock this definition *)
  FinLattice (itv_closed_meet S a b) (itv_closed_join S a b) (itv_prop0 S a b).

End Interval.
Module Exports.
Notation " [< a ; b >]_ S " := (@FinLatInterval _ _ S a b)
  (at level 8, S at level 8, format "[<  a ;  b  >]_ S").
Notation umeet := umeet.
Notation djoin := djoin.
End Exports.
End Interval.
Import Interval.Exports.

Section IntervalTheory.

Section UmeetDjoin.

Lemma mem_umeet {disp} {T : prelatticeType disp} (S : {finLattice T}) a: umeet S a \in S.
Proof. exact: Interval.mem_umeet. Qed.

Lemma mem_djoin {disp} {T : prelatticeType disp} (S : {finLattice T}) b: djoin S b \in S.
Proof. exact: Interval.mem_djoin. Qed.

Lemma umeetE {disp} {T : prelatticeType disp} (S : {finLattice T}) a: a \in S -> umeet S a = a.
Proof. exact: Interval.umeetE. Qed.

Lemma djoinE {disp} {T : prelatticeType disp} (S : {finLattice T}) b: b \in S -> djoin S b = b.
Proof. exact: Interval.djoinE. Qed.

Lemma le_umeet {disp} {T : prelatticeType disp} (S : {finLattice T}) a b :
  b \in S -> a <= b -> umeet S a <= b.
Proof. by move=> bS aleb; apply: fmeet_inf_seq. Qed.

Lemma le_djoin {disp} {T : prelatticeType disp} (S : {finLattice T}) a b :
  a \in S -> a <= b -> djoin S b >= a.
Proof. by move=> aS aleb; apply: fjoin_sumeet_seq. Qed.

End UmeetDjoin.

Lemma fmeet_itvE {disp} {T : prelatticeType disp} (S : {finLattice T}) a b :
  {in [<a; b>]_S &, premeet ([< a ; b >]_S) =2 premeet S}.
Proof. by move => x y x_in y_in; rewrite -Interval.premeet_itvE. Qed.

Lemma fjoin_itvE {disp} {T : prelatticeType disp} (S : {finLattice T}) a b :
  {in [<a; b>]_S &, prejoin ([< a ; b >]_S) =2 prejoin S}.
Proof. by move => x y x_in y_in; rewrite -Interval.prejoin_itvE. Qed.

Lemma mem_itv {disp} {T : prelatticeType disp} (S : {finLattice T}) a b x :
  x \in S -> a <= x -> x <= b -> x \in [< a ; b >]_S.
Proof. exact: Interval.mem_itv. Qed.

Lemma intervalE {disp} {T : prelatticeType disp} (S : {finLattice T}) a b x :
  a \in S -> b \in S -> a <= b ->
  x \in [< a ; b >]_S = (x \in S) && (a <= x <= b).
Proof. exact: Interval.intervalE. Qed.

Lemma intervalP {disp} {T : prelatticeType disp} (S: {finLattice T}) a b x:
  a \in S -> b \in S -> a <= b ->
  reflect
   (x \in S /\ a <= x <= b)
    (x \in [< a ; b >]_S).
Proof. exact: Interval.intervalP. Qed.

Lemma itv_subset {disp} {T : prelatticeType disp} (S: {finLattice T}) a b x :
  x \in [< a ; b >]_S -> x \in S.
Proof. exact: Interval.itv_subset. Qed.
Lemma itv_bigrange {disp} {T : prelatticeType disp} (S: {finLattice T}) a b x :
  x \in [< a ; b >]_S ->
  premeet S (umeet S a) (djoin S b) <= x <= prejoin S (umeet S a) (djoin S b).
Proof. by rewrite !inE /=; case/andP. Qed.

Lemma itv_geL {disp} {T : prelatticeType disp} (S: {finLattice T}) a b x :
  a \in S -> a <= b -> x \in [< a ; b >]_S -> a <= x.
Proof.
move=> aS aleb /itv_bigrange /andP [+ _].
by rewrite (umeetE aS) (fmeet_l aS (mem_djoin S b) (le_djoin aS aleb)).
Qed.

Lemma itv_leR {disp} {T : prelatticeType disp} (S: {finLattice T}) a b x :
  b \in S -> a <= b -> x \in [< a ; b >]_S -> x <= b.
Proof.
move=> bS aleb /itv_bigrange /andP [_].
by rewrite (djoinE bS) (fjoin_r (mem_umeet S a) bS (le_umeet bS aleb)).
Qed.
(*Proof. by move=> bS; rewrite !inE Interval.join_bar // => /and3P []. Qed.*)

Lemma itv_id {disp} {T : prelatticeType disp} (S: {finLattice T}) : [<\fbot_S; \ftop_S>]_S = S.
Proof.
apply/eqP/fset_eqP => x.
rewrite !inE; apply: andb_idr => xS.
rewrite ?Interval.umeetE ?Interval.djoinE ?mem_fbot ?mem_ftop //.
by rewrite fmeet_l ?fjoin_r ?le0f ?lef1 ?mem_fbot ?mem_ftop.
Qed.

Lemma mono_itv {disp} {T : prelatticeType disp} (S : {finLattice T}) (A B a b : T) :
  A \in S -> B \in S -> A <= B ->
  a \in [< A; B >]_S -> b \in [<A ; B >]_S -> a <= b ->
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

Lemma sub_itv {disp} {T : prelatticeType disp} (S : {finLattice T}) a b c d:
  a \in S -> b \in S -> c \in S -> d \in S ->
  a <= b -> c <= d ->
  ([<a;b>]_S `<=` [<c;d>]_S)%fset = (c <= a) && (b <= d).
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

Lemma dual_itv_r {disp} {T : prelatticeType disp} (S : {finLattice T}) a b :
  ([<a; b>]_S)^~s = [< b ; a>]_S^~s.
Proof. exact/val_inj/Interval.dual_itv_fset_eq. Qed.

Definition dual_itv :=
  (@dual_itv_r, fun {disp} {T : prelatticeType disp} => @dual_itv_r _ [prelatticeType of T^d]).

Lemma mem_itvL {disp} {T : prelatticeType disp} (S : {finLattice T}) (x y : T) :
  x \in S -> x <= y -> x \in [< x; y >]_S.
Proof. by move=> xS xy; apply/Interval.mem_itv. Qed.

Lemma mem_itvR {disp} {T : prelatticeType disp} (S : {finLattice T}) (x y : T) :
  y \in S -> x <= y -> y \in [< x; y >]_S.
Proof.
by move/(@mem_itvL _ _ (S^~s))/[apply]; rewrite -dual_itv.
Qed.
(* TODO: compare with the previous proof *
 * have -> : S = (S^~s)^~s by exact/val_inj.
   rewrite -dual_itv => ??; exact: mem_itvL. *)

Lemma mem_0itv {disp} {T : prelatticeType disp} (S : {finLattice T}) (y : T) :
  y \in S -> \fbot_S \in [< \fbot_S; y >]_S.
Proof. by move=> yS; rewrite mem_itv ?le0f ?mem_fbot. Qed.

Lemma mem_itv1 {disp} {T : prelatticeType disp} (S : {finLattice T}) (x : T) :
  x \in S -> \ftop_S \in [< x; \ftop_S >]_S.
Proof.
by move/(@mem_0itv _ _ (S^~s)); rewrite -dual_itv.
Qed.
(* TODO: compare with
 * have -> : S = (S^~s)^~s by exact/val_inj.
   rewrite -dual_itv => ?. exact: mem_0itv. *)

Lemma itvE0 {disp} {T : prelatticeType disp} (S : {finLattice T}) :
  {in S &, forall a b, a <= b -> \fbot_([<a; b>]_S) = a}.
Proof.
move=> a b aS bS aleb; apply: fbot_id; rewrite ?mem_itv //.
move=> x; exact: itv_geL.
Qed.

Lemma itvE1 {disp} {T : prelatticeType disp} (S : {finLattice T}):
  {in S &, forall a b, a <= b -> \ftop_([<a; b>]_S) = b}.
Proof.
move=> a b /[swap].
by move/(itvE0 (S := S^~s))/[apply]/[apply]; rewrite -dual_itv.
Qed.
(* TODO: compare with
 * move=> a b aS bS aleb.
   have -> : S = (S^~s)^~s by exact/val_inj.
   rewrite -dual_itv; exact : itvE0. *)

Lemma sub_atomic {disp} {T : prelatticeType disp} (S: {finLattice T}) x:
  x \in S -> \fbot_S < x ->
  exists2 y, atom S y & y <= x.
Proof.
set S' : {fset T} := ([< \fbot_S; x >]_S `\` [fset \fbot_S; x])%fset.
move=> xS botltx.
case/boolP: (S' == fset0).
- rewrite fsetD_eq0 => /fsubsetP intv_sub.
  exists x => //; apply/atomP; rewrite xS botltx; split=> //.
  move=> y yS; apply: contraTN => yltx.
  have/intv_sub : y \in [< \fbot_S; x >]_S by
    rewrite mem_itv ?le0f ?(ltW yltx).
  by rewrite !inE (lt_eqF yltx) orbF; move/eqP => ->; rewrite ltxx.
(* QC : minset_neq0 -> minset_neq0 T *)
- case/(minset_neq0 T)/fset0Pn => y /mem_minsetE.
  rewrite in_fsetD intervalE ?mem_fbot //; [|rewrite le0f //].
  case => /and3P [].
  rewrite !inE negb_or => /andP [ynbot ynx] yS /andP [boty ylex] miny.
  exists y=> //.
  apply/atomP; rewrite yS lt_neqAle boty eq_sym ynbot; split => //.
  move=> z zS botltz; apply: contraT; rewrite negbK => zlty.
  (* QC : TODO : minset still use relorder structures, so we need to unfold Order.lt here *)
  suff/miny: z \in S' by move: zlty; rewrite /Order.lt /= => ->.
  rewrite in_fsetD intervalE ?le0f ?zS ?mem_fbot //= ?inE.
  rewrite negb_or eq_sym (lt_eqF botltz).
  have zltx := (lt_le_trans zlty ylex).
  by rewrite (lt_eqF zltx) (ltW zltx).
Qed.

Lemma sub_coatomic {disp} {T : prelatticeType disp} (S: {finLattice T}) x:
  x \in S -> x < \ftop_S -> exists2 y, coatom S y & x <= y.
Proof. exact: (@sub_atomic _ _ S^~s). Qed.


(* -------------------------------------------------------------------- *)
Section IndIncr.

Context {disp : Order.disp_t} {T : prelatticeType disp}.
Variable (P : {finLattice T} -> Prop).

Hypothesis (P_incr : forall S, forall x,
  atom S x -> P S -> P [<x; \ftop_S>]_S).

Lemma ind_incr (S : {finLattice T}) (x : T) :
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
have bot_lt_x: \fbot_S < x by rewrite lt_def neq0_x le0f.
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

(* TODO: this is where things stop working *)

(* -------------------------------------------------------------------- *)
Section IndDecr.

Lemma dualK (disp : Order.disp_t) (T : prelatticeType disp) (S : {finLattice T}) :
  (S^~s)^~s = S.
Proof. by exact/val_inj. Qed.

(*Variable (disp : Order.disp_t) (T : prelatticeType disp).
Check ([prelatticeType of T^d]).
Variable (S : {finLattice [prelatticeType of T^d]}).
*)

Lemma fbot_dual_r (disp : Order.disp_t) (T : prelatticeType disp) (S : {finLattice T}) :
  \fbot_(S^~s) = \ftop_S.
Proof. by []. Qed.

Context {disp : Order.disp_t} {T : prelatticeType disp}.
Variable (P : {finLattice T} -> Prop).

Hypothesis (P_decr : forall S, forall x,
  coatom S x -> P S -> P [<\fbot_S; x>]_S).

Lemma ind_decr (S : {finLattice T}) (x : T) :
  x \in S -> P S -> P [<\fbot_S; x>]_S.
Proof.
rewrite -[[<_;_>]__]dualK.
rewrite [([<_;_>]__)^~s]dual_itv.
have ->: \fbot_S = \ftop_(S^~s) by [].
move=> xS PS.
pose P' := (fun S' : {finLattice T^d} => P S'^~s).
have:= @ind_incr _ _ P' _ S^~s x xS PS; apply. 
move=> S' x'; rewrite /P' dual_itv -fbot_dual_r=> atom_S' PS'.
have:= @P_decr S'^~s x' atom_S' PS'.
congr P; exact/val_inj. 
Qed.

(* move=> x_in_S PS.
rewrite -[S]dualK -dual_itv fbot_dual.
apply: (ind_incr (P := fun S' : finLattice L^~pl => P S'^~s)) => //.
rewrite fbot_dual_r.
apply: (ind_incr (P := fun S' : finLattice [preLattice of dual_rel <=:L] => P S'^~s)) => //.
- by move=> S' x' ??; rewrite dual_itv; apply: P_decr.
- by rewrite dualK.
Qed. *)

End IndDecr.

(* -------------------------------------------------------------------- *)
Section Ind.
Context {disp : Order.disp_t} {T : prelatticeType disp}.
Variable (P : {finLattice T} -> Prop).

Hypothesis (P_incr : forall (S: {finLattice T}), forall x,
  atom S x -> P S -> P [<x; \ftop_S>]_S).
Hypothesis (P_decr : forall (S:{finLattice T}), forall x,
  coatom S x -> P S -> P [<\fbot_S; x>]_S).

Lemma ind_id (S : {finLattice T}) (x y : T) :
  x \in S -> y \in S -> x <= y -> P S -> P [<x; y>]_S.
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
Context {disp : Order.disp_t} {T : prelatticeType disp} (S: {fset T}).

Definition axiom (f : T -> T) :=
  {in S&, {morph f : x y / premeet S x y >-> premeet (f @` S) x y}}
  /\ {in S&, {morph f : x y / prejoin S x y >-> prejoin (f @`S) x y}}.

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
Notation "{ 'fmorphism' S }" := (map (Phant S))
  (at level 0, format "{ 'fmorphism'  S }").
End Exports.
End Morphism.
Import Morphism.Exports.

(* -------------------------------------------------------------------- *)

Section FinLatticeImg.

Context {disp : Order.disp_t} {T : prelatticeType disp}.
Context {S : {finLattice T}} (f : {fmorphism S}).

Notation finLatImg := (f @`(S : {fset _})).

Lemma finLatImg_prop0 : finLatImg != fset0.
Proof.
case/fset0Pn : (finLattice_prop0 S) => x xS; apply/fset0Pn; exists (f x).
exact: in_imfset.
Qed.

Lemma fmorph_premeet :
  {in S&, {morph f : x y / premeet S x y >-> premeet finLatImg x y}}.
Proof. by case: f => ? []. Qed.

Lemma fmorph_prejoin :
  {in S&, {morph f : x y / prejoin S x y >-> prejoin finLatImg x y}}.
Proof. by case: f => ? []. Qed.


Lemma finLatImg_premeet_closed : is_premeet_closed finLatImg.
Proof.
apply/premeet_closedP => x y /imfsetP + /imfsetP.
case => x' x'S -> [y' y'S ->].
rewrite -fmorph_premeet ?in_imfset //.
exact : (mem_fmeet x'S y'S).
Qed.

Lemma finLatImg_prejoin_closed : is_prejoin_closed finLatImg.
Proof.
apply/prejoin_closedP => x y /imfsetP + /imfsetP /=.
case => x' x'S -> [y' y'S ->].
rewrite -fmorph_prejoin ?in_imfset //.
exact : (mem_fjoin x'S y'S).
Qed.

(* Lemma finLatImg_finLat :
  [&& is_prejoin_closed finLatImg,
  premeet_closed (L^~pl) finLatImg &
  finLatImg != fset0].
Proof.
by rewrite finLatImg_prop0 finLatImg_premeet_closed
  finLatImg_prejoin_closed.
Qed. *)

Canonical finLatImg_finLattice : {finLattice T} := 
  FinLattice finLatImg_premeet_closed finLatImg_prejoin_closed finLatImg_prop0.

End FinLatticeImg.

Notation "'\codom' f" := (@finLatImg_finLattice _ _ _ f)
  (at level 24, format "'\codom'  f").

Section MorphismTheory.
Context {disp : Order.disp_t} {T : prelatticeType disp}.

Lemma fmorphismP (S : {fset T}) (f : {fmorphism S}) :
  fmorphism S f.
Proof. by case : f. Qed.

Lemma fmorphI (S : {finLattice T}) (f : {fmorphism S}) :
  {in S &, {morph f : x y / premeet S x y >-> premeet (\codom f) x y}}.
Proof. by case: (fmorphismP f). Qed.

Lemma fmorphU (S : {finLattice T}) (f : {fmorphism S}) :
  {in S &, {morph f : x y / prejoin S x y >-> prejoin (\codom f) x y}}.
Proof. by case: (fmorphismP f). Qed.

Lemma codomP (S1 S2 : {finLattice T}) (f : {fmorphism S1}) :
  f @` (S1 : {fset _}) = S2 -> \codom f = S2.
Proof. move=> ?; exact: val_inj. Qed.

(* ------------------------------------------------------------------- *)

(*Lemma meet_morph_homo L (S: {finLattice T}) f :
  {in S &, {morph f : x y / premeet L S x y >->
    premeet L (f @` (S : {fset _})) x y}} ->
  {in S &, {homo f : x y / x <= y}}.
Proof.
move=> f_morph x y xS yS xley.
suff <-: premeet L (f @` (S : {fset _})) (f x) (f y) = f x by
  rewrite premeet_minr // in_imfset.
rewrite -f_morph //; congr f. apply: (@le_anti _ L).
by rewrite premeet_minl ?premeet_inf.
Qed.

Lemma meet_morph_mono L (S : {finLattice T}) f :
  {in S &, {morph f : x y / premeet L S x y >->
    premeet L (f @` (S : {fset _})) x y}} ->
  {in S &, injective f} -> {in S &, {mono f : x y / x <= y}}.
Proof.
move=> f_morph f_inj x y xS yS.
apply/(sameP idP)/(iffP idP); first exact: (meet_morph_homo f_morph).
move=> fxlefy.
suff: premeet L (f @` (S : {fset _})) (f x) (f y) == (f x).
- rewrite -f_morph ?(inj_in_eq f_inj) ?(mem_fmeet xS) //.
  move/eqP => <-; exact: premeet_minr.
by apply/eqP/(@le_anti _ L); rewrite premeet_minl ?premeet_inf ?in_imfset.
Qed.

Lemma meet_fmorphism L (S : {finLattice T}) f :
  {in S &, {morph f : x y / premeet L S x y >->
    premeet L (f @` (S : {fset _})) x y}} ->
  {in S &, injective f} -> fmorphism L S f.
Proof.
move=> f_morph f_inj; rewrite /(fmorphism _).
have f_mono := (meet_morph_mono f_morph f_inj).
split; first exact: f_morph.
move=> x y xS yS; apply/(@le_anti _ L)/andP; split.
Admitted.

(*Lemma meet_fmorphism L (S1 S2 : {finLattice T}) (f : T -> T) :
  {in S1, forall x, f x \in S2} ->
  {in S1&, {morph f : x y / premeet S1 x y >-> premeet S2 x y}} ->
  {in S1 & on S2, bijective f} -> fmorphism L S1 S2 f.
Proof.
move=> f_im f_morph [g] [g_im fgK gfK].
have f_mono := (meet_morph_mono f_im f_morph (can_in_inj fgK)).
split => //.
+ move=> x y xS yS.
  apply/(@le_anti _ L)/andP; split.
  - rewrite -[X in (_ <=__ X)]gfK ?f_mono ?leUf ?g_im ?mem_fjoin ?f_im //.
    rewrite -f_mono ?g_im ?mem_fjoin ?f_im //.
    rewrite -[X in _ && X]f_mono ?g_im ?mem_fjoin ?f_im //.
    by rewrite gfK ?lefUl ?lefUr ?mem_fjoin ?f_im.
  - by rewrite leUf ?f_mono ?lefUl ?lefUr ?f_im ?mem_fjoin.
+ apply/(@le_anti _ L)/andP; split; rewrite ?le0f ?f_im ?mem_fbot //.
  by rewrite -[X in (_ <=__ X)]gfK ?f_mono ?le0f ?g_im ?mem_fbot.
+ apply/(@le_anti _ L)/andP; split; rewrite ?lef1 ?f_im ?mem_fbot //.
  by rewrite -[X in (X <=__ _)]gfK ?f_mono ?lef1 ?g_im ?mem_fbot.
Qed.*)

Lemma dual_fmorphism L (S : {finLattice T}) (f : T -> T) :
  fmorphism L S f <-> fmorphism L S^~s f.
Proof. by split; case; split. Qed.

Lemma join_fmorphism L (S : {finLattice T}) (f : T -> T) :
  {in S &, {morph f : x y / prejoin L S x y >->
    prejoin L (f @` (S : {fset _})) x y}} ->
  {in S &, injective f} -> fmorphism L S f.
Proof.
move=> morph_join inj; apply/dual_fmorphism.
by move: (@meet_fmorphism _ S^~s f) => /(_ morph_join inj) [].
Qed.*)

(* ----------------------------------------------------------------- *)
(*Context (L : {preLattice T}) (S : {finLattice T}).
Context (f g : {fmorphism S on L}).*)



Lemma fmorph0 (S : {finLattice T}) (f : {fmorphism S}):
  f \fbot_S = \fbot_(\codom f).
Proof.
symmetry; apply: fbot_id; first exact/in_imfset/mem_fbot.
move=> y /imfsetP [x xS ->].
have fxfS: f x \in (\codom f) by rewrite in_imfset.
by rewrite (leEfmeet _ fxfS) ?in_imfset -?fmorphI ?mem_fbot ?fmeet0f.
Qed.

Lemma fmorph1 (S : {finLattice T}) (f : {fmorphism S}):
  f \ftop_S = \ftop_(\codom f).
Proof.
symmetry; apply: ftop_id; first exact/in_imfset/mem_ftop.
move=> y /imfsetP [x xS ->].
have fxfS: f x \in (\codom f) by rewrite in_imfset.
by rewrite (leEfmeet fxfS) ?in_imfset -?fmorphI ?mem_ftop ?fmeetf1.
Qed.

Lemma fmorph_homo (S : {finLattice T}) (f : {fmorphism S}):
  {in S&, {homo f : x y / x <= y}}.
Proof.
move=> x y xS yS; rewrite (leEfjoin xS) // => /eqP.
move/(congr1 f); rewrite fmorphU // => <-.
by apply/lefUr; rewrite in_imfset.
Qed.

Lemma fmorph_mono (S : {finLattice T}) (f : {fmorphism S}):
  {in S&, injective f} -> {in S&, {mono f : x y / x <= y}}.
Proof.
move=> f_inj x y xS yS; rewrite (leEfjoin xS) //.
rewrite (@leEfjoin _ _ (\codom f)) ?in_imfset //.
by rewrite -fmorphU //; apply/(inj_in_eq f_inj)=> //; apply: mem_fjoin.
Qed.

Lemma fmorph_monolt (S : {finLattice T}) (f : {fmorphism S}):
  {in S&, injective f} -> {in S&, {mono f : x y / x < y}}.
Proof.
move=> f_inj x y xS yS; rewrite !lt_def; congr (_ && _).
- apply/(sameP idP)/(iffP idP); first exact/contra_neq/f_inj.
  by apply/contra_neq => ->.
- exact: fmorph_mono.
Qed.

Lemma mem_fmorphP (S : {finLattice T}) (f : {fmorphism S}) x:
  reflect (exists2 y, y \in S & f y = x) (x \in (\codom f)).
Proof.
apply/(iffP idP).
- by case/imfsetP => y /= yS ->; exists y.
- by case => y yS <-; rewrite in_imfset.
Qed.

Lemma mem_fmorph (S : {finLattice T}) (f : {fmorphism S}) x:
  x \in S -> f x \in (\codom f).
Proof. by move=> xS; rewrite in_imfset. Qed.

End MorphismTheory.

Section IsoFMorph.

Context {disp : Order.disp_t} {T : prelatticeType disp}.
Context (S1 S2 : {fset T}).

Definition morphic_fmeet (f : T -> T) :=
  [forall x: S1, [forall y : S1,
  f (premeet S1 (fsval x) (fsval y)) ==
  premeet (f @` (S1 : {fset _})) (f (fsval x)) (f (fsval y))]].

Definition morphic_fjoin (f : T -> T) :=
  [forall x: S1, [forall y : S1,
  f (prejoin S1 (fsval x) (fsval y)) ==
  prejoin (f @` (S1 : {fset _})) (f (fsval x)) (f (fsval y))]].

Definition morphic (f : T -> T) := morphic_fmeet f && morphic_fjoin f.

Definition injf (f : T -> T) :=
  [forall x : S1, [forall y : S1,
  (f (fsval x) == f (fsval y)) ==> (fsval x == fsval y)]].

Definition surjf (f : T -> T) := f @` (S1 : {fset _}) == S2.

Definition misof f := [&& morphic f, injf f & surjf f].

(*Definition val_ffun (f : {ffun S1 -> S2}) :=
  fun x : T => fsval (f (insubd [`mem_fbot S1] x)).*)

Definition isof := exists f : T -> T, misof f.

Lemma morphicP (f : T -> T): reflect (fmorphism S1 f) (morphic f).
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
  ([/\ fmorphism S1 f, {in S1&, injective f} & f @` (S1 : {fset _}) = S2])
  (misof f).
Proof. apply/and3PP; [exact/morphicP | exact/injfP |exact/eqP]. Qed.

Lemma misof_isof (f : T -> T):
  misof f -> isof.
Proof. by move=> ?; exists f. Qed.

Lemma misof_fmorph (f : T -> T) :
  misof f -> exists2 g : {fmorphism S1}, misof g & f =1 g.
Proof.
case/misofP => f_morph f_inj f_surj.
by exists (FMorphism f_morph) => //; apply/misofP.
Qed.


Lemma isofP :
  (exists f, [/\ fmorphism S1 f, {in S1&, injective f} & f @` S1 = S2]) <->
  (isof).
Proof.
split.
- case => f [f_morph f_inj f_surj]; exists f; exact/misofP.
- by case => f /misofP ?; exists f.
Qed.

End IsoFMorph.

Section IsoFmorphTheory.

Context {disp : Order.disp_t} {T : prelatticeType disp}.

Lemma misof0 (S1 S2: {finLattice T})
  (f : T -> T) :
  misof S1 S2 f -> f \fbot_S1 = \fbot_S2.
Proof.
case/misofP => [[f_morphI f_morphU] f_inj f_surj].
symmetry; apply: fbot_id; rewrite ?inE -?f_surj ?in_imfset ?mem_fbot //.
move=> x; rewrite inE -f_surj => /imfsetP [y /= yS1 ->].
rewrite (leEfmeet (S:=S2)) ?inE ?fmeetE -?f_surj ?in_imfset ?mem_fbot //.
rewrite -f_morphI ?mem_fbot //; apply/eqP; congr f.
by rewrite fmeet0f.
Qed.

Lemma misof1 (S1 S2: {finLattice T})
  (f : T -> T) :
  misof S1 S2 f -> f \ftop_S1 = \ftop_S2.
Proof.
case/misofP => [[f_morphI f_morphU] f_inj f_surj].
symmetry; apply: ftop_id; rewrite ?inE -?f_surj ?in_imfset ?mem_ftop //.
move=> x; rewrite inE -f_surj => /imfsetP [y /= yS1 ->].
rewrite (leEfjoin (S:=S2)) ?inE ?fjoinE -?f_surj ?in_imfset ?mem_ftop //.
rewrite -f_morphU ?mem_ftop //; apply/eqP; congr f.
by rewrite fjoin1f.
Qed.

Section ItvMorph.

Lemma fmorph_itv (S : {finLattice T}) (f: {fmorphism S}) a b :
  a \in S -> b \in S -> a <= b -> {in S&, injective f} ->
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

Lemma itv_isomorph (S1 S2 : {finLattice T})
  (f : T -> T) a b:
  a \in S1 -> b \in S1 -> a <= b ->
  misof S1 S2 f ->
  misof [<a ; b>]_S1 (f @` ([< a ; b >]_S1 : {fset _})) f.
Proof.
move=> aS1 bS1 aleb /misof_fmorph [g].
case/misofP => _ g_inj g_surj g_eq.
have g_fset: forall S: {fset _}, f @` S = g @` S
  by move=> S; apply/fsetP => z; apply/idP/idP => /imfsetP [x xS ->];
    rewrite -?g_eq ?in_imfset ?g_eq ?in_imfset.
apply/misofP; split => //; first split.
- move=> x y x_itv y_itv.
  rewrite !g_eq g_fset fmorph_itv // !fmeet_itvE //;
    last 1 [rewrite inE -fmorph_itv // in_imfset |
            rewrite inE -fmorph_itv // in_imfset]; rewrite //.
  by apply: fmorphI; rewrite ?(itv_subset x_itv) ?(itv_subset y_itv).
- move=> x y x_itv y_itv.
  rewrite !g_eq g_fset fmorph_itv // !fjoin_itvE //;
    last 1 [rewrite inE -fmorph_itv // in_imfset |
            rewrite inE -fmorph_itv // in_imfset]; rewrite //.
  by apply: fmorphU; rewrite ?(itv_subset x_itv) ?(itv_subset y_itv).
- move=> ? ? /itv_subset ? /itv_subset ?; rewrite !g_eq; exact: g_inj.
Qed.

Lemma fmorph_atom (S1 S2 : {finLattice T})
  (f : T -> T) x :
  misof S1 S2 f -> atom S1 x -> atom S2 (f x).
Proof.
case/misof_fmorph => g misof_g ->.
case/misofP : (misof_g) => [_ g_inj g_surj].
case/atomP => xS1 l0tx x_min; apply/atomP; split.
- by rewrite inE -g_surj in_imfset.
- by rewrite -(misof0 misof_g) fmorph_monolt ?mem_fbot.
- move=> y; rewrite inE -g_surj => /imfsetP [x0 /= x0S1 ->].
  rewrite -(misof0 misof_g) !fmorph_monolt ?mem_fbot //.
  exact:x_min.
Qed.


End ItvMorph.


Section BijMorphism.

Lemma isof_refl (S : {finLattice T}): isof S S.
Proof.
have idmorph: fmorphism S id by
  split => x y xS yS /=; rewrite imfset_id.
by apply/isofP; exists id; split=> //=; rewrite imfset_id.
Qed.

Lemma isof_sym (S1 S2 : {finLattice T}):
  isof S1 S2 -> isof S2 S1.
Proof.
case/isofP => f [[f_morphI f_morphU] f_inj f_surj].
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
  rewrite cancel_r ?f_surj ?mem_fmeet ?f_morphI ?cancel_r ?gS1 //.
  by congr premeet; rewrite -f_surj.
- move=> x y xS2 yS2; apply: f_inj;
  rewrite ?gS1 ?mem_fjoin // -?f_surj -?imfset_comp /= ?gfS1 ?mem_fjoin ?gS1 //.
  rewrite cancel_r ?f_surj ?mem_fjoin ?f_morphU ?cancel_r ?gS1 //.
  by congr prejoin; rewrite -f_surj.
- by move=> x y xS2 yS2; move/(congr1 f); rewrite !cancel_r.
- by rewrite -f_surj -imfset_comp /=.
Qed.

Lemma isof_trans (S1 S2 S3 : {finLattice T}) :
  isof S1 S2 -> isof S2 S3 -> isof S1 S3.
Proof.
case/isofP => f [[f_morphI f_morphU] f_inj f_surj].
case/isofP => g [[g_morphI g_morphU] g_inj g_surj].
exists (g \o f); apply/misofP; split; first split.
- move=> x y xS1 yS1 /=.
  rewrite f_morphI //= f_surj g_morphI ?inE -?f_surj ?in_imfset //.
  by congr premeet; rewrite [RHS]imfset_comp.
- move=> x y xS1 yS1 /=.
  rewrite f_morphU //= f_surj g_morphU ?inE -?f_surj ?in_imfset //.
  by congr prejoin; rewrite [RHS]imfset_comp.
- move=> x y xS1 yS1 /= /g_inj; rewrite -f_surj.
  move/(_ (in_imfset _ f xS1) (in_imfset _ f yS1)).
  by move/f_inj => /(_ xS1 yS1).
- by rewrite imfset_comp /= -g_surj f_surj.
Qed.

Lemma meet_isof (S1 S2 : {finLattice T}) (f : T -> T) :
  {in S1&, injective f} -> f @` (S1 : {fset _}) = S2 ->
  {in S1&, {morph f : x y / premeet S1 x y >-> premeet S2 x y}} ->
  misof S1 S2 f.
Proof.
move=> f_inj f_surj f_meetmorph; apply/misofP; split => //.
split; rewrite f_surj //.
move=> x y xS1 yS1.
rewrite !fjoin_meets; try by (rewrite ?inE -?f_surj ?in_imfset).
rewrite big_seq_cond [RHS]big_seq_cond (big_morph_sub f_meetmorph);
  [ |by move=> ? /and3P []|exact:mem_fmeet|exact:mem_ftop].
rewrite -{2}f_surj.
have f_surj_perm : perm_eq (f @` (S1 : {fset _})) [seq f x | x <- S1] by
  exact: enum_imfset.
rewrite (big_perm_sub (fmeetC (S := S2)) (fmeetA (S := S2))
  (mem_fmeet (S := S2)) _ (mem_ftop S2) _ f_surj_perm); last first.
  by move=> ? /and3P [].
have <-: \ftop_S2 = f \ftop_S1.
- apply: ftop_id; rewrite ?inE -?f_surj ?in_imfset ?mem_ftop //.
  move=> z; rewrite inE -f_surj => /imfsetP [z' /= z'S1 ->].
  apply/(fmeet_idPl (S := S2));
    rewrite ?inE -?f_surj ?in_imfset ?mem_ftop //.
  by rewrite f_surj -f_meetmorph ?mem_ftop ?fmeetf1.
rewrite big_map [RHS]big_seq_cond; apply:congr_big=> // i; apply/idP/idP.
- case/and3P=> iS1 xi yi; rewrite -f_surj in_imfset ?iS1 //=.
  rewrite -!(eq_fmeetl (S:=S2)) -?f_meetmorph ?inE -?f_surj ?in_imfset //.
  move: (eq_fmeetl (S:=S1) xS1 iS1) (eq_fmeetl (S:=S1) yS1 iS1).
  by rewrite xi yi=> /eqP -> /eqP ->; rewrite !eq_refl.
- case/and4P=> iS1 _; rewrite iS1 /=.
  rewrite -2?(eq_fmeetl (S:=S2)) -?f_meetmorph ?inE -?f_surj ?in_imfset //.
  move/eqP/f_inj=> /(_ (mem_fmeet xS1 iS1) xS1) <-. 
  move/eqP/f_inj=> /(_ (mem_fmeet yS1 iS1) yS1) <-.
  by rewrite !leIfr. 
Qed.




(*Lemma comp_fmorphism L (S1 S2 S3 : {finLattice T})
      (f : {L : fmorphism S1 >-> S2}) (g : {L : fmorphism S2 >-> S3}) :
  fmorphism L S1 S2 f -> fmorphism L S2 S3 g -> fmorphism L S1 S3 (g \o f).
Proof.
move=> fm gm; split.
- by move=> x x_in; rewrite ?mem_fmorph.
- by move => x y x_in y_in; rewrite /= !fmorphI ?mem_fmorph.
- by move => x y x_in y_in; rewrite /= !fmorphU ?mem_fmorph.*)
(*- by rewrite /= !fmorph0.
- by rewrite /= !fmorph1.*)


(*Canonical fcomp L (S1 S2 S3 : {finLattice T})
  (f : {L : fmorphism S1 >-> S2}) (g : {L : fmorphism S2 >-> S3}) :=
  FMorphism (comp_fmorphism (fmorphismP f) (fmorphismP g)).*)

(*Lemma fmorphism_id L (S : {finLattice T}) :
  fmorphism L S S id.
Proof. by split. Qed.

Canonical fmorph_id L (S : {finLattice T}) := FMorphism (fmorphism_id S).*)

(*Section Test.
Definition fmorph_of L (S1 S2 : {finLattice T})
  (f : {L : fmorphism S1 >-> S2}) & (phantom (T -> T) f) :
  {L : fmorphism S1 >-> S2} := f.
Notation "f %:fmorph" := (fmorph_of (Phantom (T -> T) f)) (at level 0).

Variable (L : {preLattice T}) (S1 S2 S3 : {finLattice T}).
Variable (f : {L : fmorphism S1 >-> S2}) (g : {L : fmorphism S2 >-> S3}).

(*Check ((g \o f)%:fmorph : { L : fmorphism S1 >-> S3}).*)
(*Check (id %:fmorph : {fmorphism S1 >-> S1}).*)
End Test.*)

(*Lemma fcomp_bij L (S1 S2 S3 : {finLattice T})
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
Context {T: choiceType} {L : {preLattice T}} (S1 S2 : {finLattice T}).
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
End IsoFmorphTheory.


(* -------------------------------------------------------------------- *)
Module Rank.
Section ClassDef.
Context  {disp : Order.disp_t} {T : prelatticeType disp} (S : {finLattice T}).

Definition axiom (rank : T -> nat) :=
  [/\ rank \fbot_S = 0%N
    , {in S&, {homo rank : x y / x < y >-> (x < y)%N}}
    & {in S&, forall x z, x <= z -> ((rank x).+1 < rank z)%N ->
        exists2 y, y \in S & x < y < z}].

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
Import Rank.Exports.

(* -------------------------------------------------------------------- *)
Section RankTheory.
Context {disp : Order.disp_t} {T : prelatticeType disp} (S : {finLattice T}).

Implicit Types (rk : {rank S}).

Lemma rank0 rk : rk \fbot_S = 0%N.
Proof. by case: rk => ? []. Qed.

Lemma homo_rank_lt rk : {in S&, {homo rk : x y / x < y >-> (x < y)%N}}.
Proof. by case: rk => ? []. Qed.

Lemma homo_rank_le rk : {in S&, {homo rk : x y / x <= y >-> (x <= y)%N}}.
Proof. by apply/(ltW_homo_in_as (f := rk))/homo_rank_lt. Qed.

Lemma graded_rank rk :
  {in S&, forall x z, x <= z -> ((rk x).+1 < rk z)%N ->
    exists2 y, y \in S & x < y < z}.
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

Lemma rank_gt0 rk x : x \in S -> (0 < rk x)%N = (\fbot_S < x).
Proof. move=> xS; rewrite lt0n lt0f //; congr (~~ _); exact: rank_eq0. Qed.

Lemma rank_le1 rk x : x \in S -> (rk x <= rk \ftop_S)%N.
Proof. by move=> xS; apply/homo_rank_le/lef1 => //; apply/(mem_ftop S). Qed.

Lemma rank_gt1 rk x : x \in S -> (rk x < rk \ftop_S)%N = (x < \ftop_S).
Proof.
by move=> xS; rewrite ltn_neqAle rank_le1 // andbT ltf1 // rank_eq1.
Qed.

Lemma rankI rk (x y : T) : x \in S -> y \in S ->
  (rk (premeet S x  y) <= minn (rk x) (rk y))%N.
Proof.
move=> xS yS; rewrite leq_min !homo_rank_le ?(leIfl, leIfr) //;
  by apply: mem_fmeet.
Qed.
End RankTheory.

(* -------------------------------------------------------------------- *)
Section RankInd.
Context {disp : Order.disp_t} {T : prelatticeType disp} (S : {finLattice T}).
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
Context {disp : Order.disp_t} {T : prelatticeType disp}.
Context (S : {finLattice T}) (rk : {rank S}).

Lemma graded_rankS (x : T) : x \in S ->
  (0 < rk x)%N -> exists y : T, [/\ y \in S, y < x & (rk y).+1 = rk x].
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

Context {disp : Order.disp_t} {T : prelatticeType disp} (S1 S2 : {finLattice T}).
Context (f : {fmorphism S1}) (rk1 : {rank S1}) (rk2 : {rank S2}).

Lemma rank_morph x :
  x \in S1 -> misof S1 S2 f ->  (rk1 x <= rk2 (f x))%N.
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
Context {disp : Order.disp_t} {T : prelatticeType disp} (S : {finLattice T}).

Definition atomistic_r (a : S) :=
  [exists A : {fset S},
       [forall x in A, atom S (val x)]
    && (a == (\join_(x in A) x))].

Definition atomistic (a : T) :=
  if @idP (a \in S) is  ReflectT h then atomistic_r [` h] else false.

Definition coatomistic_r (a : S) :=
  [exists A : {fset S},
       [forall x in A, coatom S (val x)]
    && (a == (\meet_(x in A) x))].

Definition coatomistic (a : T) :=
  if @idP (a \in S) is  ReflectT h then coatomistic_r [` h] else false.


End Atomistic.

Export PreLattice.Exports.
Export FinLatticeStructure.Exports.
Export FinTBLatticeStructure.Exports.
Export Interval.Exports.
Export Morphism.Exports.
Export Rank.Exports.
