(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import xbigop extra_misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope fset_scope.
Local Open Scope ring_scope.

(*
Record MyPair (T1 T2 : Type) := { fst : T1; snd : T2; }.

Definition dP {T1 T2 : Type} (xy : MyPair T1 T2) : MyPair T2 T1 :=
  {| fst := xy.(snd); snd :=  xy.(fst); |}.

Parameter S : forall T1 T2, MyPair T1 T2 -> Type.

Parameter dS : forall (T1 T2 : Type) (L : MyPair T1 T2), S L -> S (dP L).

Parameter dSK : forall (T1 T2 : Type) (L : MyPair T1 T2) (x : S L), dS (dS x) = x.

Parameter o : forall (T1 T2 : Type) (L : MyPair T1 T2), S L -> nat.

Parameter H : forall (T1 T2 : Type) (L : MyPair T1 T2) (x : S L), o x = o (dS x).

Parameter (T1 T2 : Type) (L : MyPair T1 T2).

Lemma dpK (T1 T2 : Type) (L : MyPair T1 T2) : dP (dP L) = L.
Proof. by []. Qed.

Parameter (y : S L).

Goal 0%N = o (dS (dS y)).
Proof.
rewrite {1 2}/dP /=.
rewrite -H.
Admitted.
*)

(* ==================================================================== *)

Module POrder.
Section ClassDef.

Context {T: eqType}.

Set Primitive Projections.

Record class (le lt: rel T) := Class {
  lexx : reflexive le;
  le_anti : forall x y, le x y -> le y x -> x = y;
  le_trans : transitive le;
  lt_def : forall x y, (lt x y) = (x != y) && (le x y);
  dlt_def : forall x y, (lt y x) = (x != y) && (le y x)
}.

(*TODO : Confirm that the phantom is required*)
Structure pack (phr : phant T) := Pack {
  pack_le; pack_lt;
  pack_class : class pack_le pack_lt;
  }.

Unset Primitive Projections.

Variable (phr : phant T) (r : pack phr).

Definition class_of := let: Pack _ _ c as r0 := r
  return (class (pack_le r0) (pack_lt r0)) in c.

Definition pack_of_le (r : rel T) :=
  fun (ro : pack phr) & phant_id (pack_le ro) r =>
  ro.

Definition pack_of_lt (r : rel T) :=
  fun (ro : pack phr) & phant_id (pack_lt ro) r =>
  ro.

End ClassDef.

(* -------------------------------------------------------------------- *)
Module Exports.
Coercion pack_class : pack >-> class.
Notation lto r := (pack_lt r).
Notation leo r := (pack_le r).
Notation class_of := class_of.
Notation "{ 'porder' T }" := (pack (Phant T))
  (at level 0, format "{ 'porder'  T }").
Notation "<=: r" := (leo r) (at level 2, r at level 1, format "<=: r").
Notation "<: r" := (lto r) (at level 2, r at level 1, format "<: r").
Notation "x <=_ r y" := (<=:r x y) (at level 65, r at level 2, format "x  <=_ r  y").
Notation "x >=_ r y" := (y <=_r x) (at level 65, r at level 2, only parsing).
Notation "x <_ r y" := (<:r x y) (at level 65, r at level 2, format "x  <_ r  y").
Notation "x >_ r y" := (y <_r x) (at level 65, r at level 2, only parsing).
Notation "x <=_ r0 y <=_ r1 z" := ((x <=_r0 y) && (y <=_r1 z))
  (at level 70, r0 at level 2, r1 at level 2, format "x  <=_ r0  y  <=_ r1  z").
Notation "x <_ r0 y <_ r1 z" := ((x <_r0 y) && (y <_r1 z))
  (at level 70, r0 at level 2, r1 at level 2, format "x  <_ r0  y  <_ r1  z").
Notation "x <=_ r0 y <_ r1 z" := ((x <=_r0 y) && (y <_r1 z))
  (at level 70, r0 at level 2, r1 at level 2, format "x  <=_ r0  y  <_ r1  z").
Notation "x <_ r0 y <=_ r1 z" := ((x <_r0 y) && (y <=_r1 z))
  (at level 70, r0 at level 2, r1 at level 2, format "x  <_ r0  y  <=_ r1  z").
Notation "x >=<_ r y" := ((x <=_r y) || (y <=_r x))
  (at level 70, r at level 2, no associativity, format "x  >=<_ r  y").
Notation "x ><_ r y" := (~~ ( x >=<_r y ))
  (at level 70, r at level 2, no associativity, format "x  ><_ r  y").
Notation ">=<_ r y" := [pred x | x >=<_r y]
  (at level 80, r at level 2, format ">=<_ r  y").
Notation "><_ r y" := [pred x | x ><_r y]
  (at level 80, r at level 2, format "><_ r  y").
Notation "[ 'leo:' r ]" := (@pack_of_le _ (Phant _) r _ id)
  (at level 0, format "[ 'leo:'  r ]").
Notation "[ 'lto:' r ]" := (@pack_of_lt _ (Phant _) r _ id)
  (at level 0, format "[ 'lto:'  r ]").
(*TODO : Notations supplémentaires*)
End Exports.
End POrder.

Include POrder.Exports.

(* ================================================================ *)

Section DualOrder.

Context (T: eqType).

Definition dual_rel (r: rel T) := fun y x => r x y.

Definition dual_refl (r : rel T) (hr : reflexive r)
  : reflexive (dual_rel r) := hr.

Definition dual_anti (r : rel T) (ha : forall x y, r x y -> r y x -> x = y):
   forall x y, (dual_rel r) x y -> (dual_rel r) y x -> x = y :=
   fun x y yx xy=> ha x y xy yx.

Definition dual_trans (r : rel T) (ht: transitive r) :
  transitive (dual_rel r) := fun y x z drxy dryz => ht _ _ _ dryz drxy.

Variable (r : {porder T}).


Definition DualPOrderClass := @POrder.Class T (dual_rel <=:r)
  (dual_rel <:r) (dual_refl (POrder.lexx r)) (dual_anti (POrder.le_anti r))
  (dual_trans (POrder.le_trans r)) (POrder.dlt_def r) (POrder.lt_def r). 
Canonical DualPOrderPack := POrder.Pack (Phant T) DualPOrderClass.

End DualOrder.

Notation "r ^~" := (DualPOrderPack r) (at level 8, format "r ^~").

Section DualOrderTest.
Context {T: eqType}.
Variable (r : {porder T}).

Lemma le_dual_inv x y: x <=_((r^~)^~) y = x <=_r y.
Proof. by []. Qed.

Lemma lt_dual_inv x y: x <_((r^~)^~) y = x <_r y.
Proof. by []. Qed.

Goal r = (r^~)^~.
Proof. by []. Qed.

Goal [leo: (dual_rel <=:r)] = r^~.
Proof. by []. Qed.

Goal [lto: (dual_rel <:r)] = r^~.
Proof. by []. Qed.

Goal forall x y, x <_r y -> y <_(r^~) x.
Proof. by []. Qed.

Goal forall x y, x <=_r y = y <=_(r^~) x.
Proof. by []. Qed.


End DualOrderTest.

(* ==================================================================== *)
Section OrderDef.

Context {T: eqType}.
Implicit Type (r : {porder T}).

Definition min r x y := if x <_r y then x else y.
Definition max r x y := if x <_r y then y else x.

Variant compare r (x y : T) :
  T -> T -> T -> T ->
  bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | CompareLt of x <_r y : compare r x y
    x x y y false false false true false true
  | CompareGt of y <_r x : compare r x y
    y y x x false false true false true false
  | CompareEq of x = y : compare r x y
    x x x x true true true true false false.

Variant incompare r (x y : T) :
  T -> T -> T -> T ->
  bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool ->
  Set :=
  | InCompareLt of x <_r y : incompare r x y
    x x y y false false false true false true true true
  | InCompareGt of y <_r x : incompare r x y
    y y x x false false true false true false true true
  | InCompare of x ><_r y  : incompare r x y
    x y y x false false false false false false false false
  | InCompareEq of x = y : incompare r x y
    x x x x true true true true false false true true.

Variant le_xor_gt r (x y : T) :
  T -> T -> T -> T -> bool -> bool -> Set :=
  | LeNotGt of x <=_r y : le_xor_gt r x y x x y y true false
  | GtNotLe of y <_r x  : le_xor_gt r x y y y x x false true.

Variant lt_xor_ge r (x y : T) :
  T -> T -> T -> T -> bool -> bool -> Set :=
  | LtNotGe of x <_r y  : lt_xor_ge r x y x x y y false true
  | GeNotLt of y <=_r x : lt_xor_ge r x y y y x x true false.


Definition leif r (x y : T) C : Prop := ((x <=_r y) * ((x == y) = C))%type.
Definition lteif r (x y : T) C := if C then x <=_r y else x <_r y.
End OrderDef.

Notation "x <=_ r y ?= 'iff' C" := (leif r x y C)
  (at level 70, C at level 1, r at level 2,
  format "x '[hv'  <=_ r '/'  y  ?=  'iff'  C ']'" ).

Notation "x <_ r y ?<= 'if' C" := (lteif r x y C)
  (at level 71, C at level 1, r at level 1, y at next level,
  format "x '[hv'  <_ r '/'  y  ?<=  'if'  C ']'").

Section OrderTheory.

Variables ( T: eqType ) ( r : {porder T} ).

Local Notation "x <= y" := (x <=_r y).
Local Notation "x < y" := (x <_r y).
Local Notation "x >= y" := (x >=_r y) (only parsing).
Local Notation "x > y" := (x >_r y) (only parsing).
Local Notation "x <= y <= z" := ((x <= y) && (y <= z)).
Local Notation "x < y < z"   := ((x < y) && (y < z)).
Local Notation "x < y <= z"  := ((x < y) && (y <= z)).
Local Notation "x <= y < z"  := ((x <= y) && (y < z)).
Local Notation "x >=< y" := (x >=<_r y).
Local Notation "x >< y" := (x ><_r y).
Local Notation compare := (compare r).
Local Notation incompare := (incompare r).
Local Notation min := (min r).
Local Notation max := (max r).
Local Notation le_xor_gt := (le_xor_gt r).
Local Notation lt_xor_ge := (lt_xor_ge r).
Local Notation "x <= y ?= 'iff' C" := (leif r x y C).
(*Local Notation "x < y ?<= 'if' C" := (x <_r y ?<= if C).*)
Local Notation ">=< y" := (>=<_r y).


Lemma lexx : reflexive (<=:r).
Proof. by case: r => ? ? []. Qed.
Hint Resolve lexx : core.

Lemma le_anti : antisymmetric (<=:r).
Proof. case: r => le lt [] /= _ ha _ _ _ x y /andP []; exact: ha. Qed.

Lemma le_trans : transitive (<=:r).
Proof. by case: r => ? ? []. Qed.

Lemma lt_def: forall (x y : T), (x < y) = (x != y) && (x <= y).
Proof. by case: r => ? ? []. Qed.

Lemma ltxx x : x < x = false.
Proof. by rewrite lt_def eq_refl lexx. Qed.

Lemma lt_neqAle x y: (x < y) = (y != x) && (x <= y).
Proof.
rewrite eq_sym; exact: lt_def.
Qed.

Lemma le_eqVlt x y: (x <= y) = (x == y) || (x < y).
Proof.
by rewrite lt_def; case: eqP => //= ->; rewrite lexx.
Qed.

Lemma lt_eqF x y: x < y -> x == y = false.
Proof.
by rewrite lt_def => /andP [/negbTE->].
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
rewrite !lt_def => /andP [nexy lexy leyz].
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
by rewrite lt_def lexy andbT; apply: contraNneq Nleyx => ->.
Qed.

Lemma lt_le_asym x y : x < y <= x = false.
Proof.
by rewrite lt_def -andbA -eq_le eq_sym andNb.
Qed.

Lemma le_lt_asym x y : x <= y < x = false.
Proof.
by rewrite andbC lt_le_asym.
Qed.

Definition lte_anti := (=^~ eq_le, lt_asym, lt_le_asym, le_lt_asym).

Lemma lt_sorted_uniq_le s : sorted <:r s = uniq s && sorted <=:r s.
Proof.
elim: s => // a l Hind.
apply/(sameP idP)/(iffP idP).
- case/andP => /= /andP [/memPnC anl uniql].
  rewrite !path_sortedE; [|exact: lt_trans| exact: le_trans].
  case/andP => /allP lea sortedle; rewrite Hind uniql sortedle !andbT.
  by apply/allP => x xl; rewrite lt_def lea ?anl.
- rewrite /= !path_sortedE; [|exact: le_trans| exact: lt_trans].
  rewrite Hind; case/and3P => /allP altx uniql sortedle.
  rewrite uniql sortedle !andbT; apply/andP; split.
  + by apply/memPn => x xl; rewrite gt_eqF ?altx.
  + apply/allP => x xl; exact/ltW/altx.
Qed. 

Lemma le_sorted_eq s1 s2 :
  sorted <=:r s1 -> sorted <=:r s2 -> perm_eq s1 s2 -> s1 = s2.
Proof. apply/eq_sorted; [exact: le_trans| exact: le_anti]. Qed.


Lemma lt_sorted_eq s1 s2 :
  sorted <:r s1 -> sorted <:r s2 -> s1 =i s2 -> s1 = s2.
Proof.
rewrite !lt_sorted_uniq_le.
case/andP=> uniqs1 sorteds1 /andP [uniqs2 sorteds2].
move/uniq_perm; move/(_ uniqs1 uniqs2).
exact: le_sorted_eq.
Qed.

Lemma sort_le_id s : sorted <=:r s -> sort <=:r s = s.
Proof. exact/sorted_sort/le_trans. Qed.

Section Comparable.

Lemma comparable_leNgt x y : x >=< y -> (x <= y) = ~~ (y < x).
Proof.
move=> c_xy; apply/idP/idP => [/le_gtF/negP/negP//|]; rewrite lt_neqAle.
move: c_xy => /orP [] -> //; rewrite andbT negbK => /eqP ->; exact: lexx.
Qed.

Lemma comparable_ltNge x y : x >=< y -> (x < y) = ~~ (y <= x).
Proof.
move=> c_xy; apply/idP/idP => [/lt_geF/negP/negP//|].
by rewrite lt_neqAle eq_le; move: c_xy => /orP [] -> //; rewrite !andbT.
Qed.

Lemma comparable_ltgtP x y : x >=< y ->
  compare x y (min y x) (min x y) (max y x) (max x y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof.
rewrite /min /max !le_eqVlt [y == x]eq_sym.
have := (eqVneq x y, (boolP (x < y), boolP (y < x))).
move=> [[->//|neq_xy /=] [[] xy [] //=]] ; do ?by rewrite ?ltxx; constructor.
  by rewrite ltxx in xy.
by rewrite le_gtF // ltW.
Qed.

Lemma comparable_leP x y : x >=< y ->
  le_xor_gt x y (min y x) (min x y) (max y x) (max x y) (x <= y) (y < x).
Proof.
by move=> /comparable_ltgtP [?|?|->]; constructor; rewrite ?lexx // ltW.
Qed.

Lemma comparable_ltP x y : x >=< y ->
  lt_xor_ge x y (min y x) (min x y) (max y x) (max x y) (y <= x) (x < y).
Proof.
by move=> /comparable_ltgtP [?|?|->]; constructor; rewrite ?lexx // ltW.
Qed.

Lemma comparable_sym x y : (y >=< x) = (x >=< y).
Proof. by rewrite /comparable orbC. Qed.

Lemma comparablexx x : x >=< x.
Proof. by rewrite /comparable lexx. Qed.

Lemma incomparable_eqF x y : (x >< y) -> (x == y) = false.
Proof. by apply: contraNF => /eqP ->; rewrite comparablexx. Qed.

Lemma incomparable_leF x y : (x >< y) -> (x <= y) = false.
Proof. by apply: contraNF; rewrite /comparable => ->. Qed.

Lemma incomparable_ltF x y : (x >< y) -> (x < y) = false.
Proof. by rewrite lt_neqAle => /incomparable_leF ->; rewrite andbF. Qed.

Lemma comparableP x y : incompare x y
  (min y x) (min x y) (max y x) (max x y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y)
  (y >=< x) (x >=< y).
Proof.
rewrite ![y >=< _]comparable_sym; have [c_xy|i_xy] := boolP (x >=< y).
  by case: (comparable_ltgtP c_xy) => ?; constructor.
have i_yx : y >< x by rewrite comparable_sym.
rewrite (incomparable_leF i_xy) (incomparable_leF i_yx). 
rewrite !incomparable_eqF // /min /max !incomparable_ltF //.
by constructor.
Qed.

Lemma le_comparable (x y : T) : x <= y -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma lt_comparable (x y : T) : x < y -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma ge_comparable (x y : T) : y <= x -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma gt_comparable (x y : T) : y < x -> x >=< y.
Proof. by case: comparableP. Qed.

End Comparable.

Section Leif.

Lemma leifP x y C : reflect (x <= y ?= iff C) (if C then (x == y) else (x < y)).
Proof.
rewrite /leif le_eqVlt; apply: (iffP idP)=> [|[]].
  by case: C => [/eqP->|lxy]; rewrite ?eqxx // lxy lt_eqF.
by move=> /orP[/eqP->|lxy] <-; rewrite ?eqxx // lt_eqF.
Qed.

Lemma leif_refl x C : reflect (x <= x ?= iff C) C.
Proof. by apply: (iffP idP) => [-> | <-] //; split; rewrite ?eqxx ?lexx. Qed.

Lemma leif_trans x1 x2 x3 C12 C23 :
  x1 <= x2 ?= iff C12 -> x2 <= x3 ?= iff C23 -> x1 <= x3 ?= iff C12 && C23.
Proof.
move/leifP => leif12 /leifP leif23; apply/leifP; move: leif12 leif23.
case: C12 => /=.
  by move/eqP => ->.
move=> lt12; case C23.
  by move/eqP => <-.
by move/(lt_trans lt12).
Qed.

Lemma leif_le x y : x <= y -> x <= y ?= iff (x >= y).
Proof. by move=> lexy; split=> //; rewrite eq_le lexy. Qed.

Lemma leif_eq x y : x <= y -> x <= y ?= iff (x == y).
Proof. by []. Qed.

Lemma ge_leif x y C : x <= y ?= iff C -> (y <= x) = C.
Proof. by case=> le_xy; rewrite eq_le le_xy. Qed.

Lemma lt_leif x y C : x <= y ?= iff C -> (x < y) = ~~ C.
Proof. by move=> le_xy; rewrite lt_def !le_xy andbT. Qed.

Lemma ltNleif x y C : x <= y ?= iff ~~ C -> (x < y) = C.
Proof. by move=> /lt_leif; rewrite negbK. Qed.

Lemma eq_leif x y C : x <= y ?= iff C -> (x == y) = C.
Proof. by move=> /leifP; case: C comparableP => [] []. Qed.

Lemma eqTleif x y C : x <= y ?= iff C -> C -> x = y.
Proof. by move=> /eq_leif<-/eqP. Qed.

End Leif.

Section Lteif.

Lemma lteif_trans x y z C1 C2 :
  lteif r x y C1 -> lteif r y z C2 -> lteif r x z (C1 && C2).
Proof.
case: C1 C2 => [][];
  [exact: le_trans | exact: le_lt_trans | exact: lt_le_trans | exact: lt_trans].
Qed.

Lemma lteif_anti C1 C2 x y :
  (lteif r x y C1) && (lteif r y x C2) = C1 && C2 && (x == y).
Proof. by case: C1 C2 => [][]; rewrite lte_anti. Qed.

Lemma lteifxx x C : (lteif r x x C) = C.
Proof. by case: C; rewrite /= ?lexx ?ltxx. Qed.

Lemma lteifNF x y C : lteif r y x (~~ C) -> (lteif r x y C) = false.
Proof. by case: C => [/lt_geF|/le_gtF]. Qed.

Lemma lteifS x y C : x < y -> lteif r x y C.
Proof. by case: C => //= /ltW. Qed.

Lemma lteifT x y : lteif r x y true = (x <= y). Proof. by []. Qed.

Lemma lteifF x y : lteif r x y false = (x < y). Proof. by []. Qed.

Lemma lteif_orb x y : {morph (lteif r) x y : p q / p || q}.
Proof. by case=> [][] /=; case: comparableP. Qed.

Lemma lteif_andb x y : {morph (lteif r) x y : p q / p && q}.
Proof. by case=> [][] /=; case: comparableP. Qed.

Lemma lteif_imply C1 C2 x y : C1 ==> C2 -> lteif r x y C1 -> lteif r x y C2.
Proof. by case: C1 C2 => [][] //= _ /ltW. Qed.

Lemma lteifW C x y : lteif r x y C -> x <= y.
Proof. by case: C => // /ltW. Qed.

Lemma ltrW_lteif C x y : x < y -> lteif r x y C.
Proof. by case: C => // /ltW. Qed.

Lemma lteifN C x y : lteif r x y (~~ C) -> ~~ (lteif r y x C).
Proof. by case: C => /=; case: comparableP. Qed.

End Lteif.

Section MinMax.

Lemma minElt x y : min x y = if x < y then x else y. Proof. by []. Qed.
Lemma maxElt x y : max x y = if x < y then y else x. Proof. by []. Qed.

Lemma minEle x y : min x y = if x <= y then x else y.
Proof. by case: comparableP. Qed.

Lemma maxEle x y : max x y = if x <= y then y else x.
Proof. by case: comparableP. Qed.

Lemma comparable_minEgt x y : x >=< y -> min x y = if x > y then y else x.
Proof. by case: comparableP. Qed.
Lemma comparable_maxEgt x y : x >=< y -> max x y = if x > y then x else y.
Proof. by case: comparableP. Qed.
Lemma comparable_minEge x y : x >=< y -> min x y = if x >= y then y else x.
Proof. by case: comparableP. Qed.
Lemma comparable_maxEge x y : x >=< y -> max x y = if x >= y then x else y.
Proof. by case: comparableP. Qed.

Lemma min_l x y : x <= y -> min x y = x. Proof. by case: comparableP. Qed.
Lemma min_r x y : y <= x -> min x y = y. Proof. by case: comparableP. Qed.
Lemma max_l x y : y <= x -> max x y = x. Proof. by case: comparableP. Qed.
Lemma max_r x y : x <= y -> max x y = y. Proof. by case: comparableP. Qed.

Lemma minxx : idempotent (min : T -> T -> T).
Proof. by rewrite /min => x; rewrite ltxx. Qed.

Lemma maxxx : idempotent (max : T -> T -> T).
Proof. by rewrite /max => x; rewrite ltxx. Qed.

Lemma eq_minl x y : (min x y == x) = (x <= y).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP. Qed.

Lemma eq_maxr x y : (max x y == y) = (x <= y).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP. Qed.

Lemma min_idPl x y : reflect (min x y = x) (x <= y).
Proof. by apply: (iffP idP); rewrite (rwP eqP) eq_minl. Qed.

Lemma max_idPr x y : reflect (max x y = y) (x <= y).
Proof. by apply: (iffP idP); rewrite (rwP eqP) eq_maxr. Qed.

Lemma min_minKx x y : min (min x y) y = min x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP. Qed.

Lemma min_minxK x y : min x (min x y) = min x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP. Qed.

Lemma max_maxKx x y : max (max x y) y = max x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP. Qed.

Lemma max_maxxK x y : max x (max x y) = max x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP. Qed.

Lemma comparable_minl z : {in >=< z &, forall x y, min x y >=< z}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /min; case: ifP. Qed.

Lemma comparable_minr z : {in >=< z &, forall x y, z >=< min x y}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /min comparable_sym; case: ifP. Qed.

Lemma comparable_maxl z : {in >=< z &, forall x y, max x y >=< z}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /max; case: ifP. Qed.

Lemma comparable_maxr z : {in >=< z &, forall x y, z >=< max x y}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /max comparable_sym; case: ifP. Qed.

End MinMax.

(* TODO, missing theory from order.v

  Section Comparable2.
  Section Comparable3.
  Section ArgExtremum.
  Lemma mono_in_leif.
  Lemma mono_leif.
  Lemma nmono_in_leif.
  Lemma nmono_leif.
  Lemma comparable_bigl.
  Lemma comparable_bigr.
*)

End OrderTheory.

(* TODO, missing theory from order.v
  Section ContraTheory.
  Section POrderMonotonyTheory.
  Section BPOrderTheory.
  Section TPOrderTheory.
*)

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
(*Module TotalOrder.
Section ClassDef.

Context {T : eqType}.

Definition mixin_of (r : rel T) :=
  forall x y, r x y || r y x.

Record class (le lt dle: rel T) := Class {
  base : Order.class le lt dle;
  mixin : mixin_of le
}.

Structure pack (phr : phant T) := Pack {
  pack_le; pack_lt; pack_dle;
  pack_class : class pack_le pack_lt pack_dle
}.

Variable (phr : phant T) (rT : pack phr).

Definition class_of := let: Pack _ _ _ c as rT' := rT
  return class (pack_le rT') (pack_lt rT') (pack_dle rT') in c.

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
Proof. by case: r => ? ? ? []. Qed.

Lemma totalP : axiom (leo r).
Proof. by case: r => ? ? ? [[]]. Qed.
End TotalOrderTheory.*)

(* ==================================================================== *)
Module Meet.
(*TODO : Adapter la structure MeetSemilattice de order.v*)
Section ClassDef.
Context {T : eqType}.

Set Primitive Projections.
Record class (r : {porder T}) := Class {
  meet : T -> T -> T;
  meetC: commutative meet;
  meetA : associative meet;
  meetxx : idempotent meet;
  leEmeet : forall x y, (x <=_r y) = (meet x y == x);
}.


Structure pack (phr : phant T) := Pack {
  pack_order;
  pack_class : class pack_order
}.
Unset Primitive Projections.

Local Coercion pack_order: pack >-> POrder.pack.

Variables (phr : phant T) (mr : pack phr).

Definition porder_of :=
  POrder.Pack phr (POrder.pack_class mr).

Definition meet_of (r : {porder T}) :=
  fun (pr : pack phr) & phant_id (pack_order pr) r =>
  meet (pack_class pr).

Definition clone (r : {porder T}) :=
  fun (pr : pack phr) & phant_id (pack_order pr) r =>
  pr.

End ClassDef.

(* -------------------------------------------------------------------- *)
Module Exports.
Coercion pack_order : pack >-> POrder.pack.
Coercion pack_class : pack >-> class.
Canonical porder_of.
Notation meet r := (@meet_of _ (Phant _) r _ id).
Notation "{ 'meetSemiLattice' T }" := (pack (Phant T))
  (at level 0, format "{ 'meetSemiLattice'  T }").
Notation "[ 'meetSemiLattice' 'of' r ]" := (@clone _ (Phant _) r _ id)
  (at level 0, format "[ 'meetSemiLattice'  'of'  r ]"). 
End Exports.
End Meet.

Include Meet.Exports.

(* ===================================================================== *)

Module Join.

Section ClassDef.
Context {T : eqType}.

Set Primitive Projections.
Record class (r : {porder T}) := Class {
  join : T -> T -> T;
  joinC : commutative join;
  joinA : associative join;
  joinxx : idempotent join;
  leEjoin : forall x y, (x <=_r y) = (join y x == y);
}.

Structure pack (phr : phant T) := Pack {
  pack_order;
  pack_class : class pack_order
}.
Unset Primitive Projections.

Local Coercion pack_order: pack >-> POrder.pack.

Variables (phr : phant T) (mr : pack phr).

Definition order_of :=
  POrder.Pack phr (POrder.pack_class mr).

Definition join_of (r : {porder T}) :=
  fun (pr : pack phr) & phant_id (pack_order pr) r =>
  join (pack_class pr).

Definition clone (r : {porder T}) :=
  fun (pr : pack phr) & phant_id (pack_order pr) r =>
  pr.

End ClassDef.

(* ------------------------------------------------------------------- *)

Module Exports.

Notation join r := (@join_of _ (Phant _) r _ id).
Coercion pack_order : pack >-> POrder.pack.
Coercion pack_class : pack >-> class.
Canonical order_of.
Notation "{ 'joinSemiLattice' T }" := (pack (Phant T))
  (at level 0, format "{ 'joinSemiLattice'  T }").
Notation "[ 'joinSemiLattice' 'of' r ]" := (@clone _ (Phant _) r _ id)
  (at level 0, format "[ 'joinSemiLattice'  'of'  r ]"). 


End Exports.

End Join.
Include Join.Exports.

(* ==================================================================== *)

Section DualMeetJoin.

Context {T: eqType}.
Variable (m : {meetSemiLattice T}) (j : {joinSemiLattice T}).

Definition DualMeetClass := @Join.Class _ (m^~)
  (meet m) (Meet.meetC m) (Meet.meetA m) (Meet.meetxx m)
  (fun x y => (Meet.leEmeet m y x)).

Canonical DualMeetPack := Join.Pack (Phant _) DualMeetClass.

Definition DualJoinClass := @Meet.Class _ (j^~)
  (join j) (Join.joinC j) (Join.joinA j) (Join.joinxx j)
  (fun x y => (Join.leEjoin j y x)).

Canonical DualJoinPack := Meet.Pack (Phant _) DualJoinClass.

End DualMeetJoin.

(*Section DualMeetJoinTest.

Context {T: eqType}. (*(M : {meetSemiLattice T}) (J : {joinSemiLattice T}).*)
Axiom dualK: forall r : {porder T}, r^~^~ = r.
Context (M : {meetSemiLattice T}) (J : {joinSemiLattice T}).
Goal M^~^~= M.
by rewrite dualK.
Qed.


Check @Meet.clone _ (Phant _) M _ id.
Check @Join.clone _ (Phant _) M^~ _ id.
Check @Meet.clone _ (Phant _) (M^~)^~ _ id.
Set Printing All.
Goal M = @Meet.clone _ (Phant _) (M^~)^~ _ id.
reflexivity.
Qed.
(*Goal M = (M^~)^~ :> { meetSemiLattice T}.*)
(*Check (M^~)^~ : { meetSemiLattice T}.*)
Set Printing All.
Fail Check erefl J : ((J^~j)^~m) = J.

End DualMeetJoinTest.*)




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


(* ===================================================================== *)

Section JoinTheory.

Context {T: eqType} (r: {joinSemiLattice T}).

Local Notation "x `|` y" := (join r x y).
Local Notation "x <= y" := (x <=_r y).


Lemma joinC : commutative (join r).
Proof. by case: r => ? []. Qed.

Lemma joinA : associative (join r).
Proof. by case: r => ? []. Qed.

Lemma joinxx : idempotent (join r).
Proof. by case: r => ? []. Qed.

Lemma leEjoin x y : (x <= y) = (y `|` x == y).
Proof. by case: r => ? []. Qed.

Lemma joinAC : right_commutative (join r).
Proof. exact: (@meetAC _ [meetSemiLattice of r^~]). Qed.

Lemma joinCA : left_commutative (join r).
Proof. exact (@meetCA _ [meetSemiLattice of r^~]). Qed.

Lemma joinACA : interchange (join r) (join r).
Proof. exact: (@meetACA _ [meetSemiLattice of r^~]). Qed.

Lemma joinKI y x : x `|` (x `|` y) = x `|` y.
Proof. exact: (@meetKI _ [meetSemiLattice of r^~]). Qed.

Lemma joinIK y x : (x `|` y) `|` y = x `|` y.
Proof. exact: (@meetIK _ [meetSemiLattice of r^~]). Qed.

Lemma joinKIC y x : x `|` (y `|` x) = x `|` y.
Proof. exact: (@meetKIC _ [meetSemiLattice of r^~]). Qed.

Lemma joinIKC y x : y `|` x `|` y = x `|` y.
Proof. exact: (@meetIKC _ [meetSemiLattice of r^~]). Qed.

Lemma leUx x y z : (y `|` z <= x) = (y <= x) && (z <= x).
Proof. exact: (@lexI _ [meetSemiLattice of r^~]). Qed.

Lemma lexUl x y z : x <= y -> x <= y `|` z.
Proof. exact: (@leIxl _ [meetSemiLattice of r^~]). Qed.

Lemma lexUr x y z : x <= z -> x <= y `|` z.
Proof. exact: (@leIxr _ [meetSemiLattice of r^~]). Qed.

Lemma lexU2 x y z : (x <= y) || (x <= z) -> x <= y `|` z.
Proof. exact: (@leIx2 _ [meetSemiLattice of r^~]). Qed.

Lemma leUr x y : x <= y `|` x.
Proof. exact: (@leIr _ [meetSemiLattice of r^~]). Qed.

Lemma leUl x y : x <= x `|` y.
Proof. exact: (@leIl _ [meetSemiLattice of r^~]). Qed.

Lemma join_idPr {x y} : reflect (y `|` x = x) (y <= x).
Proof. exact: (@meet_idPr _ [meetSemiLattice of r^~]). Qed.


Lemma join_idPl {x y} : reflect (x `|` y = x) (y <= x).
Proof. exact: (@meet_idPl _ [meetSemiLattice of r^~]). Qed.

Lemma join_l x y : y <= x -> x `|` y = x.
Proof. exact/join_idPl. Qed.

Lemma join_r x y : x <= y -> x `|` y = y.
Proof. exact/join_idPr. Qed.

Lemma leUidl x y : (x `|` y <= x) = (y <= x).
Proof. exact: (@leIidl _ [meetSemiLattice of r^~]). Qed.

Lemma leUidr x y : (y `|` x <= x) = (y <= x).
Proof. exact: (@leIidr _ [meetSemiLattice of r^~]). Qed.

Lemma eq_joinl x y : (x `|` y == x) = (y <= x).
Proof. exact: (@eq_meetl _ [meetSemiLattice of r^~]). Qed.

Lemma eq_joinr x y : (x `|` y == y) = (x <= y).
Proof. exact: (@eq_meetr _ [meetSemiLattice of r^~]). Qed.

Lemma leU2 x y z t : x <= z -> y <= t -> x `|` y <= z `|` t.
Proof. exact: (@leI2 _ [meetSemiLattice of r^~]). Qed.

End JoinTheory.

(* ================================================================ *)

Module TMeet.
Section ClassDef.
Context {T: eqType}.

Set Primitive Projections.
Record class (r : {meetSemiLattice T}) := Class
  {
    top : T;
    lex1 : forall x, x <=_r top
  }.

Structure pack (phr : phant T) := Pack
  {
    pack_meet : {meetSemiLattice T};
    pack_class : class pack_meet
  }.

Unset Primitive Projections.
Local Coercion pack_meet : pack >-> Meet.pack.

Variables (phr : phant T) (tmr : pack phr).

Definition order_of := POrder.Pack phr (POrder.pack_class tmr).
Definition meet_of := Meet.Pack (Phant _) tmr.
Definition clone (r : {porder T}) :=
  fun (m : {meetSemiLattice T}) & phant_id (Meet.pack_order m) r =>
  fun (tm : pack phr) & phant_id (pack_meet tm) m =>
  tm.

End ClassDef.

(* ---------------------------------------------------------------- *)

Module Exports.
Coercion pack_meet : pack >-> Meet.pack.
Coercion pack_class : pack >-> class.
Canonical meet_of.
Canonical order_of.
Notation top := top.
Notation "{ 'tMeetSemiLattice' T }" := (pack (Phant T))
  (at level 0, format "{ 'tMeetSemiLattice'  T }").
Notation "[ 'tMeetSemiLattice' 'of' r ]" := (@clone _ (Phant _) r _ id _ id)
  (at level 0, format "[ 'tMeetSemiLattice'  'of'  r ]").

End Exports.
End TMeet.
Include TMeet.Exports.

(* ================================================================= *)

Module BJoin.
Section ClassDef.
Context {T: eqType}.

Set Primitive Projections.
Record class (r : {joinSemiLattice T}) := Class
  {
    bot : T;
    le0x : forall x, bot <=_r x
  }.

Structure pack (phr : phant T) := Pack
  {
    pack_join : {joinSemiLattice T};
    pack_class : class pack_join
  }.

Unset Primitive Projections.
Local Coercion pack_join : pack >-> Join.pack.

Variables (phr : phant T) (bjr : pack phr).

Definition join_of := Join.Pack (Phant _) bjr.
Definition order_of := POrder.Pack phr (POrder.pack_class bjr).

Definition clone (r : {porder T}) :=
  fun (j : {joinSemiLattice T}) & phant_id (Join.pack_order j) r =>
  fun (bj : pack phr) & phant_id (pack_join bj) j =>
  bj.

End ClassDef.

(* ---------------------------------------------------------------- *)

Module Exports.
Coercion pack_join : pack >-> Join.pack.
Coercion pack_class : pack >-> class.
Canonical join_of.
Canonical order_of.
Notation bot := bot.
Notation "{ 'bJoinSemiLattice' T }" := (pack (Phant T))
  (at level 0, format "{ 'bJoinSemiLattice'  T }").
Notation "[ 'bJoinSemiLattice' 'of' r ]" := (@clone _ (Phant _) r _ id _ id)
  (at level 0, format "[ 'bJoinSemiLattice'  'of'  r ]").


End Exports.
End BJoin.
Include BJoin.Exports.

(* =============================================================== *)

Section DualTMeetBJoin.

Context {T: eqType}.
Variables (tm : {tMeetSemiLattice T}) (bj : {bJoinSemiLattice T}).

Definition DualTMeetClass :=
  @BJoin.Class _ (DualMeetPack tm) (top tm) (TMeet.lex1 tm).

Canonical DualTMeetPack := BJoin.Pack (Phant _) DualTMeetClass.

Definition DualBJoinClass :=
  @TMeet.Class _ (DualJoinPack bj) (bot bj) (BJoin.le0x bj).

Canonical DualBJoinPack := TMeet.Pack (Phant _) DualBJoinClass.

End DualTMeetBJoin.

Section DualTBTest.
Context {T: eqType} (tm : {tMeetSemiLattice T}).
Check [bJoinSemiLattice of tm^~].

End DualTBTest.

Section TMeetTheory.

Context {T: eqType} (r: {tMeetSemiLattice T}).

Local Notation "x <= y" := (x <=_r y).
Local Notation top := (top r).

Lemma lex1 : forall x, x <= top.
Proof. by case: r => ? []. Qed.
  
Lemma meet1x : left_id top (meet r).
Proof. by move=> x; apply/eqP; rewrite meetC -leEmeet lex1. Qed.
  
Lemma meetx1 : right_id top (meet r).
Proof. by move=> x; apply/eqP; rewrite -leEmeet lex1. Qed.

End TMeetTheory.

Section BJoinTheory.

Context {T: eqType} (r : {bJoinSemiLattice T}).
Local Notation "x <= y" := (x <=_r y).
Local Notation bot := (bot r).

Lemma le0x : forall x, bot <= x.
Proof. exact :(@lex1 _ [tMeetSemiLattice of r^~]). Qed.

Lemma joinx0 : right_id bot (join r).
Proof. exact: (@meetx1 _ [tMeetSemiLattice of r^~]). Qed.

Lemma join0x : left_id bot (join r).
Proof. exact: (@meet1x _ [tMeetSemiLattice of r^~]). Qed.

End BJoinTheory.
  
(* ==================================================================== *)

(*TODO, missing theory and structures from order.v
  Section BMeetSemilatticeTheory.
  Section TJoinSemiLatticeTheory.
  (+ theories in TMeetSemilatticeTheory about the corresponding comonoid)
  (+ theories in BJoinSemilatticeTheory about the corresponding comonoid)
*)


(*Module Lattice.

Section ClassDef.

Context {T : eqType}.

Structure pack (phr : phant T) := Pack {
  pack_meet : {meetSemiLattice T};
  pack_join : {joinSemiLattice T};
  _ : (Meet.pack_order pack_meet = Join.pack_order pack_join)
}.

Variables (phr : phant T) (mjr : pack phr).

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

End LatticeTheory.

(* ==================================================================== *)

Section DualLattice.

Context (T: eqType) (r : {lattice T}).

Lemma dual_leEmeet: forall x y, (x <=_(r^~) y) = ((join r x y) == x).
Proof.
by move=> x y /=; rewrite leEdual leEjoin joinC.
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
by move=> y x /=; rewrite leEdual leEmeet.
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

Structure pack (phr : phant T) := Pack {
  pack_lattice;
  pack_class : class pack_lattice
}.

Local Coercion pack_lattice: pack >-> Lattice.pack.
Local Coercion pack_class: pack >-> class.

Variable (phr : phant T) (bl : pack phr).

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
Include TBLattice.Exports.*)



(* ==================================================================== *)

(*Section DualTBLattice.

Context {T: eqType} (L : {tblattice T}).

Lemma dual_lex1 x: (top L) <=_(L^~) x.
Proof.
rewrite /= leEdual; exact: lex1.
Qed.

Lemma dual_le0x x: x <=_(L^~) (bottom L).
Proof.
rewrite /= leEdual; exact: le0x.
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

End DualTBLattice.*)

(* ==================================================================== *)

(* TODO,  missing theory and structures about distibutive lattices
          missing theory and structures about total orders          
*)

Section BigOps.
Context {T : eqType} (m : { tMeetSemiLattice T}) (j: {bJoinSemiLattice T}).

Canonical join_monoid := Monoid.Law (joinA j) (join0x j) (joinx0 j).
Canonical join_comonoid := Monoid.ComLaw (joinC j).
Canonical meet_monoid := Monoid.Law (meetA m) (meet1x m) (meetx1 m).
Canonical meet_comonoid := Monoid.ComLaw (meetC m).

Lemma meet_max_seq {I : eqType} (r : seq I) (P : pred I) (F : I -> T) (x : I) :
  x \in r -> P x -> \big[meet m/top m]_(i <- r | P i) F i <=_m F x.
Proof.
move=> xr Px; rewrite (perm_big _ (perm_to_rem xr)) /=.
by rewrite big_cons /= Px; apply/leIl.
Qed.

Lemma meetsP_seq {I : eqType}  (r : seq I) (P : pred I) (F : I -> T) (x : T) :
  reflect
    (forall i, i \in r -> P i -> x <=_m F i)
    (x <=_m \big[meet m/top m]_(i <- r | P i) F i).
Proof.
have ->:
  x <=_m \big[meet m/top m]_(i <- r | P i) F i
    = \big[andb/true]_(i <- r | P i) (x <=_m F i).
- by elim/big_rec2: _ => [|i b y Pi <-]; rewrite 1?(lex1, lexI).
by rewrite big_all_cond; apply: (iffP allP) => h i ir; apply/implyP/h.
Qed.

Lemma join_min_seq {I : eqType} (r : seq I) (P : pred I) (F : I -> T) (x : I) :
  x \in r -> P x -> F x <=_j \big[join j/bot j]_(i <- r | P i) F i.
Proof.
move=> xr Px; rewrite (perm_big _ (perm_to_rem xr)) /=.
by rewrite big_cons /= Px; rewrite leUl.
Qed.

Lemma joinsP_seq {I : eqType}  (r : seq I) (P : pred I) (F : I -> T) (x : T) :
  reflect
    (forall i, i \in r -> P i -> F i <=_j x)
    (\big[join j/bot j]_(i <- r | P i) F i <=_j x).
Proof.
have ->:
  \big[join j/bot j]_(i <- r | P i) F i <=_j x
    = \big[andb/true]_(i <- r | P i) (F i <=_j x).
- by elim/big_rec2: _ => [|i b y Pi <-]; rewrite 1?(le0x, leUx).
by rewrite big_all_cond; apply: (iffP allP) => h i ir; apply/implyP/h.
Qed.
End BigOps.

(* ===================================================================== *)

Module PreLattice.
Section ClassDef.

Context {T : choiceType}.

Set Primitive Projections.
  
Record class (r : {porder T}) := Class
{
  lub : {fset T} -> T;
  glb : {fset T} -> T;
  lub_sup : forall S, forall x, x \in S -> x <=_r lub S;
  lub_min : forall S, forall z, (forall x, x \in S -> x <=_r z) -> lub S <=_r z;
  glb_inf : forall S, forall x, x \in S -> x <=_(r^~) glb S;
  glb_max : forall S, forall z, (forall x, x \in S -> x <=_(r^~) z) -> glb S <=_(r^~) z
}.

Structure pack (phr : phant T) := Pack
{
  pack_order : {porder T};
  pack_class : class pack_order
}.

Unset Primitive Projections.

Local Coercion pack_order : pack >-> POrder.pack.

Variable (phr : phant T) (m : pack phr).

Definition order_of := POrder.Pack phr (POrder.pack_class m).
Definition clone (r : {porder T}) :=
  fun (pl : pack phr) & phant_id (pack_order pl) r =>
  pl.

End ClassDef.


(* ---------------------------------------------------------------------- *)

Module Exports.

Canonical order_of.
Coercion pack_order : pack >-> POrder.pack.
Coercion pack_class : pack >-> class.
Notation "{ 'preLattice' T }" := (pack (Phant T))
  (at level 0, format "{ 'preLattice'  T }").
Notation "[ 'preLattice' 'of' r ]" := (@clone _ (Phant _) r _ id)
  (at level 0, format "[ 'preLattice'  'of'  r ]").
Notation lub := lub.
Notation glb := glb.

End Exports.

End PreLattice.
Include PreLattice.Exports.

Section DualPreLattice.

Context {T: choiceType}.
Variable (L : {preLattice T}).

Definition DualPreLatticeClass := PreLattice.Class
    (PreLattice.glb_inf L) (PreLattice.glb_max L)
    (PreLattice.lub_sup L) (PreLattice.lub_min L).

Canonical DualPreLatticePack :=
  PreLattice.Pack (Phant T) DualPreLatticeClass.

End DualPreLattice.

Section PreLatticeDualTest.

Context (T: choiceType) (L : {preLattice T}).
Check erefl L : [preLattice of L^~^~] = L.
End PreLatticeDualTest.

Section PreLatticeTheory.

Context {T: choiceType}.
Implicit Type L: {preLattice T}.

Lemma glb_inf_le L: forall S, forall x, x \in S -> x >=_L (glb L S).
Proof. move=> /= S x xS; exact:PreLattice.glb_inf. Qed.

Lemma glb_max_le L: forall S, forall z, (forall x, x \in S -> x >=_L z) ->
  glb L S >=_L z.
Proof.
move=> S z z_inf; apply: PreLattice.glb_max.
by move=> x /z_inf.
Qed.

Lemma lub1 (L: {preLattice T}) a: lub L [fset a] = a.
Proof.
apply:(@le_anti _ L); rewrite PreLattice.lub_sup ?inE ?eq_refl // andbT.
rewrite PreLattice.lub_min // => x; rewrite !inE => /eqP ->; exact: lexx.
Qed.

Lemma glb1 (L : {preLattice T}) a : glb L [fset a] = a.
Proof. exact: (lub1 [preLattice of L^~]). Qed.

Lemma glb_desc L A B: A `<=` B -> glb L B <=_L glb L A.
Proof. move/fsubsetP => AsubB; apply/glb_max_le => x /AsubB; exact: glb_inf_le. Qed.

Lemma lub_incr L A B : A `<=` B -> lub L A <=_L lub L B.
Proof. by move/(glb_desc [preLattice of L^~]). Qed.

Lemma glbU1 L A a : glb L [fset a; (glb L A)] = glb L (A `|` [fset a]).
Proof.
apply/(@le_anti _ L)/andP; split.
- apply: glb_max_le => x; rewrite !inE; case/orP.
  + move/(glb_inf_le L) => glbAlex; apply:(le_trans _ glbAlex).
    by apply/glb_inf_le; rewrite !inE eq_refl orbT.
  + by move/eqP => ->; apply/glb_inf_le; rewrite !inE eq_refl.
- apply: glb_max_le => x; rewrite !inE; case/orP.
  + by move/eqP => ->; apply: glb_inf_le; rewrite !inE eq_refl orbT.
  + move/eqP => ->; apply: glb_max_le => y yA; apply: glb_inf_le.
    by rewrite !inE yA.
Qed.

Lemma lubU1 L A a: lub L [fset a; lub L A] = lub L (A `|`[fset a]).
Proof. exact:(glbU1 [preLattice of L^~]). Qed.

Lemma glb_empty L : forall x, glb L fset0 >=_L x.
Proof. by move=> x; apply glb_max_le => y; rewrite in_fset0. Qed.

Lemma lub_empty L : forall x, lub L fset0 <=_L x.
Proof. exact: (glb_empty [preLattice of L^~]). Qed.

End PreLatticeTheory.

(* ====================================================================== *)

Section SubLattice.

Context {T : choiceType}.

Definition stable (L: {preLattice T}) (S : {fset T}) :=
  [forall x : S, [forall y : S, glb L [fset (fsval x); (fsval y)] \in S]].


Lemma stableP (L: {preLattice T}) (S : {fset T}) :
  reflect (forall x y, x \in S -> y \in S ->
    glb L [fset x; y] \in S)
    (stable L S).
Proof.
apply/(iffP idP).
- by move => + x y xS yS; move/forallP/(_ [`xS])/forallP/(_ [`yS]).
- move=> stableH; apply/forallP => x; apply/forallP => y.
  apply: stableH; exact: fsvalP.
Qed.

Variable (L: {preLattice T}).

Record subLattice :=
  SubLattice { elements :> {fset T};
  _ : stable L elements && stable ([preLattice of L^~]) elements }.

Canonical subLattice_subType := Eval hnf in [subType for elements].

Definition subLattice_eqMixin := Eval hnf in [eqMixin of subLattice by <:].
Canonical  subLattice_eqType  := Eval hnf in EqType subLattice subLattice_eqMixin.
  
Definition subLattice_choiceMixin := [choiceMixin of subLattice by <:].
Canonical  subLattice_choiceType  :=
  Eval hnf in ChoiceType subLattice subLattice_choiceMixin.

(*TODO : finType*)
  
Coercion mem_subLattice (S: subLattice) : {pred T} :=
  fun x : T => (x \in (elements S)).
Canonical subLattice_predType := PredType mem_subLattice.
  
Lemma in_subLatticeE (S: subLattice) x : (x \in S) = (x \in elements S).
Proof. by []. Qed.
  
Definition inE := (in_subLatticeE, inE).

Definition fmeet (S: subLattice) x y :=
  glb L [fset x; y].
Definition fjoin (S : subLattice) x y:=
  glb ([preLattice of L^~]) [fset x; y].

Definition ftop (S : subLattice) := lub L S.
Definition fbot (S : subLattice) := glb L S.

End SubLattice.

Notation "'\fmeet_' S" := (fmeet S) (at level 8, format "'\fmeet_' S").
Notation "'\fjoin_' S" := (fjoin S) (at level 8, format "'\fjoin_' S").
Notation "'\ftop_' S" := (ftop S) (at level 8, format "'\ftop_' S").
Notation "'\fbot_' S" := (fbot S) (at level 8, format "'\fbot_' S").

Section SubLatticeDual.

Context {T: choiceType} (L: {preLattice T}) (S: subLattice L).

Lemma stableDual : (stable [preLattice of L^~] S) && (stable L S).
Proof. by case: S => S0 stableS0; rewrite andbC. Defined.

Canonical SubLatticeDual := SubLattice stableDual.

End SubLatticeDual.

Notation "S ^~s" := (SubLatticeDual S)
  (at level 8, format "S ^~s").

Section SubLatticeDualTest.

Context {T: choiceType} (L: {preLattice T}) (S: subLattice L).
Goal ((S^~s)^~s) = S.
Proof. by apply/val_inj. Qed.

End SubLatticeDualTest.

Section SubLatticeTheory.

Context {T: choiceType}.
Implicit Type L : {preLattice T}.

Lemma dual_fjoinE L (S: subLattice L) : \fjoin_(S^~s) = \fmeet_S.
Proof. by []. Qed.

Lemma dual_fmeetE L (S: subLattice L) : \fmeet_(S^~s) = \fjoin_S.
Proof. by []. Qed.

Lemma mem_fjoin L (S: subLattice L): {in S &, forall x y, \fjoin_S x y \in S}.
Proof.
move=> x y; rewrite !inE /fjoin /=; case: S => /= elts + xS yS.
by case/andP => _ /stableP/(_ x y xS yS).
Qed.

Lemma mem_fmeet L (S : subLattice L) : {in S &, forall x y, \fmeet_S x y \in S}.
Proof. exact: (@mem_fjoin _ S^~s). Qed.

Lemma fmeetC L (S : subLattice L) : {in S &, commutative (\fmeet_S)}.
Proof.
move=> x y _ _; rewrite /fmeet; congr glb; apply/eqP/fset_eqP => z.
by rewrite !inE orbC.
Qed.

Lemma leIfr L (S : subLattice L) : {in S &, forall x y, \fmeet_S x y <=_L y}.
Proof.
by move=> x y xS yS; rewrite /fmeet glb_inf_le // !inE eq_refl orbT.
Qed.

Lemma leIfl L (S : subLattice L) : {in S &, forall x y, \fmeet_S x y <=_L x}.
Proof.
by move=> x y xS yS; rewrite fmeetC ?leIfr.
Qed.

Lemma lefI L (S : subLattice L) x:
  {in S &, forall y z, (x <=_L \fmeet_S y z) = (x <=_L y) && (x <=_L z)}.
Proof.
move=> y z yS zS; apply/(sameP idP)/(iffP idP).
- case/andP=> xley xlez; rewrite glb_max_le //.
  by move=> t; rewrite !inE; case/orP;move/eqP => ->.
- move=> xlem.
  by rewrite (le_trans xlem (leIfl yS zS)) (le_trans xlem (leIfr yS zS)).
Qed.


Lemma lefIl L (S : subLattice L) :
  {in S & &, forall x y z, y <=_L x -> \fmeet_S y z <=_L x}.
Proof.
move=> x y z xS yS zS ylex.
by rewrite (le_trans (leIfl yS zS) ylex).
Qed.

Lemma lefIr L (S : subLattice L) :
  {in S & &, forall x y z, z <=_L x -> \fmeet_S y z <=_L x}.
Proof. move=> x y z xS yS zS zlex; rewrite fmeetC //; exact: lefIl.
Qed.

Lemma fmeetA L (S : subLattice L) : {in S & &, associative (\fmeet_S) }.
Proof.
move=> x y z xinS yinS zinS; rewrite /fmeet [X in _ = glb L X]fset2C !glbU1.
by congr glb; apply/eqP/fset_eqP => t; rewrite !inE orbC orbA.
Qed.

Lemma fmeetxx L (S : subLattice L) : {in S, idempotent (\fmeet_S)}.
Proof.
by move=> x xS; rewrite /fmeet fset2xx glb1.
Qed.

Lemma leEfmeet L (S : subLattice L) :
  {in S &, forall x y, (x <=_L y) = (\fmeet_S x y == x)}.
Proof.
move=> x y xS yS.
apply/(sameP idP)/(iffP idP).
- move/eqP=> <-; exact: leIfr.
- move=> xley; apply/eqP/(@le_anti _ L); rewrite leIfl ?lefI //=.
  by rewrite lexx xley.
Qed.

Lemma fmeetAC L (S : subLattice L) :
  {in S & &, right_commutative (\fmeet_S)}.
Proof.
move=> x y z xS yS zS.
by rewrite -fmeetA // [X in \fmeet_S _ X]fmeetC // fmeetA.
Qed.

Lemma fmeetCA L (S : subLattice L) :
  {in S & &, left_commutative (\fmeet_S)}.
Proof.
move=> x y z xS yS zS.
by rewrite fmeetA // [X in \fmeet_S X _]fmeetC // -fmeetA.
Qed.


Lemma fmeetACA L (S : subLattice L) :
  forall x y z t, x \in S -> y \in S -> z \in S -> t \in S ->
  \fmeet_S (\fmeet_S x y) (\fmeet_S z t) =
  \fmeet_S (\fmeet_S x z) (\fmeet_S y t).
Proof. 
move=> x y z t xS yS zS tS.
by rewrite !fmeetA ?mem_fmeet // [X in \fmeet_S X _]fmeetAC.
Qed.

Lemma fmeetKI L (S : subLattice L) :
  {in S &, forall x y, \fmeet_S x (\fmeet_S x y) = \fmeet_S x y}.
Proof. by move=> x y xS yS; rewrite fmeetA ?fmeetxx. Qed.

Lemma fmeetIK L (S : subLattice L) :
  {in S &, forall x y, \fmeet_S (\fmeet_S x y) y = \fmeet_S x y}.
Proof. by move=> x y xS yS; rewrite -fmeetA ?fmeetxx. Qed.

Lemma fmeetKIC L (S : subLattice L) :
  {in S &, forall x y, \fmeet_S x (\fmeet_S y x) = \fmeet_S x y}.
Proof. by move=> ? ? ? ?; rewrite fmeetC ?mem_fmeet ?fmeetIK // fmeetC. Qed.

Lemma fmeetIKC L (S : subLattice L) :
  {in S &, forall x y, \fmeet_S (\fmeet_S y x) y = \fmeet_S x y}.
Proof. by move=> ? ? ? ?; rewrite fmeetC ?mem_fmeet ?fmeetKI // fmeetC. Qed.

Lemma leIf2 L (S : subLattice L) :
  {in S & &, forall x y z, (y <=_L x) || (z <=_L x) ->
  \fmeet_S y z <=_L x}.
Proof. 
move=> x y z xS yS zS /orP [ylex | zlex]; [exact: lefIl | exact: lefIr].
Qed.


Lemma fmeet_idPl L (S : subLattice L) {x y} : x \in S -> y \in S ->
  reflect (\fmeet_S x y = x) (x <=_L y).
Proof. move=> xS yS; rewrite (leEfmeet xS yS) //; exact: eqP. Qed.

Lemma fmeet_idPr L (S : subLattice L) {x y} : x \in S -> y \in S ->
  reflect (\fmeet_S y x = x) (x <=_L y).
Proof. by move=> xS yS; rewrite fmeetC //; apply/fmeet_idPl. Qed.

Lemma fmeet_l L (S : subLattice L) :
  {in S &, forall x y, x <=_L y -> \fmeet_S x y = x}.
Proof. move=> x y xS yS; exact/fmeet_idPl. Qed.

Lemma fmeet_r L (S : subLattice L) :
  {in S &, forall x y, y <=_L x -> \fmeet_S x y = y}.
Proof. move=> x y xS yS; exact/fmeet_idPr. Qed.

Lemma lefIidl L (S : subLattice L) :
  {in S &, forall x y, (x <=_L \fmeet_S x y) = (x <=_L y)}.
Proof. by move=> x y xS yS; rewrite !(leEfmeet xS) ?mem_fmeet ?fmeetKI. Qed.

Lemma lefIidr L (S : subLattice L) :
  {in S &, forall x y, (x <=_L \fmeet_S y x) = (x <=_L y)}.
Proof. by move=> x y xS yS; rewrite !(leEfmeet xS) ?mem_fmeet ?fmeetKIC. Qed.

Lemma eq_fmeetl L (S : subLattice L) :
  {in S &, forall x y, (\fmeet_S x y == x) = (x <=_L y)}.
Proof. by move=> ????; apply/esym/leEfmeet. Qed.

Lemma eq_fmeetr L (S: subLattice L) :
  {in S &, forall x y, (\fmeet_S x y == y) = (y <=_L x)}.
Proof. by move=> ????; rewrite fmeetC ?eq_fmeetl. Qed.

Lemma lefI2 L (S : subLattice L) x y z t :
  x \in S -> y \in S -> z \in S -> t \in S ->
  x <=_L z -> y <=_L t -> \fmeet_S x y <=_L \fmeet_S z t.
Proof.
move=> xS yS zS tS xlez ylet.
by rewrite lefI ?mem_fmeet // lefIl // lefIr.
Qed.

(* -------------------------------------------------------------------- *)

Lemma fjoinC L (S : subLattice L) : {in S &, commutative (\fjoin_S)}.
Proof. exact: (@fmeetC _ S^~s). Qed.

Lemma lefUr L (S: subLattice L) : {in S &, forall x y, x <=_L \fjoin_S y x}.
Proof. 
move=> ????; exact: (@leIfr _ S^~s).
Qed.

Lemma lefUl L (S : subLattice L) : {in S &, forall x y, x <=_L \fjoin_S x y}.
Proof.
move=> ????; exact: (@leIfl _ S^~s).
Qed.

Lemma leUf L (S : subLattice L) x : {in S &, forall y z,
  (\fjoin_S y z <=_L x) = (y <=_L x) && (z <=_L x)}.
Proof.
move=> ????; exact: (@lefI _ S^~s).
Qed.

Lemma fjoinA L (S : subLattice L) : {in S & &, associative (\fjoin_S)}.
Proof. exact: (@fmeetA _ S^~s). Qed.

Lemma fjoinxx L (S : subLattice L) : {in S, idempotent (\fjoin_S)}.
Proof. exact: (@fmeetxx _ S^~s). Qed.

Lemma leEfjoin L (S : subLattice L) :
  {in S &, forall x y, (x <=_L y) = (\fjoin_S y x == y)}.
Proof.
move=> ????; exact: (@leEfmeet _ S^~s).
Qed.

Lemma fjoinAC L (S : subLattice L) :
  {in S & &, right_commutative (\fjoin_S)}.
Proof. exact: (@fmeetAC _ S^~s). Qed.

Lemma fjoinCA L (S : subLattice L) :
  {in S & &, left_commutative (\fjoin_S)}.
Proof. exact: (@fmeetCA _ S^~s). Qed.

Lemma fjoinACA L (S : subLattice L) x y z t :
  x \in S -> y \in S -> z \in S -> t \in S ->
  \fjoin_S (\fjoin_S x y) (\fjoin_S z t) =
  \fjoin_S (\fjoin_S x z) (\fjoin_S y t).
Proof. exact: (@fmeetACA _ S^~s). Qed.

Lemma fjoinKI L (S: subLattice L) :
  {in S &, forall x y, \fjoin_S x (\fjoin_S x y) = \fjoin_S x y}.
Proof. exact: (@fmeetKI _ S^~s). Qed.

Lemma fjoinIK L (S : subLattice L) :
  {in S &, forall x y, \fjoin_S (\fjoin_S x y) y = \fjoin_S x y}.
Proof. exact: (@fmeetIK _ S^~s). Qed.

Lemma fjoinKIC L (S : subLattice L) :
  {in S &, forall x y, \fjoin_S x (\fjoin_S y x) = \fjoin_S x y}.
Proof. exact: (@fmeetKIC _ S^~s). Qed.

Lemma fjoinIKC L (S : subLattice L) :
  {in S &, forall x y, \fjoin_S (\fjoin_S y x) y = \fjoin_S x y}.
Proof. exact: (@fmeetIKC _ S^~s). Qed.

Lemma leUfl L (S: subLattice L) :
  {in S & &, forall x y z, x <=_L y -> x <=_L \fjoin_S y z}.
Proof.
move=> ??????; exact: (@lefIl _ S^~s).
Qed.

Lemma leUfr L (S : subLattice L) :
  {in S & &, forall x y z, x <=_L z -> x <=_L \fjoin_S y z}.
Proof.
move=> ??????; exact: (@lefIr _ S^~s).
Qed.

(*Lemma lefU2 L (S : subLattice L) :
  {in S & &, forall x y z, (x <=_L y) || (x <=_L z) ->
  Proof.
  x <=_L \fjoin_S y z}.
move=> ??????; exact: (@leIf2 _ S^~s).
Qed.*)

Lemma fjoin_idPr L (S : subLattice L) {x y}: x \in S -> y \in S ->
  reflect (\fjoin_S y x = x) (y <=_L x).
Proof.
move=> ??; exact: (@fmeet_idPr _ S^~s).
Qed.


Lemma fjoin_idPl L (S: subLattice L) {x y} : x \in S -> y \in S ->
  reflect (\fjoin_S x y = x) (y <=_L x).
Proof.
move=> ??; exact: (@fmeet_idPl _ S^~s).
Qed.

Lemma fjoin_l L (S : subLattice L) :
  {in S &, forall x y, y <=_L x -> \fjoin_S x y = x}.
Proof.
move=> ????; exact: (@fmeet_l _ S^~s).
Qed.

Lemma fjoin_r L (S : subLattice L) :
  {in S &, forall x y, x <=_L y -> \fjoin_S x y = y}.
Proof.
move=> ????; exact: (@fmeet_r _ S^~s).
Qed.

Lemma leUfidl L (S: subLattice L) :
  {in S &, forall x y, (\fjoin_S x y <=_L x) = (y <=_L x)}.
Proof.
move=> ????; exact: (@lefIidl _ S^~s).
Qed.

Lemma leUfidr L (S : subLattice L) :
  {in S &, forall x y, (\fjoin_S y x <=_L x) = (y <=_L x)}.
Proof.
move=> ????; exact: (@lefIidr _ S^~s).
Qed.

Lemma eq_fjoinl L (S : subLattice L) :
  {in S &, forall x y, (\fjoin_S x y == x) = (y <=_L x)}.
Proof.
move=> ????; exact: (@eq_fmeetl _ S^~s).
Qed.

Lemma eq_fjoinr L (S : subLattice L) :
  {in S &, forall x y, (\fjoin_S x y == y) = (x <=_L y)}.
Proof.
move=> ????; exact: (@eq_fmeetr _ S^~s). 
Qed.

Lemma leUf2 L (S: subLattice L) x y z t :
  x \in S -> y \in S -> z \in S -> t \in S ->
  x <=_L z -> y <=_L t -> \fjoin_S x y <=_L \fjoin_S z t.
Proof.
move=> ????; exact: (@lefI2 _ S^~s). 
Qed.

(* -------------------------------------------------------------------- *)

Lemma mem_fbot L (S : subLattice L) : S != fset0 :> {fset _} ->
  \fbot_S \in S.
Proof.
rewrite /fbot.
have: forall S', S' `<=` S -> S'!= fset0 -> glb L S' \in S.
- move=> S' + /fset0Pn [a] /mem_fset1U; move=> + S'eq.
  rewrite -{}S'eq; elim/fset_ind: S'.
  + rewrite fsetU0 => /fsubsetP a_sub_S; rewrite -fset2xx.
    by apply/mem_fmeet; apply/a_sub_S; rewrite inE.
  + move=> b /= S'' bnS'' Hind /fsubsetP abS''_subS.
    have a_in_S: a \in S by apply: abS''_subS; rewrite !inE eq_refl.
    have b_in_S: b \in S by apply: abS''_subS; rewrite !inE eq_refl orbT.  
    rewrite fsetUCA fsetUC -glbU1 mem_fmeet //.
    apply/Hind/fsubsetP=> z zaS''; apply/abS''_subS.
    by rewrite fsetUCA inE zaS'' orbT.
by move/(_ S) => + Sprop; move/(_ (fsubset_refl S) Sprop).
Qed.

Lemma mem_ftop L (S : subLattice L) : S != fset0 :> {fset _} ->
  \ftop_S \in S.
Proof. exact: (@mem_fbot _ S^~s). Qed.

Lemma le0f L (S : subLattice L) : S != fset0 :> {fset _} ->
  {in S, forall x, \fbot_S <=_L x}.
Proof. move=> Sprop0 x xS; exact: glb_inf_le. Qed.

Lemma fjoinf0 L (S : subLattice L) : S != fset0 :> {fset _} ->
  {in S, right_id \fbot_S (\fjoin_S)}.
Proof. by move=> Sprop0 x xS; apply/eqP; rewrite eq_fjoinl ?le0f ?mem_fbot. Qed.

Lemma fjoin0f L (S : subLattice L): S != fset0 :> {fset _} ->
  {in S, left_id \fbot_S (\fjoin_S)}.
Proof. by move=> Sprop0 x xS; apply/eqP; rewrite eq_fjoinr ?le0f ?mem_fbot. Qed.

Lemma lef1 L (S : subLattice L) : S != fset0 :> {fset _} ->
  {in S, forall x, x <=_L \ftop_S}.
Proof.
move=> ???; exact: (@le0f _ S^~s).
Qed.

Lemma fmeetf1 L (S : subLattice L) : S != fset0 :> {fset _} ->
  {in S, right_id \ftop_S (\fmeet_S)}.
Proof. exact: (@fjoinf0 _ S^~s). Qed.

Lemma fmeet1f L (S : subLattice L) : S != fset0 :> {fset _} ->
  {in S, left_id \ftop_S (\fmeet_S)}.
Proof. exact: (@fjoin0f _ S^~s). Qed.

(* ---------------------------------------------------------------------- *) 


Lemma ftop_id L (S: subLattice L) : S!= fset0 :> {fset _} ->
  {in S, forall t, (forall x, x \in S -> x <=_L t) -> \ftop_S = t}.
Proof.
move=> Sprop0 t tS ttop; apply/(@le_anti _ L).
by rewrite lef1 //= andbT; apply/ttop; rewrite mem_ftop.
Qed.

  

Lemma ftopE L (S: subLattice L) : S != fset0 :> {fset _} ->
  \ftop_S = \big[\fjoin_S / \fbot_S]_(i <- S) i.
Proof.
move=> Sprop0; apply/ftop_id => //.
- rewrite big_seq; elim/big_ind:  _ => //.
  + exact: mem_fbot.
  + exact: mem_fjoin.
- move=> x x_in_S; rewrite big_seq.
  rewrite (@big_mem_sub _ _ _ _ (mem S) _ _ _ _ _ _ x x_in_S x_in_S) => //.
  + rewrite lefUl //; apply/big_stable => //;
      [exact:mem_fjoin | exact: mem_fbot].
  + move=> ????; exact: fjoinC.
  + move=> ??????; exact: fjoinA.
  + exact: mem_fjoin.
  + exact: mem_fbot.
Qed.

Lemma fbot_id L (S: subLattice L) : S != fset0 :> {fset _} ->
  {in S, forall t, (forall x, x \in S -> x >=_L t) -> \fbot_S = t}.
Proof. exact: (@ftop_id _ S^~s). Qed.

Lemma fbotE L (S: subLattice L) : S != fset0 :> {fset _} ->
\fbot_S = \big[\fmeet_S / \ftop_S]_(i <- S) i.
Proof. exact: (@ftopE _ S^~s). Qed.


End SubLatticeTheory.


(* ==================================================================== *)
Section Atom.
Context {T : choiceType}.
Implicit Type (L : {preLattice T}).

Definition atom L (S : subLattice L) a := [&& a \in S, (\fbot_S <_L a) &
  ~~[exists x : S, (\fbot_S <_L val x) && (val x <_L a)]].

Definition coatom L (S : subLattice L) a := @atom _ S^~s a.

Lemma atomP L (S : subLattice L) a: reflect
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

Lemma coatomP L (S : subLattice L) a: reflect
  ([/\ a \in S, (a <_L \ftop_S) &
  forall x, x \in S -> x <_L \ftop_S -> ~~(a <_L x)])
  (coatom S a).
Proof. apply/(iffP idP).
- by move/atomP.
- move=> ?; exact/atomP.
Qed.

End Atom.

(* ==================================================================== *)
Section SubLatticeInd.

Context {T : choiceType}.
Implicit Type (L:{preLattice T}).

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

Lemma stable_interval L (S:subLattice L) a b:
  stable L (interval S a b) && stable ([preLattice of L^~]) (interval S a b).
Proof.
apply/andP; split; apply/stableP => x y /intervalP [xS ax xb]
  /intervalP [yS ay yb]; apply/intervalP; split.
- exact: mem_fmeet.
- by rewrite (lefI _ xS yS) ax ay.
- by apply/(le_trans _ xb)/(@leIfl _ _ S).
- exact: mem_fjoin.
- exact/(le_trans ax)/(@lefUl _ _ S).
- by rewrite (leUf _ xS yS) xb yb.
Qed.

Definition SubLatInterval L (S: subLattice L) a b :=
  SubLattice (stable_interval S a b).

Notation " [< a ; b >]_ S " := (@SubLatInterval _ S a b)
  (at level 0, S at level 8, format "[<  a ;  b  >]_ S").

Lemma in_intervalP L (S: subLattice L) a b x:
  reflect
   [/\ x \in S, a <=_L x & x <=_L b]
    (x \in [< a ; b >]_S).
Proof. by rewrite !inE; exact:and3P. Qed.

Lemma intv_id L (S: subLattice L) : [<\fbot_S; \ftop_S>]_S = S.
Proof.
case/boolP: (S == fset0 :> {fset _}).
- move/eqP => Seq0; apply/eqP/fset_eqP => x.
  by rewrite !inE Seq0 in_fset0.
- move=> Sprop0; apply/eqP/fset_eqP => x.
  rewrite !inE; apply: andb_idr => xS.
  by rewrite le0f ?lef1.
Qed.

Lemma mono_interval L (S : subLattice L) (x y x' y' : T) :
  x'<=_L x -> y <=_L y' -> [< x; y >]_[< x'; y' >]_S = [< x; y >]_S.
Proof.
move=> lex ley; apply/eqP/fset_eqP => z.
rewrite !inE; case/boolP: (z \in S) => //.
move=> zS /=; apply: andb_idl => /andP [xlez zley].
by rewrite (le_trans lex xlez) (le_trans zley ley).
Qed.

Lemma sub_interval L (S : subLattice L) c d: {in S &, forall a b,
  a <=_L b -> c <=_L d ->
  ([<a;b>]_S `<=` [<c;d>]_S)%fset = (c <=_L a) && (b <=_L d)}.
Proof.
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
Qed.

Lemma dual_intv_r L (S : subLattice L) a b :
  ([<a; b>]_S)^~s = [< b ; a>]_(S^~s).
Proof. by apply/eqP/fset_eqP => x; rewrite !inE /= [X in _ && X]andbC. Qed.

Definition dual_intv := (@dual_intv_r, fun L => @dual_intv_r [preLattice of L^~]).

Lemma mem_intv_dual L (S : subLattice L) a b : 
  [<a; b>]_(S^~s) =i [<b; a>]_S.
Proof. by move=> x; rewrite !inE /= [X in _ && X]andbC. Qed.

Lemma inL_intv L (S : subLattice L) (x y : T) :
  x \in S -> x <=_L y -> x \in [< x; y >]_S.
Proof. by move=> ??; apply/in_intervalP; split=> //; rewrite lexx. Qed.

Lemma inR_intv L (S : subLattice L) (x y : T) :
  y \in S -> x <=_L y -> y \in [< x; y >]_S.
Proof. by move=> ??; rewrite -mem_intv_dual inL_intv. Qed.

Lemma in0L_intv L (S : subLattice L) (y : T) :
  y \in S -> \fbot_S \in [< \fbot_S; y >]_S.
Proof.
by move=> nz_S; rewrite inL_intv ?mem_fbot ?le0f //; apply/fset0Pn; exists y. 
Qed.

Lemma in0R_intv L (S : subLattice L) (x : T) :
  x \in S -> \ftop_S \in [< x; \ftop_S >]_S.
Proof.
move=> ?; rewrite -mem_intv_dual.
have <-: \fbot_(S^~s) = \ftop_S by [].
exact:in0L_intv.
Qed.

Lemma intv0E L (S : subLattice L) (a b : T) :
  a \in S -> a <=_L b -> \fbot_([<a; b>]_S) = a.
Proof.
move=> aS ab; apply:fbot_id.
- by apply/fset0Pn; exists a; rewrite !inE aS ab lexx.
- by rewrite !inE aS ab lexx.
- by move=> x; rewrite !inE => /and3P [].
Qed.


Lemma intv1E L (S : subLattice L) (a b : T) :
  b \in S -> a <=_L b -> \ftop_[<a; b>]_S = b.
Proof.
by move: (@intv0E _ S^~s b a); rewrite -dual_intv.
Qed.

Lemma sub_atomic L (S: subLattice L) x:
  x \in S -> \fbot_S <_L x ->
  exists y, atom S y /\ y <=_L x.
Proof.
set S' := ([< \fbot_S; x >]_S `\` [fset \fbot_S; x])%fset.
move=> x_in_S bot_lt_x.
have Sprop0: S != fset0 :> {fset _} by apply/fset0Pn; exists x.
case/boolP: (S' == fset0).
- rewrite fsetD_eq0 => /fsubsetP intv_sub.
  exists x; split; rewrite ?lexx //.
  apply/atomP; split => // y y_in_S; apply: contraTN => y_lt_x.
  rewrite lt_neqAle le0f ?andbT //.
  have/intv_sub: (y \in [<\fbot_S; x>]_S) by
    apply/in_intervalP; split; [by []| exact: le0f |exact:ltW].
  by rewrite !inE (lt_eqF y_lt_x) orbF => /eqP ->; rewrite eq_refl.
- case/(minset_neq0 L)/fset0Pn => y /mem_minsetE.
  rewrite !inE negb_or.
  case => /and4P [/andP [yNbot y_neq_x] y_in_S bot_le_y y_le_x mini_y].
  exists y; split => //; apply/atomP; split => //.
    by rewrite lt_neqAle yNbot bot_le_y.
  move=> x0 x0_in_S bot_lt_x0; apply: contraT; rewrite negbK => x0_lt_y.
  have/mini_y: x0 \in S'.
    rewrite !inE x0_in_S eq_sym (lt_eqF bot_lt_x0) (ltW bot_lt_x0) /=.
    rewrite -lt_def; exact: (lt_le_trans x0_lt_y).
  by rewrite x0_lt_y.
Qed.

Lemma sub_coatomic L (S: subLattice L) x:
  x \in S -> x <_L \ftop_S -> exists y, coatom S y /\ x <=_L y.
Proof. exact: (@sub_atomic _ S^~s). Qed.


(* -------------------------------------------------------------------- *)
Section IndIncr.
Context (L : {preLattice T}).
Variable (P : subLattice L -> Prop).

Hypothesis (P_incr : forall S, forall x,
  atom S x -> P S -> P [<x; \ftop_S>]_S).

Lemma ind_incr (S : subLattice L) (x : T) :
  x \in S -> P S -> P [<x; \ftop_S>]_S.
Proof.
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
Qed.
End IndIncr.



(* -------------------------------------------------------------------- *)
Section IndDecr.
Lemma dualK (L : {preLattice T}) (S : subLattice L) : (S^~s)^~s = S.
Proof. by exact/val_inj. Qed.

Lemma fbot_dual_r (L : {preLattice T}) (S : subLattice L) :
  \fbot_(S^~s) = \ftop_S.
  
  Notation dualize := (fun f => (@f, fun L => @f [preLattice of L^~])).
  Proof. by []. Qed.

Definition fbot_dual := dualize fbot_dual_r.

Context (L : {preLattice T}).
Variable (P : subLattice L -> Prop).

Hypothesis (P_decr : forall S, forall x,
  coatom S x -> P S -> P [<\fbot_S; x>]_S).

Lemma ind_decr (S : subLattice L) (x : T) :
  x \in S -> P S -> P [<\fbot_S; x>]_S.
Proof.
move=> x_in_S PS.
rewrite -[S]dualK -dual_intv fbot_dual.
apply: (ind_incr (P := fun S' : subLattice [preLattice of L^~] => P S'^~s)) => //.
- by move=> S' x' ??; rewrite dual_intv; apply: P_decr.
- by rewrite dualK.
Qed.

End IndDecr.

(* -------------------------------------------------------------------- *)
Section Ind.
Context (L : {preLattice T}).
Variable (P : subLattice L -> Prop).

Hypothesis (P_incr : forall (S: subLattice L), forall x,
  atom S x -> P S -> P [<x; \ftop_S>]_S).
Hypothesis (P_decr : forall (S:subLattice L), forall x,
  coatom S x -> P S -> P [<\fbot_S; x>]_S).

Lemma ind_id (S : subLattice L) (x y : T) :
  x \in S -> y \in S -> x <=_L y -> P S -> P [<x; y>]_S.
Proof.
move=> xS yS le_xy PS; have h: P [< x; \ftop_S >]_S by apply: ind_incr.
have Sprop0 : S != fset0 :> {fset _} by apply/fset0Pn; exists x.
suff: P [< \fbot_[< x; \ftop_S >]_S; y >]_[< x; \ftop_S >]_S.
- by rewrite intv0E ?lef1 // mono_interval // ?lexx ?lef1.
apply: ind_decr => //; apply/in_intervalP; split=> //.
by rewrite lef1.
Qed.
End Ind.

End SubLatticeInd.

(* ==================================================================== *)
(*
Module GradedLattice.
Section ClassDef.
Context {T: eqType}.

Record class (L : {tblattice T}) := Class {
  rank : T -> nat;
  _ : rank (bottom L) = O%N;
  _ : forall x y, x <_L y -> (rank x < rank y)%N;
  _ : forall x y, x <=_L y -> ((rank x).+1 < rank y)%N -> exists z, (x <_L z) && (z <_L y)
}.

Structure pack (phr : phant T) := Pack {
  pack_lattice;
  pack_class : class pack_lattice
}.

Local Coercion pack_lattice : pack >-> TBLattice.pack.
Local Coercion pack_class : pack >-> class.

Variable (phr : phant T) (gl : pack phr).

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
*)

(*==================================================================== *)
(*

Section SubsetLattice.
Variable (T : finType).

Definition subset (A B : {set T}) := A \subset B.
Definition ssubset (A B : {set T}) := (A != B) && subset A B.

Lemma subset_order : axiom subset.
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

*)
