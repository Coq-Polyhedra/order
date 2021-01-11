(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import xbigop extra_misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope fset_scope.
Local Open Scope ring_scope.

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
Notation "x <=_ r y" := (<=:r x y) (at level 65, y at next level, r at level 2, format "x  <=_ r  y").
Notation "x >=_ r y" := (y <=_r x) (at level 65, y at next level, r at level 2, only parsing).
Notation "x <_ r y" := (<:r x y) (at level 65, y at next level, r at level 2, format "x  <_ r  y").
Notation "x >_ r y" := (y <_r x) (at level 65, y at next level, r at level 2, only parsing).
Notation "x <=_ r0 y <=_ r1 z" := ((x <=_r0 y) && (y <=_r1 z))
  (at level 65, y, z at next level, r0 at level 2, r1 at level 2, format "x  <=_ r0  y  <=_ r1  z").
Notation "x <_ r0 y <_ r1 z" := ((x <_r0 y) && (y <_r1 z))
  (at level 65, y, z at next level, r0 at level 2, r1 at level 2, format "x  <_ r0  y  <_ r1  z").
Notation "x <=_ r0 y <_ r1 z" := ((x <=_r0 y) && (y <_r1 z))
  (at level 65, y, z at next level, r0 at level 2, r1 at level 2, format "x  <=_ r0  y  <_ r1  z").
Notation "x <_ r0 y <=_ r1 z" := ((x <_r0 y) && (y <=_r1 z))
  (at level 65, y, z at next level, r0 at level 2, r1 at level 2, format "x  <_ r0  y  <=_ r1  z").
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

Context {T: eqType} (r : {porder T}).

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
Hint Extern 0 (is_true (_ <=__ _)) => exact: lexx : core.

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
Arguments le_anti {_} _ [_ _].
Hint Resolve lexx : core.
Hint Extern 0 (is_true (_ <=__ _)) => exact: lexx : core.

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

(*TODO*)

Record class (r : {porder T}) := Class
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

Section PreLatticeDualTest.

Context (T: choiceType) (L : {preLattice T}).
Check erefl L : [preLattice of L^~^~] = L.
End PreLatticeDualTest.

Section PreLatticeTheory.

Context {T: choiceType}.
Implicit Type L: {preLattice T}.

Lemma premeet_min L S:
  {in S &, forall x y, premeet L S x y <=_L x /\ premeet L S x y <=_L y}.
Proof. exact: PreLattice.premeet_min. Qed.

Lemma premeet_inf L S:
  {in S & &, forall x y z, z <=_L x -> z <=_L y -> z <=_L premeet L S x y}.
Proof. exact: PreLattice.premeet_inf. Qed.

Lemma premeet_incr L S S': S `<=` S' ->
  {in S &, forall x y, premeet L S x y <=_L premeet L S' x y}.
Proof. move=> ?????; exact: PreLattice.premeet_incr. Qed.

Lemma prejoin_max L S:
  {in S &, forall x y, prejoin L S x y <=_(L^~) x /\ prejoin L S x y <=_(L^~) y}.
Proof. exact: PreLattice.prejoin_max. Qed.

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

(*Lemma glb_inf_le L: forall S, forall x, x \in S -> x >=_L (glb L S).
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

End PreLatticeTheory.*)

(* ====================================================================== *)

Section SubLattice.

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

End SubLattice.

Notation "{ 'finLattice' L }" := (finLattice L) (at level 0, format "{ 'finLattice'  L }").
Notation "'\fmeet_' S" := (@fmeet _ _ S) (at level 8, format "'\fmeet_' S").
Notation "'\fjoin_' S" := (@fjoin _ _ S) (at level 8, format "'\fjoin_' S").

Section SubLatticeDual.

Context {T : choiceType} (L : {preLattice T}) (S : {finLattice L}).

Lemma stableDual : (stable [preLattice of L^~] S) && (stable L S).
Proof. by case: S => S0 stableS0; rewrite andbC. Defined.

Canonical FinLatticeDual := FinLattice stableDual.

Variable (x : T).
Check (x \in FinLatticeDual).
Check (FinLatticeDual).

End SubLatticeDual.

Notation "S ^~s" := (FinLatticeDual S)
  (at level 8, format "S ^~s").

Section SubLatticeDualTest.

Context {T: choiceType} (L: {preLattice T}) (S: {finLattice L}).
Goal ((S^~s)^~s) = S.
Proof. by apply/val_inj. Qed.

End SubLatticeDualTest.

(* ========================================================================= *)

Section SubLatticeTheory.

Context {T: choiceType}.
Implicit Type L : {preLattice T}.

Lemma dual_fjoinE L (S: {finLattice L}):
  \fjoin_(S^~s)= \fmeet_S.
Proof. by []. Qed.

Lemma dual_fmeetE L (S: {finLattice L}) : \fmeet_(S^~s) = \fjoin_S.
Proof. by []. Qed.

Lemma mem_fjoin L (S: {finLattice L}): {in S &, forall x y, \fjoin_S x y \in S}.
Proof.
move=> x y; rewrite !inE /fjoin /=; case: S => /= elts + xS yS.
by case/andP => _ /stableP/(_ x y xS yS).
Qed.

Lemma mem_fmeet L (S : {finLattice L}) : {in S &, forall x y, \fmeet_S x y \in S}.
Proof. exact: (@mem_fjoin _ S^~s). Qed.

Lemma leIfl L (S : {finLattice L}) : {in S &, forall x y, \fmeet_S x y <=_L x}.
Proof.
by move=> x y xS yS; move: (premeet_min L xS yS) => [].
Qed.

Lemma leIfr L (S : {finLattice L}) : {in S &, forall x y, \fmeet_S x y <=_L y}.
Proof.
by move=> x y xS yS; move: (premeet_min L xS yS) => [].
Qed.

Lemma lefI L (S : {finLattice L}) :
  {in S & &, forall x y z, (x <=_L \fmeet_S y z) = (x <=_L y) && (x <=_L z)}.
Proof.
move=> x y z xS yS zS; apply/(sameP idP)/(iffP idP).
- by case/andP=> xley xlez; apply/premeet_inf.
- move=> xlem.
  by rewrite (le_trans xlem (leIfl yS zS)) (le_trans xlem (leIfr yS zS)).
Qed.

Lemma fmeetC L (S : {finLattice L}) : {in S &, commutative (\fmeet_S)}.
Proof.
move=> x y xS yS; apply: (le_anti L).
by apply/andP; split; rewrite lefI ?mem_fmeet ?leIfl ?leIfr.
Qed.

Lemma lefIl L (S : {finLattice L}) :
  {in S & &, forall x y z, y <=_L x -> \fmeet_S y z <=_L x}.
Proof.
move=> x y z xS yS zS ylex.
by rewrite (le_trans (leIfl yS zS) ylex).
Qed.

Lemma lefIr L (S : {finLattice L}) :
  {in S & &, forall x y z, z <=_L x -> \fmeet_S y z <=_L x}.
Proof. move=> x y z xS yS zS zlex; rewrite fmeetC //; exact: lefIl.
Qed.

Lemma fmeetA L (S : {finLattice L}) : {in S & &, associative (\fmeet_S) }.
Proof.
move=> x y z xS yS zS; apply: (le_anti L).
apply/andP; split; rewrite ?lefI ?leIfl ?leIfr ?mem_fmeet ?andbT //=.
- apply/andP; split.
  + by apply/lefIr => //; rewrite ?mem_fmeet ?leIfl.
  + by apply/lefIr => //; rewrite ?mem_fmeet ?leIfr.
- apply/andP; split.
  + by apply/lefIl => //; rewrite ?mem_fmeet ?leIfl.
  + by apply/lefIl => //; rewrite ?mem_fmeet ?leIfr.
Qed.

Lemma fmeetxx L (S : {finLattice L}) : {in S, idempotent (\fmeet_S)}.
Proof.
move => x xS; apply: (le_anti L).
by rewrite lefIl //= lefI ?lexx.
Qed.

Lemma leEfmeet L (S : {finLattice L}) :
  {in S &, forall x y, (x <=_L y) = (\fmeet_S x y == x)}.
Proof.
move=> x y xS yS.
apply/(sameP idP)/(iffP idP).
- move/eqP=> <-; exact: leIfr.
- move=> xley; apply/eqP/(le_anti L); rewrite leIfl ?lefI //=.
  by rewrite lexx xley.
Qed.

Lemma fmeetAC L (S : {finLattice L}) :
  {in S & &, right_commutative (\fmeet_S)}.
Proof.
move=> x y z xS yS zS.
by rewrite -fmeetA // [X in \fmeet_S _ X]fmeetC // fmeetA.
Qed.

Lemma fmeetCA L (S : {finLattice L}) :
  {in S & &, left_commutative (\fmeet_S)}.
Proof.
move=> x y z xS yS zS.
by rewrite fmeetA // [X in \fmeet_S X _]fmeetC // -fmeetA.
Qed.


Lemma fmeetACA L (S : {finLattice L}) :
  forall x y z t, x \in S -> y \in S -> z \in S -> t \in S ->
  \fmeet_S (\fmeet_S x y) (\fmeet_S z t) =
  \fmeet_S (\fmeet_S x z) (\fmeet_S y t).
Proof.
move=> x y z t xS yS zS tS.
by rewrite !fmeetA ?mem_fmeet // [X in \fmeet_S X _]fmeetAC.
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
move=> xS yS zS tS xlez ylet.
by rewrite lefI ?mem_fmeet // lefIl // lefIr.
Qed.

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

End SubLatticeTheory.

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
apply/(le_anti L)/andP; split.
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

Definition SubLatInterval L (S: {finLattice L}) a b :=
  FinLattice (@stable_interval L S a b).

End Interval.
End Interval.

Notation " [< a ; b >]_ S " := (@Interval.SubLatInterval _ _ S a b)
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
  exists y => //. apply/atomP. split => //.
    by rewrite lt_neqAle yNbot bot_le_y.
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

(* ==================================================================== *)
