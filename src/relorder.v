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
