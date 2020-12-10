From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BigOpSub.

Parameter (T : eqType).
Parameter x0 : T.
Parameter op : T -> T -> T.
Parameter P : pred T.
Parameter Q : pred T.

Hypothesis hc : forall x y, Q x -> Q y -> op x y = op y x.
Hypothesis ha : forall x y z, Q x -> Q y -> Q x -> op x (op y z) = op (op x y) z.
Hypothesis hs : forall x y, Q x -> Q y -> Q (op x y).
Hypothesis PQ : forall x, P x -> Q x.
Hypothesis Q0 : Q x0.

Lemma big_stable (t : seq T) : Q (\big[op/x0]_(y <- t | P y) y).
Proof.
elim: t.
    by rewrite big_nil.
move=> a l Hind; rewrite big_cons; case/boolP: (P a).
    by move/PQ/hs/(_ Hind).
move=> _; exact: Hind.
Qed.


Lemma big_mem_sub (r : seq T) x : x \in r -> P x ->
    \big[op/x0]_(y <- r | P y) y = op x (\big[op/x0]_(y <- (rem x r) | P y) y).
Proof.
elim: r; rewrite ?in_nil // => a l Hind; rewrite inE; case/orP.
- by move/eqP => -> /=; rewrite eq_refl big_cons => ->.
- move=> /=; case/boolP: (a == x).
  + by move/eqP => <-; rewrite big_cons => _ ->.
  + move=> aneqx x_in_l Px; rewrite !big_cons; case/boolP: (P a).
    - move/PQ => Qa; rewrite Hind //; have Qx: (Q x) by apply: PQ.
      by rewrite ha // [X in op X _]hc // ha.
    - move=> _; exact: Hind.
Qed. 

Lemma big_nmem_sub (r : seq T) x: x \in r -> ~~ P x ->
  \big[op/x0]_(y <- r | P y) y = \big[op/x0]_(y <- rem x r | P y) y.
Proof.
elim: r; rewrite ?in_nil // => a l Hind; rewrite inE; case/orP.
- by move/eqP => ->; rewrite big_cons /= eq_refl; case: (P a).
- move=> x_in_l; rewrite big_cons /=; case/boolP: (a == x).
  + by move/eqP => <-; case: (P a).
  + by move=> _ nPx; rewrite big_cons; case: (P a); rewrite Hind.
Qed.

Lemma big_perm_sub (r : seq T) : forall s: seq T, perm_eq r s ->
  \big[op/x0]_(x <- r | P x) x = \big[op/x0]_(x <- s | P x) x.
Proof.
elim: r.
- by move=> s; rewrite perm_sym; move/perm_nilP => ->.
- move=> a l Hind s eq_rs; move: (perm_mem eq_rs) => r_mem_s.
  have a_in_s: a \in s by rewrite -r_mem_s !inE eq_refl.
  move: (perm_to_rem a_in_s) => eq_srm.
  move: (perm_trans eq_rs eq_srm); rewrite perm_cons.
  move/Hind => NHind; rewrite big_cons; case/boolP: (P a).
  + by move=> Pa; rewrite (big_mem_sub a_in_s) // NHind.
  + by move=> nPa; rewrite NHind -big_nmem_sub.
Qed.
  
End BigOpSub.