From mathcomp Require Import all_ssreflect.

Section BigOpSub.

Context {T : eqType} {x0 : T} {op : T -> T -> T} {P Q : pred T}.

Hypothesis hc : forall x y, Q x -> Q y -> op x y = op y x.
Hypothesis ha : forall x y z, Q x -> Q y -> Q z -> op x (op y z) = op (op x y) z.
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
      by rewrite ha ?big_stable // [X in op X _]hc // ha ?big_stable.
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
  + by move=> Pa; rewrite (big_mem_sub s a a_in_s) // NHind.
  + by move=> nPa; rewrite NHind -big_nmem_sub.
Qed.

End BigOpSub.

Section BigOpSub2.

Context {T : eqType} {op : T -> T -> T} {Q : pred T}.

Hypothesis hc : forall x y, Q x -> Q y -> op x y = op y x.
Hypothesis ha : forall x y z, Q x -> Q y -> Q z -> op x (op y z) = op (op x y) z.
Hypothesis hs : forall x y, Q x -> Q y -> Q (op x y).
Hypothesis hxx : forall x, Q x -> op x x = x.

Lemma perm_eq2C (a b: T) (l : seq T) :
  perm_eq [:: a, b & l] [:: b, a & l].
Proof. by have /permPl := perm_catCA [:: a] [:: b] l. Qed.

Lemma big_cons_idx (r : seq T) (x0 y0 : T) :
  Q x0 -> Q y0 ->
  \big[op/x0]_(x <- y0::r | Q x) x = \big[op/op x0 y0]_(x <- r | Q x) x.
Proof.
move=> Qx0 Qy0; elim: r => [|a l Hind].
- by rewrite big_cons !big_nil hc ?Qy0 ?Qx0.
- move: (perm_eq2C y0 a l) => permL.
  rewrite (big_perm_sub hc ha hs (fun x H => H) Qx0 _ _ permL).
  by rewrite big_cons [RHS]big_cons Hind.
Qed.

Lemma big_idxx (r : seq T) (x0 y0 : T):
  x0 \in r -> y0 \in r -> Q x0 -> Q y0 ->
  \big[op/x0]_(x <- r | Q x) x = \big[op/y0]_(x <- r | Q x) x.
Proof.
move=> x0r y0r Qx0 Qy0; case/boolP: (y0 == x0).
- by move/eqP => ->.
- move/negP=> y0nx0; move: (perm_to_rem x0r) => permx0.
  rewrite (big_perm_sub hc ha hs (fun x H => H) Qx0 _ _ permx0).
  rewrite (big_perm_sub hc ha hs (fun x H => H) Qy0 _ _ permx0).
  rewrite !big_cons_idx //.
  rewrite (perm_mem permx0) inE in y0r.
  case/orP : y0r => // /perm_to_rem => permy0.
  rewrite hxx //; have Qy0x0 : Q (op y0 x0) by rewrite hs.
  rewrite (big_perm_sub hc ha hs (fun x H => H) Qx0 _ _ permy0).
  rewrite (big_perm_sub hc ha hs (fun x H => H) Qy0x0 _ _ permy0).
  rewrite !big_cons_idx //.
  suff -> : op (op y0 x0) y0 = op x0 y0 by [].
  by rewrite [X in op X _]hc -?ha ?hxx.
Qed.
End BigOpSub2.

Section BigOpSubF.

Context {T : eqType} {op : T -> T -> T} {F : T -> T} {P Q : pred T}.
Context {x0 : T}.

Hypothesis hc : forall x y, Q x -> Q y -> op x y = op y x.
Hypothesis ha : forall x y z, Q x -> Q y -> Q z -> op x (op y z) = op (op x y) z.
Hypothesis hs : forall x y, Q x -> Q y -> Q (op x y).
Hypothesis hxx : forall x, Q x -> op x x = x.
Hypothesis PQ : forall x, P x -> Q x.
Hypothesis hF : forall x, Q x -> Q (F x).
Hypothesis Q0 : Q x0.

Lemma big_map_fun (r : seq T) :
  \big[op/x0]_(i <- r | P i) F i =
  \big[op/x0]_(i <- [seq F j | j <- r & P j]) i.
Proof.
elim: r.
- by rewrite /= !big_nil.
- move=> a l Hind; rewrite /= big_cons; case: (P a) => //=.
  by rewrite big_cons; congr op.
Qed.

End BigOpSubF.
