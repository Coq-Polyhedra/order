From mathcomp Require Import all_ssreflect finmap.

Open Scope fset_scope.

Section BigOpSub.

Context {T : eqType} {op : T -> T -> T} {P Q : pred T}.

Hypothesis hc : forall x y, Q x -> Q y -> op x y = op y x.
Hypothesis ha : forall x y z, Q x -> Q y -> Q z -> op x (op y z) = op (op x y) z.
Hypothesis hs : forall x y, Q x -> Q y -> Q (op x y).
Hypothesis PQ : forall x, P x -> Q x.

Lemma big_stable {t : seq T} {x0} :
  Q x0 -> Q (\big[op/x0]_(y <- t | P y) y).
Proof.
move => Qx0.
elim: t => [| a l Hind]; first by rewrite big_nil.
by rewrite big_cons; case/boolP: (P a) => [/PQ/hs/(_ Hind)| _].
Qed.

Lemma big_mem_sub {r : seq T} {x0 x} :
  Q x0 -> x \in r -> P x ->
    \big[op/x0]_(y <- r | P y) y = op x (\big[op/x0]_(y <- (rem x r) | P y) y).
Proof.
move => Qx0.
elim: r; rewrite ?in_nil // => a l Hind; rewrite inE; case/orP.
- by move/eqP => -> /=; rewrite eq_refl big_cons => ->.
- move=> /=; case/boolP: (a == x).
  + by move/eqP => <-; rewrite big_cons => _ ->.
  + move=> aneqx x_in_l Px; rewrite !big_cons; case/boolP: (P a).
    - move/PQ => Qa; rewrite Hind //; have Qx: (Q x) by apply: PQ.
      by rewrite ha ?big_stable // [X in op X _]hc // ha ?big_stable.
    - move=> _; exact: Hind.
Qed.

Lemma big_nmem_sub {r : seq T} {x0 x} : x \in r -> ~~ P x ->
  \big[op/x0]_(y <- r | P y) y = \big[op/x0]_(y <- rem x r | P y) y.
Proof.
elim: r; rewrite ?in_nil // => a l Hind; rewrite inE; case/orP.
- by move/eqP => ->; rewrite big_cons /= eq_refl; case: (P a).
- move=> x_in_l; rewrite big_cons /=; case/boolP: (a == x).
  + by move/eqP => <-; case: (P a).
  + by move=> _ nPx; rewrite big_cons; case: (P a); rewrite Hind.
Qed.

Lemma big_perm_sub {r : seq T} {x0} :
  Q x0 -> forall s: seq T, perm_eq r s ->
  \big[op/x0]_(x <- r | P x) x = \big[op/x0]_(x <- s | P x) x.
Proof.
move => Px0; elim: r.
- by move=> s; rewrite perm_sym; move/perm_nilP => ->.
- move=> a l Hind s eq_rs; move: (perm_mem eq_rs) => r_mem_s.
  have a_in_s: a \in s by rewrite -r_mem_s !inE eq_refl.
  move: (perm_to_rem a_in_s) => eq_srm.
  move: (perm_trans eq_rs eq_srm); rewrite perm_cons.
  move/Hind => NHind; rewrite big_cons; case/boolP: (P a).
  + by move=> Pa; rewrite (big_mem_sub _ a_in_s) // NHind.
  + by move=> nPa; rewrite NHind -big_nmem_sub.
Qed.

Lemma perm_eq2C (a b: T) (l : seq T) :
  perm_eq [:: a, b & l] [:: b, a & l].
Proof. by have /permPl := perm_catCA [:: a] [:: b] l. Qed.

Lemma big_cons_idx {r : seq T} {x0 y0 : T} :
  Q x0 -> P y0 ->
  \big[op/x0]_(x <- y0 :: r | P x) x = \big[op/op y0 x0]_(x <- r | P x) x.
Proof.
move=> Qx0 Py0.
elim: r => [|a l Hind].
- by rewrite big_cons !big_nil ifT.
- move: (perm_eq2C y0 a l) => permL.
  rewrite (big_perm_sub _ _ permL) //.
  by rewrite big_cons [RHS]big_cons Hind.
Qed.

Lemma big_rem_idx {r : seq T} {x0 y0 : T} :
  Q x0 -> y0 \in r -> P y0 ->
  \big[op/x0]_(x <- r | P x) x = \big[op/op y0 x0]_(x <- rem y0 r | P x) x.
Proof.
move => Qx0 y0r Py0.
move/(big_perm_sub Qx0): (perm_to_rem y0r) => ->.
exact: big_cons_idx.
Qed.

Hypothesis hxx : forall x, Q x -> op x x = x.

Lemma big_rem_idxx {r : seq T} {x0 y0 : T} :
  Q x0 -> y0 \in r -> P y0 ->
  \big[op/x0]_(x <- r | P x) x = \big[op/op y0 x0]_(x <- r | P x) x.
Proof.
move => Qx0 y0r Py0.
rewrite (big_rem_idx _ _ Py0) -1?{1}[y0 in LHS]hxx -?ha ?hs // ?PQ //.
by rewrite -big_rem_idx ?hs // PQ.
Qed.

Lemma big_idxx {r : seq T} {x0 y0 : T}:
  x0 \in r -> y0 \in r -> P x0 -> P y0 ->
  \big[op/x0]_(x <- r | P x) x = \big[op/y0]_(x <- r | P x) x.
Proof.
move=> x0r y0r Px0 Py0.
by rewrite (big_rem_idxx _ _ Py0) 1?[in RHS](big_rem_idxx _ _ Px0) 1?hc ?PQ.
Qed.

End BigOpSub.

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

Section BigOpSubMorph.

Context {T : eqType} {op1 op2 : T -> T -> T} {P Q : pred T}.
Context {x : T} {f : T -> T}.

Hypothesis f_morph : {in Q&, {morph f : x y / op1 x y >-> op2 x y}}.
Hypothesis PQ : forall x, P x -> Q x.
Hypothesis opQ : {in Q&, forall x y, Q (op1 x y)}.
Hypothesis Qx : Q x.

Lemma big_morph_sub (r : seq T) :
  f (\big[op1/x]_(i <- r | P i) i) =
  \big[op2/f x]_(i <- r| P i) f i.
Proof.
elim r; first by rewrite !big_nil.
move=> a l Hind; rewrite !big_cons; case E: (P a) => //.
rewrite f_morph ?Hind //.
+ exact: PQ.
+ exact: big_stable.
Qed.

End BigOpSubMorph.

Section BigOpVal1.

Context {T: Type} {P : pred T} {S : subType P} (a : S).
Definition fun_val (f : T -> T) (x : S) := insubd a (f (val x)).
Definition fun2_val (f : T -> T -> T) (x y : S) :=
  insubd a (f (val x) (val y)).

Context {op : T -> T -> T} {x0 : T}.
Hypothesis Px0 : P x0.
Hypothesis Pop : {in P &, forall x y, P (op x y)}.

Definition vop := fun2_val op.
Definition vx0 := insubd a x0.

Hypothesis vopA : associative vop.
Hypothesis vop0x : left_id vx0 vop.
Hypothesis vopx0 : right_id vx0 vop.

Definition vmop := Monoid.Law vopA vop0x vopx0.

Hypothesis vopC : commutative vmop.

Definition vcop := Monoid.ComLaw vopC.

Context {I : Type} {F : I -> T}.
Hypothesis FP: forall i, P (F i).

Lemma big_val (r : seq I) (Q : pred I) :
  \big[op / x0]_(i <- r | Q i) F i =
  val (\big[vcop / vx0]_(i <- r | Q i) insubd a (F i)).
Admitted.

End BigOpVal1.

Section BigOpVal2.

Context {T: Type} {P : pred T} {S : subType P} {x0 : S}.
Context {op : Monoid.com_law x0}.


Definition val_fun (f: S -> S) (x : T) :=
  val (f (insubd x0 x)).
Definition val_fun2 (f : S -> S -> S) (x y: T) :=
  val (f (insubd x0 x) (insubd x0 y)).

Context {I : Type} {F : I -> S}.
Lemma big_val_foo (r : seq I) (Q : pred I):
  val (\big[op / x0]_(i <- r | Q i) F i) = 
  \big[val_fun2 op / val x0]_(i <- r | Q i) val (F i).
Proof.
elim : r; rewrite ?big_nil //.
move=> a l Hind; rewrite !big_cons; case : (Q a).
- by rewrite -Hind /val_fun2 !valKd.
- by rewrite -Hind.
Qed.


End BigOpVal2.