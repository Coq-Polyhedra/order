From mathcomp Require Import all_ssreflect finmap.

Section Bijective.

Definition bijective_in_on {T1 T2}
           (P1 : mem_pred T1) (P2 : mem_pred T2) f :=
  exists g, [/\ prop_in1 P2 (inPhantom (forall y, g y \in P1)),
          prop_in1 P1 (inPhantom (cancel f g))
        & prop_in1 P2 (inPhantom (cancel g f))].

Notation "{ 'in' P1 & 'on' P2 , 'bijective' f }" :=
  (bijective_in_on (mem P1) (mem P2) f)
    (at level 0, f at level 8, format "'[hv' { 'in'  P1  &  'on'  P2 , '/ '  'bijective'  f } ']'") : type_scope.

Lemma inj_surj_bij (T1 T2 : choiceType)
      (P1 : mem_pred T1) (P2 : mem_pred T2) (f : T1 -> T2) y0 :
  y0 \in P2 -> {in P1, forall x, (f x) \in P2 } ->
  {in P1 & , injective f} ->
  {in P2, forall y, exists2 x, x \in P1 & y = f x} ->
  {in P1 & on P2, bijective f}.
Proof.
move => P2y0 f_im f_inj f_surj.
have {}f_surj: forall y, P2 y -> exists x, (P1 x) && (y == f x).
+ by move => y /f_surj [x ??]; exists x; apply/andP; split => //; apply/eqP.
pose g y := match @idP (P2 y) with
           | ReflectT P2y => xchoose (f_surj _ P2y)
           | _ => xchoose (f_surj _ P2y0)
           end.
exists g; split.
+ move=> y ?; rewrite /g; case: {-}_/idP=> // P2y.
  by case/andP: (xchooseP (f_surj _ P2y)).
+ move=> x P1x; rewrite /g; case: {-}_/idP=> [P2fx |].
  - by case/andP: (xchooseP (f_surj _ P2fx))=> ? /eqP?; apply/f_inj.
  - by move/f_im: P1x.
+ move => y ?; rewrite /g; case: {-}_/idP=> // P2y.
  by case/andP: (xchooseP (f_surj _ P2y)) => _ /eqP/esym.
Qed.

Lemma in_on_bij_inj {T1 T2} {P1 : mem_pred T1} {P2 : mem_pred T2} {f} :
  {in P1 & on P2, bijective f} -> {in P1 &, injective f}.
Proof. by case => g [_ /can_in_inj]. Qed.

Lemma in_on_bij_id T (P : mem_pred T) :
  {in P & on P, bijective id}.
Proof. by exists id; split; move=> ?. Qed.

End Bijective.

Notation "{ 'in' P1 & 'on' P2 , 'bijective' f }" :=
  (bijective_in_on (mem P1) (mem P2) f)
    (at level 0, f at level 8, format "'[hv' { 'in'  P1  &  'on'  P2 , '/ '  'bijective'  f } ']'") : type_scope.

Local Open Scope fset_scope.

Section FSetLemmas.

Context {T: choiceType}.

Lemma fset2C (a b : T): [fset a; b] = [fset b; a].
Proof. by apply/eqP/fset_eqP => x; rewrite !inE orbC. Qed.

Lemma fset2xx (a : T) : [fset a; a] = [fset a].
Proof. by apply/eqP/fset_eqP => x; rewrite !inE orbb. Qed.

End FSetLemmas.

(* ==================================================================== *)
Section FSetRect.
Context (T : choiceType) (P : {fset T} -> Type).

Hypothesis P0 : P fset0.
Hypothesis PS : forall x S, x \notin S -> P S -> P (x |` S).

Lemma fset_rect S : P S.
Proof.
move: {2}#|`S| (@leqnn #|`S|) => n; elim: n S => [|n ih] S.
- by rewrite leqn0 cardfs_eq0 => /eqP->.
rewrite leq_eqVlt ltnS orbC; case: leqP => /= [/ih //|_ nz_S].
have: S != fset0 by rewrite -cardfs_gt0 (eqP nz_S).
move/fset0Pn => x; have: xchoose x \in S by apply: xchooseP.
move/fsetD1K => <-; apply: PS; first by rewrite !in_fsetE eqxx.
apply: ih; move: nz_S; rewrite (cardfsD1 (xchoose x)).
by rewrite (xchooseP x) add1n => /eqP[] <-.
Qed.
End FSetRect.

Definition fset_ind (T : choiceType) (P : {fset T} -> Prop) :=
  @fset_rect T P.

(* ======================================================================= *)

Lemma andPP P Q b c :
  reflect P b -> reflect Q c -> reflect (P /\ Q) (b && c).
Proof.
by move=> /rwP Pb /rwP Qc; apply: (iffP andP); intuition.
Qed.

Notation "'and_[ view1 , view2 ]" := (@andPP _ _ _ _ view1 view2)
  (at level 4, right associativity, format "''and_[' view1 ,  view2 ]").

Lemma implyPP (P Q : Prop) (b c : bool) :
  reflect P b -> reflect Q c -> reflect (P -> Q) (b ==> c).
Proof. by move=> /rwP Pb /rwP Qc; apply: (iffP implyP); intuition. Qed.

Notation "'imply_[ view1 , view2 ]" := (@implyPP _ _ _ _ view1 view2)
  (at level 4, right associativity, format "''imply_[' view1 ,  view2 ]").
