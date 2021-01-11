From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import xbigop extra_misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module RelOrder.

Definition dual_rel (T : Type) (r : rel T) := fun y x => r x y.
Definition dual_bottom (T : Type) (top : T) := top.
Definition dual_top (T : Type) (bottom : T) := bottom.
Definition dual_meet (T : Type) (join : T -> T -> T) := join.
Definition dual_join (T : Type) (meet : T -> T -> T) := meet.

(* ========================================================================== *)

Module POrder.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record mixin_of (le lt : rel T) := Mixin {
  lexx : reflexive le;
  le_anti : forall x y, le x y -> le y x -> x = y;
  le_trans : transitive le;
  lt_def : forall x y, (lt x y) = (x != y) && (le x y);
  dlt_def : forall x y, (lt y x) = (x != y) && (le y x);
}.
Unset Primitive Projections.

Notation class_of := mixin_of (only parsing).

(* NB: the interface should not be a primitive record. see:                   *)
(* https://github.com/math-comp/math-comp/pull/462#issuecomment-598130155.    *)
Set Primitive Projections.
Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  class_ : class_of le lt;
}.
Unset Primitive Projections.

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) :=
  let: Pack _ _ c as ord' := ord in c.

Variable (leT ltT : rel T).

Definition clone c of phant_id class c := @Pack phT leT ltT c.

End ClassDef.

Notation class_of := mixin_of (only parsing).

Module Exports.
Notation "{ 'pOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'pOrder'  T }").
Notation POrder le lt mixin := (@Pack _ (Phant _) le lt mixin).
Notation "[ 'leo:' leT ]" :=
  (@clone _ (Phant _) _ leT _ _ id) (at level 0, format "[ 'leo:'  leT ]").
Notation "[ 'lto:' ltT ]" :=
  (@clone _ (Phant _) _ _ ltT _ id) (at level 0, format "[ 'lto:'  ltT ]").
End Exports.

End POrder.
Import POrder.Exports.

Notation le := POrder.le.
Notation lt := POrder.lt.
Arguments le {T phT} ord x y : rename, simpl never.
Arguments lt {T phT} ord x y : rename, simpl never.

(* ========================================================================== *)

Module BPOrder.

Section ClassDef.

Variable T : eqType.

Definition mixin_of (le : rel T) (bottom : T) := forall x, le bottom x.

Set Primitive Projections.
Record class_of (le lt : rel T) (bottom : T) := Class {
  base : POrder.class_of le lt;
  mixin : mixin_of le bottom;
}.
Unset Primitive Projections.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  bottom : T;
  _ : class_of le lt bottom;
}.

Local Coercion base : class_of >-> POrder.class_of.

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (bottom ord) :=
  let: Pack _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.

Variable (leT ltT : rel T) (bottomT : T).

Definition clone c of phant_id class c := @Pack phT leT ltT bottomT c.

Definition pack (m0 : forall x, leT bottomT x) :=
  fun (bord : POrder.order phT) b
        & phant_id (POrder.class bord) b =>
  fun m & phant_id m0 m => @Pack phT leT ltT bottomT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Notation "{ 'bPOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'bPOrder'  T }").
Notation BPOrder le lt bottom mixin :=
  (@pack _ (Phant _) le lt bottom mixin _ _ id _ id).
Notation "[ 'bPOrder' 'of' le ]" :=
  (@clone _ (Phant _) _ le (nosimpl _) (nosimpl _) _ id)
  (at level 0, format "[ 'bPOrder'  'of'  le ]").
End Exports.

End BPOrder.
Import BPOrder.Exports.

Notation bottom := BPOrder.bottom.
Arguments bottom {T phT} ord : rename, simpl never.

(* ========================================================================== *)

Module TPOrder.

Section ClassDef.

Variable T : eqType.

Definition mixin_of (le : rel T) (top : T) := forall x, le x top.

Set Primitive Projections.
Record class_of (le lt : rel T) (top : T) := Class {
  base : POrder.class_of le lt;
  mixin : mixin_of le top;
}.
Unset Primitive Projections.

Set Primitive Projections.
Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  top : T;
  class_ : class_of le lt top;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (top ord) :=
  let: Pack _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.

Variable (leT ltT : rel T) (topT : T).

Definition clone c of phant_id class c := @Pack phT leT ltT topT c.

Definition pack (m0 : forall x, leT x topT) :=
  fun (bord : POrder.order phT) b
        & phant_id (POrder.class bord) b =>
  fun m & phant_id m0 m => @Pack phT leT ltT topT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Notation "{ 'tPOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tPOrder'  T }").
Notation TPOrder le lt top mixin :=
  (@pack _ (Phant _) le lt top mixin _ _ id _ id).
Notation "[ 'tPOrder' 'of' le ]" :=
  (@clone _ (Phant _) _ le (nosimpl _) (nosimpl _) _ id)
  (at level 0, format "[ 'tPOrder'  'of'  le ]").
End Exports.

End TPOrder.
Import TPOrder.Exports.

Notation top := TPOrder.top.
Arguments top {T phT} ord : rename, simpl never.

(* ========================================================================== *)

Module TBPOrder.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (bottom top : T) := Class {
  base : BPOrder.class_of le lt bottom;
  mixin : TPOrder.mixin_of le top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  bottom : T;
  top : T;
  class_ : class_of le lt bottom top;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> BPOrder.class_of.
Local Coercion base2 le lt bottom top (c : class_of le lt bottom top) :
  TPOrder.class_of le lt top := TPOrder.Class (base c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (bottom ord) (top ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
(* NB: [nosimpl] is needed to let the [Canonical] command ignore a field.     *)
Definition bP_tPOrder :=
  @TPOrder.Pack _ phT (BPOrder.le bPOrder) (BPOrder.lt bPOrder)
                ((* hack! *) nosimpl (top ord)) class.

Variable (leT ltT : rel T) (bottomT topT : T).

Definition pack :=
  fun (bord : BPOrder.order phT) (b : BPOrder.class_of leT ltT bottomT)
      & phant_id (BPOrder.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class b m) =>
  @Pack phT leT ltT bottomT topT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> BPOrder.class_of.
Coercion base2 : class_of >-> TPOrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Canonical bP_tPOrder.
Notation "{ 'tbPOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tbPOrder'  T }").
Notation "[ 'tbPOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'tbPOrder'  'of'  le ]").
End Exports.

End TBPOrder.
Import TBPOrder.Exports.

(* ========================================================================== *)

Module Meet.
(*TODO : Adapter la structure MeetSemilattice de order.v*)
Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record mixin_of (le : rel T) (meet : T -> T -> T) := Mixin {
  meetC : commutative meet;
  meetA : associative meet;
  leEmeet : forall x y, (le x y) = (meet x y == x);
}.

Record class_of (le lt : rel T) (meet : T -> T -> T) := Class {
  base : POrder.class_of le lt;
  mixin : mixin_of le meet;
}.


Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  class_ : class_of le lt meet;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) :=
  let: Pack _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.

Variable (leT ltT : rel T) (meetT : T -> T -> T).

Definition clone c of phant_id class c := @Pack phT leT ltT meetT c.

Definition pack (m0 : mixin_of leT meetT) :=
  fun (bord : POrder.order phT) b
        & phant_id (POrder.class bord) b =>
  fun m & phant_id m0 m => @Pack phT leT ltT meetT (@Class leT ltT meetT b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Notation "{ 'meetOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'meetOrder'  T }").
Notation MeetOrder le lt meet mixin :=
  (@pack _ (Phant _) le lt meet mixin _ _ id _ id).
Notation "[ 'meetOrder' 'of' le ]" :=
  (@clone _ (Phant _) _ le (nosimpl _) (nosimpl _) _ id)
  (at level 0, format "[ 'meetOrder'  'of'  le ]").
End Exports.

End Meet.
Import Meet.Exports.

Notation meet := Meet.meet.
Arguments meet {T phT} ord x y : rename, simpl never.

(* ========================================================================== *)

Module BMeet.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (meet : T -> T -> T) (bottom : T) := Class {
  base : Meet.class_of le lt meet;
  mixin : BPOrder.mixin_of le bottom;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  bottom : T;
  class_ : class_of le lt meet bottom;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Meet.class_of.
Local Coercion base2 le lt meet bottom (c : class_of le lt meet bottom) :
  BPOrder.class_of le lt bottom := BPOrder.Class (base c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (bottom ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bP_meetOrder :=
  @Meet.Pack
    _ phT (BPOrder.le bPOrder) (BPOrder.lt bPOrder) (nosimpl (meet ord)) class.

Variable (leT ltT : rel T) (meetT : T -> T -> T) (bottomT : T).

Definition pack :=
  fun (bord : Meet.order phT) (b : Meet.class_of leT ltT meetT)
      & phant_id (Meet.class bord) b =>
  fun (mord : BPOrder.order phT) m
      & phant_id (BPOrder.class mord) (BPOrder.Class b m) =>
  @Pack phT leT ltT meetT bottomT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Meet.class_of.
Coercion base2 : class_of >-> BPOrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Canonical bP_meetOrder.
Notation "{ 'bMeetOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'bMeetOrder'  T }").
Notation "[ 'bMeetOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'bMeetOrder'  'of'  le ]").
End Exports.

End BMeet.
Import BMeet.Exports.

(* ========================================================================== *)

Module TMeet.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (meet : T -> T -> T) (top : T) := Class {
  base : Meet.class_of le lt meet;
  mixin : TPOrder.mixin_of le top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  top : T;
  class_ : class_of le lt meet top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Meet.class_of.
Local Coercion base2 le lt meet top (c : class_of le lt meet top) :
  TPOrder.class_of le lt top := TPOrder.Class (base c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (top ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition tP_meetOrder :=
  @Meet.Pack
    _ phT (TPOrder.le tPOrder) (TPOrder.lt tPOrder) (nosimpl (meet ord)) class.

Variable (leT ltT : rel T) (meetT : T -> T -> T) (topT : T).

Definition pack :=
  fun (bord : Meet.order phT) (b : Meet.class_of leT ltT meetT)
      & phant_id (Meet.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class b m) =>
  @Pack phT leT ltT meetT topT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Meet.class_of.
Coercion base2 : class_of >-> TPOrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Canonical tP_meetOrder.
Notation "{ 'tMeetOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tMeetOrder'  T }").
Notation "[ 'tMeetOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'tMeetOrder'  'of'  le ]").
End Exports.

End TMeet.
Import TMeet.Exports.

(* ========================================================================== *)

Module TBMeet.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (meet : T -> T -> T) (bottom top : T) := Class {
  base : BMeet.class_of le lt meet bottom;
  mixin : TPOrder.mixin_of le top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  bottom : T;
  top : T;
  class_ : class_of le lt meet bottom top;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> BMeet.class_of.
Local Coercion base2 le lt meet bottom top
                     (c : class_of le lt meet bottom top) :
  TMeet.class_of le lt meet top := TMeet.Class (base c) (mixin c).
Local Coercion base3 le lt meet bottom top
                     (c : class_of le lt meet bottom top) :
  TBPOrder.class_of le lt bottom top := TBPOrder.Class (base c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (meet ord) (bottom ord) (top ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition tbPOrder :=
  @TBPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) class.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) class.
Definition bP_tMeetOrder :=
  @TMeet.Pack _ phT (BPOrder.le bPOrder) (BPOrder.lt bPOrder)
              (nosimpl (meet ord)) (nosimpl (top ord)) class.
Definition tP_bMeetOrder :=
  @BMeet.Pack _ phT (TPOrder.le tPOrder) (TPOrder.lt tPOrder)
              (nosimpl (meet ord)) (nosimpl (bottom ord)) class.
Definition tbP_meetOrder :=
  @Meet.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
             (nosimpl (meet ord)) class.
Definition tbP_bMeetOrder :=
  @BMeet.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
              (nosimpl (meet ord)) (TBPOrder.bottom tbPOrder) class.
Definition tbP_tMeetOrder :=
  @TMeet.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
              (nosimpl (meet ord)) (TBPOrder.top tbPOrder) class.
Definition bMeet_tMeetOrder :=
  @TMeet.Pack _ phT (BMeet.le bMeetOrder) (BMeet.lt bMeetOrder)
              (BMeet.meet bMeetOrder) (nosimpl (top ord)) class.

Variable (leT ltT : rel T) (meetT : T -> T -> T) (bottomT topT : T).

Definition pack :=
  fun (bord : BMeet.order phT) (b : BMeet.class_of leT ltT meetT bottomT)
      & phant_id (BMeet.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class b m) =>
  @Pack phT leT ltT meetT bottomT topT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> BMeet.class_of.
Coercion base2 : class_of >-> TMeet.class_of.
Coercion base3 : class_of >-> TBPOrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion tbPOrder : order >-> TBPOrder.order.
Canonical tbPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion bMeetOrder : order >-> BMeet.order.
Canonical bMeetOrder.
Coercion tMeetOrder : order >-> TMeet.order.
Canonical tMeetOrder.
Canonical bP_tMeetOrder.
Canonical tP_bMeetOrder.
Canonical tbP_meetOrder.
Canonical tbP_bMeetOrder.
Canonical tbP_tMeetOrder.
Canonical bMeet_tMeetOrder.
Notation "{ 'tbMeetOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tbMeetOrder'  T }").
Notation "[ 'tbMeetOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'tbMeetOrder'  'of'  le ]").
End Exports.

End TBMeet.
Import TBMeet.Exports.

(* ========================================================================== *)

Module Join.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (join : T -> T -> T) := Class {
  base : POrder.class_of le lt;
  mixin : Meet.mixin_of (dual_rel le) join;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  join : T -> T -> T;
  class_ : class_of le lt join;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (join ord) :=
  let: Pack _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.

Variable (leT ltT : rel T) (joinT : T -> T -> T).

Definition clone c of phant_id class c := @Pack phT leT ltT joinT c.

Definition pack (m0 : Meet.mixin_of (dual_rel leT) joinT) :=
  fun (bord : POrder.order phT) b
        & phant_id (POrder.class bord) b =>
  fun m & phant_id m0 m => @Pack phT leT ltT joinT (@Class leT ltT joinT b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Notation "{ 'joinOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'joinOrder'  T }").
Notation JoinOrder le lt join mixin :=
  (@pack _ (Phant _) le lt join mixin _ _ id _ id).
Notation "[ 'joinOrder' 'of' le ]" :=
  (@clone _ (Phant _) _ le (nosimpl _) (nosimpl _) _ id)
  (at level 0, format "[ 'joinOrder'  'of'  le ]").
End Exports.

End Join.
Import Join.Exports.

Notation join := Join.join.
Arguments join {T phT} ord x y : rename, simpl never.

(* ========================================================================== *)

Module BJoin.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (join : T -> T -> T) (bottom : T) := Class {
  base : Join.class_of le lt join;
  mixin : BPOrder.mixin_of le bottom;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  join : T -> T -> T;
  bottom : T;
  class_ : class_of le lt join bottom;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Join.class_of.
Local Coercion base2 le lt join bottom (c : class_of le lt join bottom) :
  BPOrder.class_of le lt bottom := BPOrder.Class (base c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (join ord) (bottom ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bP_joinOrder :=
  @Join.Pack
    _ phT (BPOrder.le bPOrder) (BPOrder.lt bPOrder) (nosimpl (join ord)) class.

Variable (leT ltT : rel T) (joinT : T -> T -> T) (bottomT : T).

Definition pack :=
  fun (bord : Join.order phT) (b : Join.class_of leT ltT joinT)
      & phant_id (Join.class bord) b =>
  fun (mord : BPOrder.order phT) m
      & phant_id (BPOrder.class mord) (BPOrder.Class b m) =>
  @Pack phT leT ltT joinT bottomT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Join.class_of.
Coercion base2 : class_of >-> BPOrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Canonical bP_joinOrder.
Notation "{ 'bJoinOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'bJoinOrder'  T }").
Notation "[ 'bJoinOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'bJoinOrder'  'of'  le ]").
End Exports.

End BJoin.
Import BJoin.Exports.

(* ========================================================================== *)

Module TJoin.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (join : T -> T -> T) (top : T) := Class {
  base : Join.class_of le lt join;
  mixin : TPOrder.mixin_of le top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  join : T -> T -> T;
  top : T;
  class_ : class_of le lt join top;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Join.class_of.
Local Coercion base2 le lt join top (c : class_of le lt join top) :
  TPOrder.class_of le lt top := TPOrder.Class (base c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (join ord) (top ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition tP_joinOrder :=
  @Join.Pack
    _ phT (TPOrder.le tPOrder) (TPOrder.lt tPOrder) (nosimpl (join ord)) class.

Variable (leT ltT : rel T) (joinT : T -> T -> T) (topT : T).

Definition pack :=
  fun (bord : Join.order phT) (b : Join.class_of leT ltT joinT)
      & phant_id (Join.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class b m) =>
  @Pack phT leT ltT joinT topT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Join.class_of.
Coercion base2 : class_of >-> TPOrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Canonical tP_joinOrder.
Notation "{ 'tJoinOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tJoinOrder'  T }").
Notation "[ 'tJoinOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'tJoinOrder'  'of'  le ]").
End Exports.

End TJoin.
Import TJoin.Exports.

(* ========================================================================== *)

Module TBJoin.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (join : T -> T -> T) (bottom top : T) := Class {
  base : BJoin.class_of le lt join bottom;
  mixin : TPOrder.mixin_of le top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  join : T -> T -> T;
  bottom : T;
  top : T;
  class_ : class_of le lt join bottom top;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> BJoin.class_of.
Local Coercion base2 le lt join bottom top
                     (c : class_of le lt join bottom top) :
  TJoin.class_of le lt join top := TJoin.Class (base c) (mixin c).
Local Coercion base3 le lt join bottom top
                     (c : class_of le lt join bottom top) :
  TBPOrder.class_of le lt bottom top := TBPOrder.Class (base c) (mixin c).

Variable (phT : phant T).
Variable (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (join ord) (bottom ord) (top ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition tbPOrder :=
  @TBPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) class.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) class.
Definition bP_tJoinOrder :=
  @TJoin.Pack _ phT (BPOrder.le bPOrder) (BPOrder.lt bPOrder)
              (nosimpl (join ord)) (nosimpl (top ord)) class.
Definition tP_bJoinOrder :=
  @BJoin.Pack _ phT (TPOrder.le tPOrder) (TPOrder.lt tPOrder)
              (nosimpl (join ord)) (nosimpl (bottom ord)) class.
Definition tbP_joinOrder :=
  @Join.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
             (nosimpl (join ord)) class.
Definition tbP_bJoinOrder :=
  @BJoin.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
              (nosimpl (join ord)) (TBPOrder.bottom tbPOrder) class.
Definition tbP_tJoinOrder :=
  @TJoin.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
              (nosimpl (join ord)) (TBPOrder.top tbPOrder) class.
Definition bJoin_tJoinOrder :=
  @TJoin.Pack _ phT (BJoin.le bJoinOrder) (BJoin.lt bJoinOrder)
              (BJoin.join bJoinOrder) (nosimpl (top ord)) class.

Variable (leT ltT : rel T) (joinT : T -> T -> T) (bottomT topT : T).

Definition pack :=
  fun (bord : BJoin.order phT) (b : BJoin.class_of leT ltT joinT bottomT)
      & phant_id (BJoin.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class b m) =>
  @Pack phT leT ltT joinT bottomT topT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> BJoin.class_of.
Coercion base2 : class_of >-> TJoin.class_of.
Coercion base3 : class_of >-> TBPOrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion tbPOrder : order >-> TBPOrder.order.
Canonical tbPOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion bJoinOrder : order >-> BJoin.order.
Canonical bJoinOrder.
Coercion tJoinOrder : order >-> TJoin.order.
Canonical tJoinOrder.
Canonical bP_tJoinOrder.
Canonical tP_bJoinOrder.
Canonical tbP_joinOrder.
Canonical tbP_bJoinOrder.
Canonical tbP_tJoinOrder.
Canonical bJoin_tJoinOrder.
Notation "{ 'tbJoinOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tbJoinOrder'  T }").
Notation "[ 'tbJoinOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'tbJoinOrder'  'of'  le ]").
End Exports.

End TBJoin.
Import TBJoin.Exports.

(* ========================================================================== *)

Module Lattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (meet join : T -> T -> T) := Class {
  base : Meet.class_of le lt meet;
  mixin : Meet.mixin_of (dual_rel le) join;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  class_ : class_of le lt meet join;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Meet.class_of.
Local Coercion base2 le lt meet join (c : class_of le lt meet join) :
  Join.class_of le lt join := Join.Class c (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (join ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition meet_joinOrder :=
  @Join.Pack
    _ phT (Meet.le meetOrder) (Meet.lt meetOrder) (nosimpl (join ord)) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T).

Definition pack :=
  fun (bord : Meet.order phT) (b : Meet.class_of leT ltT meetT)
      & phant_id (Meet.class bord) b =>
  fun (mord : Join.order phT) m
      & phant_id (Join.class mord) (Join.Class b m) =>
  @Pack phT leT ltT meetT joinT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Meet.class_of.
Coercion base2 : class_of >-> Join.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Canonical meet_joinOrder.
Notation "{ 'lattice' T }" := (order (Phant T))
  (at level 0, format "{ 'lattice'  T }").
Notation "[ 'lattice' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'lattice'  'of'  le ]").
End Exports.

End Lattice.
Import Lattice.Exports.

(* ========================================================================== *)

Module BLattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (meet join : T -> T -> T) (bottom : T) :=
  Class {
  base : Lattice.class_of le lt meet join;
  mixin : BPOrder.mixin_of le bottom;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  bottom : T;
  class_ : class_of le lt meet join bottom;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Lattice.class_of.
Local Coercion base2 le lt meet join bottom
                     (c : class_of le lt meet join bottom) :
  BMeet.class_of le lt meet bottom := BMeet.Class (base c) (mixin c).
Local Coercion base3 le lt meet join bottom
                     (c : class_of le lt meet join bottom) :
  BJoin.class_of le lt join bottom := BJoin.Class (base c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (meet ord) (join ord) (bottom ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition meet_bJoinOrder :=
  @BJoin.Pack _ phT (Meet.le meetOrder) (Meet.lt meetOrder)
              (nosimpl (join ord)) (nosimpl (bottom ord)) class.
Definition join_bMeetOrder :=
  @BMeet.Pack _ phT (Join.le joinOrder) (Join.lt joinOrder)
              (nosimpl (meet ord)) (nosimpl (bottom ord)) class.
Definition bMeet_bJoinOrder :=
  @BJoin.Pack _ phT (BMeet.le bMeetOrder) (BMeet.lt bMeetOrder)
              (nosimpl (join ord)) (BMeet.bottom bMeetOrder) class.
Definition lattice_bPOrder :=
  @BPOrder.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
                (nosimpl (bottom ord)) class.
Definition lattice_bMeetOrder :=
  @BMeet.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
              (Lattice.meet lattice) (nosimpl (bottom ord)) class.
Definition lattice_bJoinOrder :=
  @BJoin.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
              (Lattice.join lattice) (nosimpl (bottom ord)) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT : T).

Definition pack :=
  fun (bord : Lattice.order phT) (b : Lattice.class_of leT ltT meetT joinT)
      & phant_id (Lattice.class bord) b =>
  fun (mord : BPOrder.order phT) m
      & phant_id (BPOrder.class mord) (BPOrder.Class b m) =>
  @Pack phT leT ltT meetT joinT bottomT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Lattice.class_of.
Coercion base2 : class_of >-> BMeet.class_of.
Coercion base3 : class_of >-> BJoin.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion bMeetOrder : order >-> BMeet.order.
Canonical bMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion bJoinOrder : order >-> BJoin.order.
Canonical bJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Canonical meet_bJoinOrder.
Canonical join_bMeetOrder.
Canonical bMeet_bJoinOrder.
Canonical lattice_bPOrder.
Canonical lattice_bMeetOrder.
Canonical lattice_bJoinOrder.

Notation "{ 'bLattice' T }" := (order (Phant T))
  (at level 0, format "{ 'bLattice'  T }").
Notation "[ 'bLattice' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'bLattice'  'of'  le ]").
End Exports.

End BLattice.
Import BLattice.Exports.

(* ========================================================================== *)

Module TLattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (meet join : T -> T -> T) (top : T) := Class {
  base : Lattice.class_of le lt meet join;
  mixin : TPOrder.mixin_of le top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  top : T;
  class_ : class_of le lt meet join top;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Lattice.class_of.
Local Coercion base2 le lt meet join top (c : class_of le lt meet join top) :
  TMeet.class_of le lt meet top := TMeet.Class (base c) (mixin c).
Local Coercion base3 le lt meet join top (c : class_of le lt meet join top) :
  TJoin.class_of le lt join top := TJoin.Class (base c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (join ord) (top ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition meet_tJoinOrder :=
  @TJoin.Pack _ phT (Meet.le meetOrder) (Meet.lt meetOrder)
              (nosimpl (join ord)) (nosimpl (top ord)) class.
Definition join_tMeetOrder :=
  @TMeet.Pack _ phT (Join.le joinOrder) (Join.lt joinOrder)
              (nosimpl (meet ord)) (nosimpl (top ord)) class.
Definition tMeet_tJoinOrder :=
  @TJoin.Pack _ phT (TMeet.le tMeetOrder) (TMeet.lt tMeetOrder)
              (nosimpl (join ord)) (TMeet.top tMeetOrder) class.
Definition lattice_tPOrder :=
  @TPOrder.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
                (nosimpl (top ord)) class.
Definition lattice_tMeetOrder :=
  @TMeet.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
              (Lattice.meet lattice) (nosimpl (top ord)) class.
Definition lattice_tJoinOrder :=
  @TJoin.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
              (Lattice.join lattice) (nosimpl (top ord)) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (topT : T).

Definition pack :=
  fun (bord : Lattice.order phT) (b : Lattice.class_of leT ltT meetT joinT)
      & phant_id (Lattice.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class b m) =>
  @Pack phT leT ltT meetT joinT topT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Lattice.class_of.
Coercion base2 : class_of >-> TMeet.class_of.
Coercion base3 : class_of >-> TJoin.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion tMeetOrder : order >-> TMeet.order.
Canonical tMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion tJoinOrder : order >-> TJoin.order.
Canonical tJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Canonical meet_tJoinOrder.
Canonical join_tMeetOrder.
Canonical tMeet_tJoinOrder.
Canonical lattice_tPOrder.
Canonical lattice_tMeetOrder.
Canonical lattice_tJoinOrder.
Notation "{ 'tLattice' T }" := (order (Phant T))
  (at level 0, format "{ 'tLattice'  T }").
Notation "[ 'tLattice' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'tLattice'  'of'  le ]").
End Exports.

End TLattice.
Import TLattice.Exports.

(* ========================================================================== *)

Module TBLattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (meet join : T -> T -> T) (bottom top : T) :=
  Class {
  base : BLattice.class_of le lt meet join bottom;
  mixin : TPOrder.mixin_of le top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  bottom : T;
  top : T;
  class_ : class_of le lt meet join bottom top;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> BLattice.class_of.
Local Coercion base2 le lt meet join bottom top
      (c : class_of le lt meet join bottom top) :
  TLattice.class_of le lt meet join top := TLattice.Class (base c) (mixin c).
Local Coercion base3 le lt meet join bottom top
      (c : class_of le lt meet join bottom top) :
  TBMeet.class_of le lt meet bottom top := TBMeet.Class (base c) (mixin c).
Local Coercion base4 le lt meet join bottom top
      (c : class_of le lt meet join bottom top) :
  TBJoin.class_of le lt join bottom top := TBJoin.Class (base c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (meet ord) (join ord) (bottom ord) (top ord) :=
  let: Pack _ _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition tbPOrder :=
  @TBPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) class.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) class.
Definition tbMeetOrder :=
  @TBMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) class.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) class.
Definition tbJoinOrder :=
  @TBJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) (top ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bLattice :=
  @BLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition tLattice :=
  @TLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.
(* TODO: non-trivial joins are missing below. *)

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT topT : T).

Definition pack :=
  fun (bord : BLattice.order phT)
      (b : BLattice.class_of leT ltT meetT joinT bottomT)
      & phant_id (BLattice.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class b m) =>
  @Pack phT leT ltT meetT joinT bottomT topT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> BLattice.class_of.
Coercion base2 : class_of >-> TLattice.class_of.
Coercion base3 : class_of >-> TBMeet.class_of.
Coercion base4 : class_of >-> TBJoin.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion tbPOrder : order >-> TBPOrder.order.
Canonical tbPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion bMeetOrder : order >-> BMeet.order.
Canonical bMeetOrder.
Coercion tMeetOrder : order >-> TMeet.order.
Canonical tMeetOrder.
Coercion tbMeetOrder : order >-> TBMeet.order.
Canonical tbMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion bJoinOrder : order >-> BJoin.order.
Canonical bJoinOrder.
Coercion tJoinOrder : order >-> TJoin.order.
Canonical tJoinOrder.
Coercion tbJoinOrder : order >-> TBJoin.order.
Canonical tbJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion bLattice : order >-> BLattice.order.
Canonical bLattice.
Coercion tLattice : order >-> TLattice.order.
Canonical tLattice.
Notation "{ 'tbLattice' T }" := (order (Phant T))
  (at level 0, format "{ 'tbLattice'  T }").
Notation "[ 'tbLattice' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'tbLattice'  'of'  le ]").
End Exports.

End TBLattice.
Import TBLattice.Exports.

(* ========================================================================== *)

Module DistrLattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record mixin_of (meet join : T -> T -> T) := Mixin {
  meetUl : left_distributive meet join;
  joinIl : left_distributive join meet;
}.

Record class_of (le lt : rel T) (meet join : T -> T -> T) := Class {
  base : Lattice.class_of le lt meet join;
  mixin : mixin_of meet join;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  class_ : class_of le lt meet join;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Lattice.class_of.

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (join ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T).

Definition clone c of phant_id class c := @Pack phT leT ltT meetT joinT c.

Definition pack (m0 : mixin_of meetT joinT) :=
  fun (bord : Lattice.order phT) b & phant_id (Lattice.class bord) b =>
  fun m & phant_id m0 m =>
  @Pack phT leT ltT meetT joinT (@Class leT ltT meetT joinT b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Lattice.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Notation "{ 'distrLattice' T }" := (order (Phant T))
  (at level 0, format "{ 'distrLattice'  T }").
Notation DistrLattice le lt meet join mixin :=
  (@pack _ (Phant _) le lt meet join mixin _ _ id _ id).
Notation "[ 'distrLattice' 'of' le ]" :=
  (@clone _ (Phant _) _ le (nosimpl _) (nosimpl _) (nosimpl _) _ id)
  (at level 0, format "[ 'distrLattice'  'of'  le ]").
End Exports.

End DistrLattice.
Import DistrLattice.Exports.

(* ========================================================================== *)

Module BDistrLattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (meet join : T -> T -> T) (bottom : T) :=
  Class {
  base : DistrLattice.class_of le lt meet join;
  mixin : BPOrder.mixin_of le bottom;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  bottom : T;
  class_ : class_of le lt meet join bottom;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> DistrLattice.class_of.
Local Coercion base2 le lt meet join bottom
                     (c : class_of le lt meet join bottom) :
  BLattice.class_of le lt meet join bottom := BLattice.Class (base c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (meet ord) (join ord) (bottom ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bLattice :=
  @BLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT : T).

Definition pack :=
  fun (bord : DistrLattice.order phT)
      (b : DistrLattice.class_of leT ltT meetT joinT)
      & phant_id (DistrLattice.class bord) b =>
  fun (mord : BPOrder.order phT) m
      & phant_id (BPOrder.class mord) (BPOrder.Class b m) =>
  @Pack phT leT ltT meetT joinT bottomT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> DistrLattice.class_of.
Coercion base2 : class_of >-> BLattice.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion bMeetOrder : order >-> BMeet.order.
Canonical bMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion bJoinOrder : order >-> BJoin.order.
Canonical bJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion bLattice : order >-> BLattice.order.
Canonical bLattice.
Coercion distrLattice : order >-> DistrLattice.order.
Canonical distrLattice.
Notation "{ 'bDistrLattice' T }" := (order (Phant T))
  (at level 0, format "{ 'bDistrLattice'  T }").
Notation "[ 'bDistrLattice' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'bDistrLattice'  'of'  le ]").
End Exports.

End BDistrLattice.
Import BDistrLattice.Exports.

(* ========================================================================== *)

Module TDistrLattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (meet join : T -> T -> T) (top : T) :=
  Class {
  base : DistrLattice.class_of le lt meet join;
  mixin : TPOrder.mixin_of le top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  top : T;
  class_ : class_of le lt meet join top;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> DistrLattice.class_of.
Local Coercion base2 le lt meet join top (c : class_of le lt meet join top) :
  TLattice.class_of le lt meet join top := TLattice.Class (base c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (join ord) (top ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition tLattice :=
  @TLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (topT : T).

Definition pack :=
  fun (bord : DistrLattice.order phT)
      (b : DistrLattice.class_of leT ltT meetT joinT)
      & phant_id (DistrLattice.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class b m) =>
  @Pack phT leT ltT meetT joinT topT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> DistrLattice.class_of.
Coercion base2 : class_of >-> TLattice.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion tMeetOrder : order >-> TMeet.order.
Canonical tMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion tJoinOrder : order >-> TJoin.order.
Canonical tJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion tLattice : order >-> TLattice.order.
Canonical tLattice.
Coercion distrLattice : order >-> DistrLattice.order.
Canonical distrLattice.
Notation "{ 'tDistrLattice' T }" := (order (Phant T))
  (at level 0, format "{ 'tDistrLattice'  T }").
Notation "[ 'tDistrLattice' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'tDistrLattice'  'of'  le ]").
End Exports.

End TDistrLattice.
Import TDistrLattice.Exports.

(* ========================================================================== *)

Module TBDistrLattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (meet join : T -> T -> T) (bottom top : T) :=
  Class {
  base : BDistrLattice.class_of le lt meet join bottom;
  mixin : TPOrder.mixin_of le top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  bottom : T;
  top : T;
  class_ : class_of le lt meet join bottom top;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> BDistrLattice.class_of.
Local Coercion base2 le lt meet join bottom top
      (c : class_of le lt meet join bottom top) :
  TDistrLattice.class_of le lt meet join top :=
  TDistrLattice.Class (base c) (mixin c).
Local Coercion base3 le lt meet join bottom top
      (c : class_of le lt meet join bottom top) :
  TBLattice.class_of le lt meet join bottom top :=
  TBLattice.Class (base c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (meet ord) (join ord) (bottom ord) (top ord) :=
  let: Pack _ _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition tbPOrder :=
  @TBPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) class.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) class.
Definition tbMeetOrder :=
  @TBMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) class.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) class.
Definition tbJoinOrder :=
  @TBJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) (top ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bLattice :=
  @BLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition tLattice :=
  @TLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.
Definition tbLattice :=
  @TBLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) (top ord) class.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bDistrLattice :=
  @BDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition tDistrLattice :=
  @TDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT topT : T).

Definition pack :=
  fun (bord : BDistrLattice.order phT)
      (b : BDistrLattice.class_of leT ltT meetT joinT bottomT)
      & phant_id (BDistrLattice.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class b m) =>
  @Pack phT leT ltT meetT joinT bottomT topT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> BDistrLattice.class_of.
Coercion base2 : class_of >-> TDistrLattice.class_of.
Coercion base3 : class_of >-> TBLattice.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion tbPOrder : order >-> TBPOrder.order.
Canonical tbPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion bMeetOrder : order >-> BMeet.order.
Canonical bMeetOrder.
Coercion tMeetOrder : order >-> TMeet.order.
Canonical tMeetOrder.
Coercion tbMeetOrder : order >-> TBMeet.order.
Canonical tbMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion bJoinOrder : order >-> BJoin.order.
Canonical bJoinOrder.
Coercion tJoinOrder : order >-> TJoin.order.
Canonical tJoinOrder.
Coercion tbJoinOrder : order >-> TBJoin.order.
Canonical tbJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion bLattice : order >-> BLattice.order.
Canonical bLattice.
Coercion tLattice : order >-> TLattice.order.
Canonical tLattice.
Coercion tbLattice : order >-> TBLattice.order.
Canonical tbLattice.
Coercion distrLattice : order >-> DistrLattice.order.
Canonical distrLattice.
Coercion bDistrLattice : order >-> BDistrLattice.order.
Canonical bDistrLattice.
Coercion tDistrLattice : order >-> TDistrLattice.order.
Canonical tDistrLattice.
Notation "{ 'tbDistrLattice' T }" := (order (Phant T))
  (at level 0, format "{ 'tbDistrLattice'  T }").
Notation "[ 'tbDistrLattice' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'tbDistrLattice'  'of' le ]").
End Exports.

End TBDistrLattice.
Import TBDistrLattice.Exports.

(* ========================================================================== *)

Module Total.

Section ClassDef.

Variable T : eqType.

Definition mixin_of (le : rel T) := total le.

Set Primitive Projections.
Record class_of (le lt : rel T) (meet join : T -> T -> T) := Class {
  base : DistrLattice.class_of le lt meet join;
  mixin : mixin_of le;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  class_ : class_of le lt meet join;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> DistrLattice.class_of.

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (join ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T).

Definition clone c of phant_id class c := @Pack phT leT ltT meetT joinT c.

Definition pack (m0 : mixin_of leT) :=
  fun (bord : DistrLattice.order phT) b
        & phant_id (DistrLattice.class bord) b =>
  fun m & phant_id m0 m =>
  @Pack phT leT ltT meetT joinT (@Class leT ltT meetT joinT b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> DistrLattice.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion distrLattice : order >-> DistrLattice.order.
Canonical distrLattice.
Notation "{ 'totalOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'totalOrder'  T }").
Notation TotalOrder le lt meet join mixin :=
  (@pack _ (Phant _) le lt meet join mixin _ _ id _ id).
Notation "[ 'totalOrder' 'of' le ]" :=
  (@clone _ (Phant _) _ le (nosimpl _) (nosimpl _) (nosimpl _) _ id)
  (at level 0, format "[ 'totalOrder'  'of'  le ]").
End Exports.

End Total.
Import Total.Exports.

(* ========================================================================== *)

Module BTotal.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (meet join : T -> T -> T) (bottom : T) :=
  Class {
  base : Total.class_of le lt meet join;
  mixin : BPOrder.mixin_of le bottom;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  bottom : T;
  class_ : class_of le lt meet join bottom;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Total.class_of.
Local Coercion base2 le lt meet join bottom
                     (c : class_of le lt meet join bottom) :
  BDistrLattice.class_of le lt meet join bottom :=
  BDistrLattice.Class (base c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (meet ord) (join ord) (bottom ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bLattice :=
  @BLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bDistrLattice :=
  @BDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition totalOrder :=
  @Total.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT : T).

Definition pack :=
  fun (bord : Total.order phT) (b : Total.class_of leT ltT meetT joinT)
      & phant_id (Total.class bord) b =>
  fun (mord : BPOrder.order phT) m
      & phant_id (BPOrder.class mord) (BPOrder.Class b m) =>
  @Pack phT leT ltT meetT joinT bottomT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Total.class_of.
Coercion base2 : class_of >-> BDistrLattice.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion bMeetOrder : order >-> BMeet.order.
Canonical bMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion bJoinOrder : order >-> BJoin.order.
Canonical bJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion bLattice : order >-> BLattice.order.
Canonical bLattice.
Coercion distrLattice : order >-> DistrLattice.order.
Canonical distrLattice.
Coercion bDistrLattice : order >-> BDistrLattice.order.
Canonical bDistrLattice.
Coercion totalOrder : order >-> Total.order.
Canonical totalOrder.
Notation "{ 'bTotalOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'bTotalOrder'  T }").
Notation "[ 'bTotalOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'bTotalOrder'  'of'  le ]").
End Exports.

End BTotal.
Import BTotal.Exports.

(* ========================================================================== *)

Module TTotal.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (meet join : T -> T -> T) (top : T) :=
  Class {
  base : Total.class_of le lt meet join;
  mixin : TPOrder.mixin_of le top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  top : T;
  class_ : class_of le lt meet join top;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Total.class_of.
Local Coercion base2 le lt meet join top (c : class_of le lt meet join top) :
  TDistrLattice.class_of le lt meet join top :=
  TDistrLattice.Class (base c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (join ord) (top ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition tLattice :=
  @TLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition tDistrLattice :=
  @TDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.
Definition totalOrder :=
  @Total.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (topT : T).

Definition pack :=
  fun (bord : Total.order phT) (b : Total.class_of leT ltT meetT joinT)
      & phant_id (Total.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class b m) =>
  @Pack phT leT ltT meetT joinT topT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Total.class_of.
Coercion base2 : class_of >-> TDistrLattice.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion tMeetOrder : order >-> TMeet.order.
Canonical tMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion tJoinOrder : order >-> TJoin.order.
Canonical tJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion tLattice : order >-> TLattice.order.
Canonical tLattice.
Coercion distrLattice : order >-> DistrLattice.order.
Canonical distrLattice.
Coercion tDistrLattice : order >-> TDistrLattice.order.
Canonical tDistrLattice.
Coercion totalOrder : order >-> Total.order.
Canonical totalOrder.
Notation "{ 'tTotalOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tTotalOrder'  T }").
Notation "[ 'tTotalOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'tTotalOrder'  'of'  le ]").
End Exports.

End TTotal.
Import TTotal.Exports.

(* ========================================================================== *)

Module TBTotal.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.
Record class_of (le lt : rel T) (meet join : T -> T -> T) (bottom top : T) :=
  Class {
  base : BTotal.class_of le lt meet join bottom;
  mixin : TPOrder.mixin_of le top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  bottom : T;
  top : T;
  class_ : class_of le lt meet join bottom top;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> BTotal.class_of.
Local Coercion base2 le lt meet join bottom top
      (c : class_of le lt meet join bottom top) :
  TTotal.class_of le lt meet join top := TTotal.Class (base c) (mixin c).
Local Coercion base3 le lt meet join bottom top
      (c : class_of le lt meet join bottom top) :
  TBDistrLattice.class_of le lt meet join bottom top :=
  TBDistrLattice.Class (base c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (meet ord) (join ord) (bottom ord) (top ord) :=
  let: Pack _ _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition tbPOrder :=
  @TBPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) class.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) class.
Definition tbMeetOrder :=
  @TBMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) class.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) class.
Definition tbJoinOrder :=
  @TBJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) (top ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bLattice :=
  @BLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition tLattice :=
  @TLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.
Definition tbLattice :=
  @TBLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) (top ord) class.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bDistrLattice :=
  @BDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition tDistrLattice :=
  @TDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.
Definition tbDistrLattice :=
  @TBDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) (top ord) class.
Definition totalOrder :=
  @Total.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bTotalOrder :=
  @BTotal.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition tTotalOrder :=
  @TTotal.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT topT : T).

Definition pack :=
  fun (bord : BTotal.order phT)
      (b : BTotal.class_of leT ltT meetT joinT bottomT)
      & phant_id (BTotal.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class b m) =>
  @Pack phT leT ltT meetT joinT bottomT topT (Class b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> BTotal.class_of.
Coercion base2 : class_of >-> TTotal.class_of.
Coercion base3 : class_of >-> TBDistrLattice.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion tbPOrder : order >-> TBPOrder.order.
Canonical tbPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion bMeetOrder : order >-> BMeet.order.
Canonical bMeetOrder.
Coercion tMeetOrder : order >-> TMeet.order.
Canonical tMeetOrder.
Coercion tbMeetOrder : order >-> TBMeet.order.
Canonical tbMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion bJoinOrder : order >-> BJoin.order.
Canonical bJoinOrder.
Coercion tJoinOrder : order >-> TJoin.order.
Canonical tJoinOrder.
Coercion tbJoinOrder : order >-> TBJoin.order.
Canonical tbJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion bLattice : order >-> BLattice.order.
Canonical bLattice.
Coercion tLattice : order >-> TLattice.order.
Canonical tLattice.
Coercion tbLattice : order >-> TBLattice.order.
Canonical tbLattice.
Coercion distrLattice : order >-> DistrLattice.order.
Canonical distrLattice.
Coercion bDistrLattice : order >-> BDistrLattice.order.
Canonical bDistrLattice.
Coercion tDistrLattice : order >-> TDistrLattice.order.
Canonical tDistrLattice.
Coercion tbDistrLattice : order >-> TBDistrLattice.order.
Canonical tbDistrLattice.
Coercion totalOrder : order >-> Total.order.
Canonical totalOrder.
Coercion bTotalOrder : order >-> BTotal.order.
Canonical bTotalOrder.
Coercion tTotalOrder : order >-> TTotal.order.
Canonical tTotalOrder.
Notation "{ 'tbTotalOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tbTotalOrder'  T }").
Notation "[ 'tbTotalOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'tbTotalOrder'  'of'  le ]").
End Exports.

End TBTotal.
Import TBTotal.Exports.

(* ========================================================================== *)

Section POrderDef.

Context {T: eqType} (ord : {pOrder T}).
Implicit Types (x y z : T).

Local Notation le := (le ord).
Local Notation lt := (lt ord).
Local Notation "x <= y" := (le x y).
Local Notation "x < y" := (lt x y).

Definition comparable : rel T := fun x y => (x <= y) || (y <= x).

Local Notation "x >< y" := (~~ (comparable x y)).

Definition ge : simpl_rel T := [rel x y | y <= x].
Definition gt : simpl_rel T := [rel x y | y < x].

Definition leif x y C : Prop := ((x <= y) * ((x == y) = C))%type.

Definition le_of_leif x y C (le_xy : leif x y C) : x <= y := le_xy.1.

Definition lteif x y C := if C then x <= y else x < y.

Definition min x y := if x < y then x else y.
Definition max x y := if x < y then y else x.

Variant le_xor_gt x y : T -> T -> T -> T -> bool -> bool -> Set :=
  | LeNotGt of x <= y : le_xor_gt x y x x y y true false
  | GtNotLe of y < x  : le_xor_gt x y y y x x false true.

Variant lt_xor_ge x y : T -> T -> T -> T -> bool -> bool -> Set :=
  | LtNotGe of x < y  : lt_xor_ge x y x x y y false true
  | GeNotLt of y <= x : lt_xor_ge x y y y x x true false.

Variant compare x y :
  T -> T -> T -> T -> bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | CompareLt of x < y : compare x y x x y y false false false true false true
  | CompareGt of y < x : compare x y y y x x false false true false true false
  | CompareEq of x = y : compare x y x x x x true true true true false false.

Variant incompare x y :
  T -> T -> T -> T ->
  bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | InCompareLt of x < y :
    incompare x y x x y y false false false true false true true true
  | InCompareGt of y < x :
    incompare x y y y x x false false true false true false true true
  | InCompare of x >< y  :
    incompare x y x y y x false false false false false false false false
  | InCompareEq of x = y :
    incompare x y x x x x true true true true false false true true.

Definition arg_min {I : finType} := @extremum T I le.
Definition arg_max {I : finType} := @extremum T I ge.

End POrderDef.

Section LatticeDef.

Context {T: eqType} (ord : {lattice T}).
Implicit Types (x y : T).

Local Notation "x <= y" := (le ord x y).
Local Notation "x < y" := (lt ord x y).
Local Notation "x >< y" := (~~ (comparable ord x y)).
Local Notation "x `&` y" := (meet ord x y).
Local Notation "x `|` y" := (join ord x y).

Variant lel_xor_gt x y :
  T -> T -> T -> T -> T -> T -> T -> T -> bool -> bool -> Set :=
  | LelNotGt of x <= y : lel_xor_gt x y x x y y x x y y true false
  | GtlNotLe of y < x  : lel_xor_gt x y y y x x y y x x false true.

Variant ltl_xor_ge x y :
  T -> T -> T -> T -> T -> T -> T -> T -> bool -> bool -> Set :=
  | LtlNotGe of x < y  : ltl_xor_ge x y x x y y x x y y false true
  | GelNotLt of y <= x : ltl_xor_ge x y y y x x y y x x true false.

Variant comparel x y :
   T -> T -> T -> T -> T -> T -> T -> T ->
   bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparelLt of x < y : comparel x y
    x x y y x x y y false false false true false true
  | ComparelGt of y < x : comparel x y
    y y x x y y x x false false true false true false
  | ComparelEq of x = y : comparel x y
    x x x x x x x x true true true true false false.

Variant incomparel x y :
  T -> T -> T -> T -> T -> T -> T -> T ->
  bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | InComparelLt of x < y : incomparel x y
    x x y y x x y y false false false true false true true true
  | InComparelGt of y < x : incomparel x y
    y y x x y y x x false false true false true false true true
  | InComparel of x >< y  : incomparel x y
    x y y x (y `&` x) (x `&` y) (y `|` x) (x `|` y)
    false false false false false false false false
  | InComparelEq of x = y : incomparel x y
    x x x x x x x x true true true true false false true true.

End LatticeDef.

(* TODO: Reserved Notation *)

Notation "<=: r" := (le r) (at level 2, r at level 1, format "<=: r").
Notation "<: r" := (lt r) (at level 2, r at level 1, format "<: r").
Notation "x <=_ r y" :=
  (<=: r x y) (at level 65, r at level 2, format "x  <=_ r  y").
Notation "x >=_ r y" := (y <=_r x) (at level 65, r at level 2, only parsing).
Notation "x <_ r y" :=
  (<: r x y) (at level 65, r at level 2, format "x  <_ r  y").
Notation "x >_ r y" := (y <_r x) (at level 65, r at level 2, only parsing).
Notation "x <=_ r0 y <=_ r1 z" := ((x <=_r0 y) && (y <=_r1 z))
  (at level 70, r0 at level 2, r1 at level 2, format "x  <=_ r0  y  <=_ r1  z").
Notation "x <_ r0 y <_ r1 z" := ((x <_r0 y) && (y <_r1 z))
  (at level 70, r0 at level 2, r1 at level 2, format "x  <_ r0  y  <_ r1  z").
Notation "x <=_ r0 y <_ r1 z" := ((x <=_r0 y) && (y <_r1 z))
  (at level 70, r0 at level 2, r1 at level 2, format "x  <=_ r0  y  <_ r1  z").
Notation "x <_ r0 y <=_ r1 z" := ((x <_r0 y) && (y <=_r1 z))
  (at level 70, r0 at level 2, r1 at level 2, format "x  <_ r0  y  <=_ r1  z").
Notation "x >=<_ r y" := (comparable r x y)
  (at level 70, r at level 2, no associativity, format "x  >=<_ r  y").
Notation "x ><_ r y" := (~~ comparable r x y)
  (at level 70, r at level 2, no associativity, format "x  ><_ r  y").
Notation ">=<_ r y" :=
  [pred x | x >=<_r y] (at level 80, r at level 2, format ">=<_ r  y").
Notation "><_ r y" :=
  [pred x | x ><_r y] (at level 80, r at level 2, format "><_ r  y").

Notation "x <=_ r y ?= 'iff' C" := (leif r x y C)
  (at level 70, C at level 1, r at level 2,
   format "x '[hv'  <=_ r '/'  y  ?=  'iff'  C ']'").

Notation "x <_ r y ?<= 'if' C" := (lteif r x y C)
  (at level 71, C at level 1, r at level 1, y at next level,
   format "x '[hv'  <_ r '/'  y  ?<=  'if'  C ']'").

(* ========================================================================== *)

Section DualOrder.

Variable T : eqType.

Canonical dual_pOrder (ord : {pOrder T}) :=
  POrder
    (dual_rel <=:ord) (dual_rel <:ord)
    (let mixin := POrder.class ord in
     @POrder.Mixin
       T (dual_rel <=:ord) (dual_rel <:ord) (POrder.lexx mixin)
       (fun x y yx xy => POrder.le_anti mixin xy yx)
       (fun y x z xy yz => POrder.le_trans mixin yz xy)
       (POrder.dlt_def mixin) (POrder.lt_def mixin)).

Canonical dual_bPOrder (ord : {tPOrder T}) :=
  BPOrder (dual_rel <=:ord) (dual_rel <:ord) (dual_bottom (top ord))
          (TPOrder.mixin (TPOrder.class ord)).

Canonical dual_tPOrder (ord : {bPOrder T}) :=
  TPOrder (dual_rel <=:ord) (dual_rel <:ord) (dual_top (bottom ord))
          (BPOrder.mixin (BPOrder.class ord)).

(* BUG, TODO: can we design better packagers to infer head symbols of         *)
(* operators from existing instances, or should operators other than [le] be  *)
(* specified (e.g., TBOrder le lt bottom top) to synthesize proper            *)
(* unification hints anyway? Clone notations have the same issue.             *)
Canonical dual_tbPOrder (ord : {tbPOrder T}) := [tbPOrder of dual_rel <=:ord].

Canonical dual_meetOrder (ord : {joinOrder T}) :=
  MeetOrder (dual_rel <=:ord) (dual_rel <:ord) (dual_meet (join ord))
            (Join.mixin (Join.class ord)).

Canonical dual_bMeetOrder (ord : {tJoinOrder T}) :=
  [bMeetOrder of dual_rel <=:ord].

Canonical dual_tMeetOrder (ord : {bJoinOrder T}) :=
  [tMeetOrder of dual_rel <=:ord].

Canonical dual_tbMeetOrder (ord : {tbJoinOrder T}) :=
  [tbMeetOrder of dual_rel <=:ord].

Canonical dual_joinOrder (ord : {meetOrder T}) :=
  JoinOrder (dual_rel <=:ord) (dual_rel <:ord) (dual_meet (meet ord))
            (Meet.mixin (Meet.class ord)).

Canonical dual_bJoinOrder (ord : {tMeetOrder T}) :=
  [bJoinOrder of dual_rel <=:ord].

Canonical dual_tJoinOrder (ord : {bMeetOrder T}) :=
  [tJoinOrder of dual_rel <=:ord].

Canonical dual_tbJoinOrder (ord : {tbMeetOrder T}) :=
  [tbJoinOrder of dual_rel <=:ord].

Canonical dual_lattice (ord : {lattice T}) := [lattice of dual_rel <=:ord].

Canonical dual_bLattice (ord : {tLattice T}) := [bLattice of dual_rel <=:ord].

Canonical dual_tLattice (ord : {bLattice T}) := [tLattice of dual_rel <=:ord].

Canonical dual_tbLattice (ord : {tbLattice T}) :=
  [tbLattice of dual_rel <=:ord].

Canonical dual_distrLattice (ord : {distrLattice T}) :=
  DistrLattice
    (dual_rel <=:ord) (dual_rel <:ord)
    (dual_meet (join ord)) (dual_join (meet ord))
    (let mixin := DistrLattice.mixin (DistrLattice.class ord) in
     DistrLattice.Mixin
       (DistrLattice.joinIl mixin) (DistrLattice.meetUl mixin)).

Canonical dual_bDistrLattice (ord : {tDistrLattice T}) :=
  [bDistrLattice of dual_rel <=:ord].

Canonical dual_tDistrLattice (ord : {bDistrLattice T}) :=
  [tDistrLattice of dual_rel <=:ord].

Canonical dual_tbDistrLattice (ord : {tbDistrLattice T}) :=
  [tbDistrLattice of dual_rel <=:ord].

Canonical dual_totalOrder (ord : {totalOrder T}) :=
  TotalOrder
    (dual_rel <=:ord) (dual_rel <:ord)
    (dual_meet (join ord)) (dual_join (meet ord))
    (fun x y => Total.mixin (Total.class ord) y x).

Canonical dual_bTotalOrder (ord : {tTotalOrder T}) :=
  [bTotalOrder of dual_rel <=:ord].

Canonical dual_tTotalOrder (ord : {bTotalOrder T}) :=
  [tTotalOrder of dual_rel <=:ord].

Canonical dual_tbTotalOrder (ord : {tbTotalOrder T}) :=
  [tbTotalOrder of dual_rel <=:ord].

End DualOrder.

Notation "ord ^~" := (dual_pOrder ord) (at level 8, format "ord ^~").

Parameter (r : {pOrder nat}).

(*
Set Primitive Projections.
Record R := mkR { x : nat; y : nat; _ : x = y; }.
Unset Primitive Projections.

Parameter z : R.

Goal z = let: mkR x y p := z in mkR p.
Proof.
done.

Goal r = let: POrder.Pack le lt mixin := r in POrder.Pack _ mixin.
Proof.
*)

Goal r = (r^~)^~.
Proof.
reflexivity.
Qed.

(* ========================================================================== *)

Module Import POrderTheory.
Section POrderTheory.
Context {T : eqType} {ord : {pOrder T}}.
Implicit Types (x y : T) (s : seq T).

Local Notation le := (le ord).
Local Notation lt := (lt ord).
Local Notation ge := (ge ord).
Local Notation gt := (gt ord).
Local Notation leif := (leif ord).
Local Notation lteif := (lteif ord).
Local Notation min := (min ord).
Local Notation max := (max ord).
Local Notation le_xor_gt := (le_xor_gt ord).
Local Notation lt_xor_ge := (lt_xor_ge ord).
Local Notation compare := (compare ord).
Local Notation incompare := (incompare ord).
Local Notation arg_min := (arg_min ord).
Local Notation arg_max := (arg_max ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x < y" := (x <_ord y).
Local Notation "x >= y" := (x >=_ord y) (only parsing).
Local Notation "x > y" := (x >_ord y) (only parsing).
Local Notation "x <= y <= z" := ((x <= y) && (y <= z)).
Local Notation "x < y < z"   := ((x < y) && (y < z)).
Local Notation "x < y <= z"  := ((x < y) && (y <= z)).
Local Notation "x <= y < z"  := ((x <= y) && (y < z)).

Local Notation ">=<%O" := (comparable ord).
Local Notation ">=< y" := (>=<_ord y).
Local Notation "x >=< y" := (x >=<_ord y).
Local Notation "x >< y" := (x ><_ord y).

Local Notation "x <= y ?= 'iff' C" := (leif x y C).
Local Notation "x < y ?<= 'if' C" := (lteif x y C).

Lemma geE x y : ge x y = (y <= x). Proof. by []. Qed.
Lemma gtE x y : gt x y = (y < x). Proof. by []. Qed.

Lemma lexx : reflexive le.
Proof. by case: ord => ? ? []. Qed.
Hint Resolve lexx : core.

Definition le_refl : reflexive le := lexx.
Definition ge_refl : reflexive ge := lexx.

Lemma le_anti : antisymmetric le.
Proof. by case: ord => le lt [] ? ha ? ? ? x y /andP []; exact: ha. Qed.

Lemma ge_anti : antisymmetric ge.
Proof. by move=> x y /le_anti. Qed.

Lemma le_trans : transitive le.
Proof. by case: ord => ? ? []. Qed.

Lemma ge_trans : transitive ge.
Proof. by move=> ? ? ? ? /le_trans; apply. Qed.

Lemma lt_def x y : (x < y) = (x != y) && (x <= y).
Proof. by case: ord => ? ? []. Qed.

Lemma lt_neqAle x y : (x < y) = (x != y) && (x <= y).
Proof. by case: ord => ? ? []. Qed.

Lemma ltxx x : x < x = false.
Proof. by rewrite lt_def eqxx. Qed.

Definition lt_irreflexive : irreflexive lt := ltxx.
Hint Resolve lt_irreflexive : core.

Definition ltexx := (lexx, ltxx).

Lemma le_eqVlt x y : (x <= y) = (x == y) || (x < y).
Proof. by rewrite lt_neqAle; case: eqP => //= ->; rewrite lexx. Qed.

Lemma lt_eqF x y : x < y -> x == y = false.
Proof. by rewrite lt_neqAle => /andP [/negbTE->]. Qed.

Lemma gt_eqF x y : y < x -> x == y = false.
Proof. by apply: contraTF => /eqP ->; rewrite ltxx. Qed.

Lemma eq_le x y : (x == y) = (x <= y <= x).
Proof. by apply/eqP/idP => [->|/le_anti]; rewrite ?lexx. Qed.

Lemma ltW x y : x < y -> x <= y.
Proof. by rewrite le_eqVlt orbC => ->. Qed.

Lemma lt_le_trans y x z : x < y -> y <= z -> x < z.
Proof.
rewrite !lt_neqAle => /andP [nexy lexy leyz]; rewrite (le_trans lexy) // andbT.
by apply: contraNneq nexy => eqxz; rewrite eqxz eq_le leyz andbT in lexy *.
Qed.

Lemma lt_trans : transitive lt.
Proof. by move=> y x z le1 /ltW le2; apply/(@lt_le_trans y). Qed.

Lemma le_lt_trans y x z : x <= y -> y < z -> x < z.
Proof. by rewrite le_eqVlt => /orP [/eqP ->|/lt_trans t /t]. Qed.

Lemma lt_nsym x y : x < y -> y < x -> False.
Proof. by move=> xy /(lt_trans xy); rewrite ltxx. Qed.

Lemma lt_asym x y : x < y < x = false.
Proof. by apply/negP => /andP []; apply: lt_nsym. Qed.

Lemma le_gtF x y : x <= y -> y < x = false.
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
by rewrite lt_neqAle lexy andbT; apply: contraNneq Nleyx => ->.
Qed.

Lemma lt_le_asym x y : x < y <= x = false.
Proof. by rewrite lt_neqAle -andbA -eq_le eq_sym andNb. Qed.

Lemma le_lt_asym x y : x <= y < x = false.
Proof. by rewrite andbC lt_le_asym. Qed.

Definition lte_anti := (=^~ eq_le, lt_asym, lt_le_asym, le_lt_asym).

Lemma lt_sorted_uniq_le s : sorted lt s = uniq s && sorted le s.
Proof.
case: s => //= n s; elim: s n => //= m s IHs n.
rewrite inE lt_neqAle negb_or IHs -!andbA.
case sn: (n \in s); last do !bool_congr.
rewrite andbF; apply/and5P=> [[ne_nm lenm _ _ le_ms]]; case/negP: ne_nm.
by rewrite eq_le lenm /=; apply: (allP (order_path_min le_trans le_ms)).
Qed.

Lemma lt_sorted_eq s1 s2 : sorted lt s1 -> sorted lt s2 -> s1 =i s2 -> s1 = s2.
Proof. by apply: irr_sorted_eq => //; apply: lt_trans. Qed.

Lemma le_sorted_eq s1 s2 :
  sorted le s1 -> sorted le s2 -> perm_eq s1 s2 -> s1 = s2.
Proof. exact/sorted_eq/le_anti/le_trans. Qed.

Lemma sort_le_id s : sorted le s -> sort le s = s.
Proof. exact/sorted_sort/le_trans. Qed.

Lemma comparable_leNgt x y : x >=< y -> (x <= y) = ~~ (y < x).
Proof.
move=> c_xy; apply/idP/idP => [/le_gtF/negP/negP//|]; rewrite lt_neqAle.
by move: c_xy => /orP [] -> //; rewrite andbT negbK => /eqP ->.
Qed.

Lemma comparable_ltNge x y : x >=< y -> (x < y) = ~~ (y <= x).
Proof.
move=> c_xy; apply/idP/idP => [/lt_geF/negP/negP//|].
by rewrite lt_neqAle eq_le; move: c_xy => /orP [] -> //; rewrite andbT.
Qed.

Lemma comparable_ltgtP x y : x >=< y ->
  compare x y (min y x) (min x y) (max y x) (max x y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof.
rewrite /min /max /comparable !le_eqVlt [y == x]eq_sym.
have := (eqVneq x y, (boolP (x < y), boolP (y < x))).
move=> [[->//|neq_xy /=] [[] xy [] //=]] ; do ?by rewrite ?ltxx; constructor.
  by rewrite ltxx in xy.
by rewrite le_gtF // ltW.
Qed.

Lemma comparable_leP x y : x >=< y ->
  le_xor_gt x y (min y x) (min x y) (max y x) (max x y) (x <= y) (y < x).
Proof. by case/comparable_ltgtP=> [?|?|->]; constructor; rewrite // ltW. Qed.

Lemma comparable_ltP x y : x >=< y ->
  lt_xor_ge x y (min y x) (min x y) (max y x) (max x y) (y <= x) (x < y).
Proof. by case/comparable_ltgtP=> [?|?|->]; constructor; rewrite // ltW. Qed.

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
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y) (y >=< x) (x >=< y).
Proof.
rewrite ![y >=< _]comparable_sym; have [c_xy|i_xy] := boolP (x >=< y).
  by case: (comparable_ltgtP c_xy) => ?; constructor.
by rewrite /min /max ?incomparable_eqF ?incomparable_leF;
   rewrite ?incomparable_ltF// 1?comparable_sym //; constructor.
Qed.

Lemma le_comparable (x y : T) : x <= y -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma lt_comparable (x y : T) : x < y -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma ge_comparable (x y : T) : y <= x -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma gt_comparable (x y : T) : y < x -> x >=< y.
Proof. by case: comparableP. Qed.

(* leif *)

Lemma leifP x y C : reflect (x <= y ?= iff C) (if C then x == y else x < y).
Proof.
rewrite /leif le_eqVlt; apply: (iffP idP)=> [|[]].
  by case: C => [/eqP->|lxy]; rewrite ?eqxx // lxy lt_eqF.
by case/orP=> [/eqP->|lxy] <-; rewrite ?eqxx // lt_eqF.
Qed.

Lemma leif_refl x C : reflect (x <= x ?= iff C) C.
Proof. by apply: (iffP idP) => [-> | <-] //; split; rewrite ?eqxx. Qed.

Lemma leif_trans x1 x2 x3 C12 C23 :
  x1 <= x2 ?= iff C12 -> x2 <= x3 ?= iff C23 -> x1 <= x3 ?= iff C12 && C23.
Proof.
move=> ltx12 ltx23; apply/leifP; rewrite -ltx12.
case eqx12: (x1 == x2).
  by rewrite (eqP eqx12) lt_neqAle !ltx23 andbT; case C23.
by rewrite (@lt_le_trans x2) ?ltx23 // lt_neqAle eqx12 ltx12.
Qed.

Lemma leif_le x y : x <= y -> x <= y ?= iff (x >= y).
Proof. by move=> lexy; split=> //; rewrite eq_le lexy. Qed.

Lemma leif_eq x y : x <= y -> x <= y ?= iff (x == y).
Proof. by []. Qed.

Lemma ge_leif x y C : x <= y ?= iff C -> (y <= x) = C.
Proof. by case=> le_xy; rewrite eq_le le_xy. Qed.

Lemma lt_leif x y C : x <= y ?= iff C -> (x < y) = ~~ C.
Proof. by move=> le_xy; rewrite lt_neqAle !le_xy andbT. Qed.

Lemma ltNleif x y C : x <= y ?= iff ~~ C -> (x < y) = C.
Proof. by move/lt_leif; rewrite negbK. Qed.

Lemma eq_leif x y C : x <= y ?= iff C -> (x == y) = C.
Proof. by move/leifP; case: C comparableP => [] []. Qed.

Lemma eqTleif x y C : x <= y ?= iff C -> C -> x = y.
Proof. by move=> /eq_leif<-/eqP. Qed.

(* lteif *)

Lemma lteif_trans x y z C1 C2 :
  x < y ?<= if C1 -> y < z ?<= if C2 -> x < z ?<= if C1 && C2.
Proof.
case: C1 C2 => [][];
  [exact: le_trans | exact: le_lt_trans | exact: lt_le_trans | exact: lt_trans].
Qed.

Lemma lteif_anti C1 C2 x y :
  (x < y ?<= if C1) && (y < x ?<= if C2) = C1 && C2 && (x == y).
Proof. by case: C1 C2 => [][]; rewrite lte_anti. Qed.

Lemma lteifxx x C : (x < x ?<= if C) = C.
Proof. by case: C; rewrite /= ltexx. Qed.

Lemma lteifNF x y C : y < x ?<= if ~~ C -> x < y ?<= if C = false.
Proof. by case: C => [/lt_geF|/le_gtF]. Qed.

Lemma lteifS x y C : x < y -> x < y ?<= if C.
Proof. by case: C => //= /ltW. Qed.

Lemma lteifT x y : x < y ?<= if true = (x <= y). Proof. by []. Qed.

Lemma lteifF x y : x < y ?<= if false = (x < y). Proof. by []. Qed.

Lemma lteif_orb x y : {morph lteif x y : p q / p || q}.
Proof. by case=> [][] /=; case: comparableP. Qed.

Lemma lteif_andb x y : {morph lteif x y : p q / p && q}.
Proof. by case=> [][] /=; case: comparableP. Qed.

Lemma lteif_imply C1 C2 x y : C1 ==> C2 -> x < y ?<= if C1 -> x < y ?<= if C2.
Proof. by case: C1 C2 => [][] //= _ /ltW. Qed.

Lemma lteifW C x y : x < y ?<= if C -> x <= y.
Proof. by case: C => // /ltW. Qed.

Lemma ltrW_lteif C x y : x < y -> x < y ?<= if C.
Proof. by case: C => // /ltW. Qed.

Lemma lteifN C x y : x < y ?<= if ~~ C -> ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: comparableP. Qed.

(* min and max *)

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

Lemma comparable_minr z : {in >=<%O z &, forall x y, z >=< min x y}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /min; case: ifP. Qed.

Lemma comparable_maxl z : {in >=< z &, forall x y, max x y >=< z}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /max; case: ifP. Qed.

Lemma comparable_maxr z : {in >=<%O z &, forall x y, z >=< max x y}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /max; case: ifP. Qed.

Section Comparable2.
Variables (z x y : T) (cmp_xy : x >=< y).

Lemma comparable_minC : min x y = min y x.
Proof. by case: comparableP cmp_xy. Qed.

Lemma comparable_maxC : max x y = max y x.
Proof. by case: comparableP cmp_xy. Qed.

Lemma comparable_eq_minr : (min x y == y) = (y <= x).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP cmp_xy. Qed.

Lemma comparable_eq_maxl : (max x y == x) = (y <= x).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP cmp_xy. Qed.

Lemma comparable_min_idPr : reflect (min x y = y) (y <= x).
Proof. by apply: (iffP idP); rewrite (rwP eqP) comparable_eq_minr. Qed.

Lemma comparable_max_idPl : reflect (max x y = x) (y <= x).
Proof. by apply: (iffP idP); rewrite (rwP eqP) comparable_eq_maxl. Qed.

Lemma comparable_le_minr : (z <= min x y) = (z <= x) && (z <= y).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?andbb//; last rewrite andbC;
  by case: (comparableP z) => // [/lt_trans xlt/xlt|->] /ltW.
Qed.

Lemma comparable_le_minl : (min x y <= z) = (x <= z) || (y <= z).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?orbb//; last rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]//; apply/le_trans/ltW.
Qed.

Lemma comparable_lt_minr : (z < min x y) = (z < x) && (z < y).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?andbb//; last rewrite andbC;
  by case: (comparableP z) => // /lt_trans xlt/xlt.
Qed.

Lemma comparable_lt_minl : (min x y < z) = (x < z) || (y < z).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?orbb//; last rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]//; apply/lt_trans.
Qed.

Lemma comparable_le_maxr : (z <= max x y) = (z <= x) || (z <= y).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?orbb//; first rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]// /le_trans->//; apply/ltW.
Qed.

Lemma comparable_le_maxl : (max x y <= z) = (x <= z) && (y <= z).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?andbb//; first rewrite andbC;
  by case: (comparableP z) => // [ylt /lt_trans /(_ _)/ltW|->/ltW]->.
Qed.

Lemma comparable_lt_maxr : (z < max x y) = (z < x) || (z < y).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?orbb//; first rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]// /lt_trans->.
Qed.

Lemma comparable_lt_maxl : (max x y < z) = (x < z) && (y < z).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?andbb//; first rewrite andbC;
by case: (comparableP z) => // ylt /lt_trans->.
Qed.

Lemma comparable_minxK : max (min x y) y = y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP cmp_xy. Qed.

Lemma comparable_minKx : max x (min x y) = x.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP cmp_xy. Qed.

Lemma comparable_maxxK : min (max x y) y = y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP cmp_xy. Qed.

Lemma comparable_maxKx : min x (max x y) = x.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP cmp_xy. Qed.

Lemma comparable_lteifNE C : x >=< y -> x < y ?<= if ~~ C = ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: comparableP. Qed.

Lemma comparable_lteif_minr C :
  (z < min x y ?<= if C) = (z < x ?<= if C) && (z < y ?<= if C).
Proof. by case: C; rewrite /= (comparable_le_minr, comparable_lt_minr). Qed.

Lemma comparable_lteif_minl C :
  (min x y < z ?<= if C) = (x < z ?<= if C) || (y < z ?<= if C).
Proof. by case: C; rewrite /= (comparable_le_minl, comparable_lt_minl). Qed.

Lemma comparable_lteif_maxr C :
  (z < max x y ?<= if C) = (z < x ?<= if C) || (z < y ?<= if C).
Proof. by case: C; rewrite /= (comparable_le_maxr, comparable_lt_maxr). Qed.

Lemma comparable_lteif_maxl C :
  (max x y < z ?<= if C) = (x < z ?<= if C) && (y < z ?<= if C).
Proof. by case: C; rewrite /= (comparable_le_maxl, comparable_lt_maxl). Qed.

End Comparable2.

Section Comparable3.
Variables (x y z : T) (cmp_xy : x >=< y) (cmp_xz : x >=< z) (cmp_yz : y >=< z).
Let P := comparableP.

Lemma comparable_minA : min x (min y z) = min (min x y) z.
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z) => [xy|xy|xy|<-] [xz|xz|xz|<-]// []//= yz.
- by have := lt_trans xy (lt_trans yz xz); rewrite ltxx.
- by have := lt_trans xy (lt_trans xz yz); rewrite ltxx.
- by have := lt_trans xy xz; rewrite yz ltxx.
Qed.

Lemma comparable_maxA : max x (max y z) = max (max x y) z.
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z) => [xy|xy|xy|<-] [xz|xz|xz|<-]// []//= yz.
- by have := lt_trans xy (lt_trans yz xz); rewrite ltxx.
- by have := lt_trans xy (lt_trans xz yz); rewrite ltxx.
- by have := lt_trans xy xz; rewrite yz ltxx.
Qed.

Lemma comparable_max_minl : max (min x y) z = min (max x z) (max y z).
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z).
move=> [xy|xy|xy|<-] [xz|xz|xz|<-] [yz|yz|yz|//->]//= _; rewrite ?ltxx//.
- by have := lt_trans xy (lt_trans yz xz); rewrite ltxx.
- by have := lt_trans xy (lt_trans xz yz); rewrite ltxx.
Qed.

Lemma comparable_min_maxl : min (max x y) z = max (min x z) (min y z).
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z).
move=> [xy|xy|xy|<-] [xz|xz|xz|<-] []yz//= _; rewrite ?ltxx//.
- by have := lt_trans xy (lt_trans yz xz); rewrite ltxx.
- by have := lt_trans xy yz; rewrite ltxx.
- by have := lt_trans xy (lt_trans xz yz); rewrite ltxx.
- by have := lt_trans xy xz; rewrite yz ltxx.
Qed.

End Comparable3.

Lemma comparable_minAC x y z : x >=< y -> x >=< z -> y >=< z ->
  min (min x y) z = min (min x z) y.
Proof.
move=> xy xz yz; rewrite -comparable_minA// [min y z]comparable_minC//.
by rewrite comparable_minA// 1?comparable_sym.
Qed.

Lemma comparable_maxAC x y z : x >=< y -> x >=< z -> y >=< z ->
  max (max x y) z = max (max x z) y.
Proof.
move=> xy xz yz; rewrite -comparable_maxA// [max y z]comparable_maxC//.
by rewrite comparable_maxA// 1?comparable_sym.
Qed.

Lemma comparable_minCA x y z : x >=< y -> x >=< z -> y >=< z ->
  min x (min y z) = min y (min x z).
Proof.
move=> xy xz yz; rewrite comparable_minA// [min x y]comparable_minC//.
by rewrite -comparable_minA// 1?comparable_sym.
Qed.

Lemma comparable_maxCA x y z : x >=< y -> x >=< z -> y >=< z ->
  max x (max y z) = max y (max x z).
Proof.
move=> xy xz yz; rewrite comparable_maxA// [max x y]comparable_maxC//.
by rewrite -comparable_maxA// 1?comparable_sym.
Qed.

Lemma comparable_minACA x y z t :
    x >=< y -> x >=< z -> x >=< t -> y >=< z -> y >=< t -> z >=< t ->
  min (min x y) (min z t) = min (min x z) (min y t).
Proof.
move=> xy xz xt yz yt zt; rewrite comparable_minA// ?comparable_minl//.
rewrite [min _ z]comparable_minAC// -comparable_minA// ?comparable_minl//.
by rewrite inE comparable_sym.
Qed.

Lemma comparable_maxACA x y z t :
    x >=< y -> x >=< z -> x >=< t -> y >=< z -> y >=< t -> z >=< t ->
  max (max x y) (max z t) = max (max x z) (max y t).
Proof.
move=> xy xz xt yz yt zt; rewrite comparable_maxA// ?comparable_maxl//.
rewrite [max _ z]comparable_maxAC// -comparable_maxA// ?comparable_maxl//.
by rewrite inE comparable_sym.
Qed.

Lemma comparable_max_minr x y z : x >=< y -> x >=< z -> y >=< z ->
  max x (min y z) = min (max x y) (max x z).
Proof.
move=> xy xz yz; rewrite ![max x _]comparable_maxC// ?comparable_minr//.
by rewrite comparable_max_minl// 1?comparable_sym.
Qed.

Lemma comparable_min_maxr x y z : x >=< y -> x >=< z -> y >=< z ->
  min x (max y z) = max (min x y) (min x z).
Proof.
move=> xy xz yz; rewrite ![min x _]comparable_minC// ?comparable_maxr//.
by rewrite comparable_min_maxl// 1?comparable_sym.
Qed.

Section ArgExtremum.

Context (I : finType) (i0 : I) (P : {pred I}) (F : I -> T) (Pi0 : P i0).
Hypothesis F_comparable : {in P &, forall i j, F i >=< F j}.

Lemma comparable_arg_minP: extremum_spec le P F (arg_min i0 P F).
Proof.
by apply: extremum_inP => // [x _|y x z _ _ _]; [apply: lexx|apply: le_trans].
Qed.

Lemma comparable_arg_maxP: extremum_spec ge P F (arg_max i0 P F).
Proof.
apply: extremum_inP => // [x _|y x z _ _ _|]; [exact: lexx|exact: ge_trans|].
by move=> x y xP yP; rewrite orbC [_ || _]F_comparable.
Qed.

End ArgExtremum.

(* monotonicity *)

Lemma mono_in_leif (A : {pred T}) (f : T -> T) C :
   {in A &, {mono f : x y / x <= y}} ->
  {in A &, forall x y, (f x <= f y ?= iff C) = (x <= y ?= iff C)}.
Proof. by move=> mf x y Ax Ay; rewrite /leif !eq_le !mf. Qed.

Lemma mono_leif (f : T -> T) C :
    {mono f : x y / x <= y} ->
  forall x y, (f x <= f y ?= iff C) = (x <= y ?= iff C).
Proof. by move=> mf x y; rewrite /leif !eq_le !mf. Qed.

Lemma nmono_in_leif (A : {pred T}) (f : T -> T) C :
    {in A &, {mono f : x y /~ x <= y}} ->
  {in A &, forall x y, (f x <= f y ?= iff C) = (y <= x ?= iff C)}.
Proof. by move=> mf x y Ax Ay; rewrite /leif !eq_le !mf. Qed.

Lemma nmono_leif (f : T -> T) C : {mono f : x y /~ x <= y} ->
  forall x y, (f x <= f y ?= iff C) = (y <= x ?= iff C).
Proof. by move=> mf x y; rewrite /leif !eq_le !mf. Qed.

Lemma comparable_bigl x x0 op I (P : pred I) F (s : seq I) :
  {in >=< x &, forall y z, op y z >=< x} -> x0 >=< x ->
  {in P, forall i, F i >=< x} -> \big[op/x0]_(i <- s | P i) F i >=< x.
Proof. by move=> *; elim/big_ind : _. Qed.

Lemma comparable_bigr x x0 op I (P : pred I) F (s : seq I) :
  {in >=<%O x &, forall y z, x >=< op y z} -> x >=< x0 ->
  {in P, forall i, x >=< F i} -> x >=< \big[op/x0]_(i <- s | P i) F i.
Proof. by move=> *; elim/big_ind : _. Qed.

End POrderTheory.
(* Hint Resolve comparable_minr comparable_minl : core. *)
(* Hint Resolve comparable_maxr comparable_maxl : core. *)

(* TODO:
Section ContraTheory.
Section POrderMonotonyTheory.
*)

End POrderTheory.

Hint Extern 0 (is_true (le _ _ _)) => apply: lexx : core.
Hint Resolve lexx ltxx lt_irreflexive ltW lt_eqF : core.

Arguments leifP {T ord x y C}.
Arguments leif_refl {T ord x C}.
Arguments mono_in_leif [T ord A f C].
Arguments nmono_in_leif [T ord A f C].
Arguments mono_leif [T ord f C].
Arguments nmono_leif [T ord f C].
Arguments min_idPl {T ord x y}.
Arguments max_idPr {T ord x y}.
Arguments comparable_min_idPr {T ord x y _}.
Arguments comparable_max_idPl {T ord x y _}.

Module Import BPOrderTheory.
Section BPOrderTheory.
Context {T : eqType} {ord : {bPOrder T}}.
Implicit Types (x y : T).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x < y" := (x <_ord y).
Local Notation "0" := (bottom ord).

Lemma le0x x : 0 <= x. Proof. by case: ord => ? ? ? []. Qed.

Lemma lex0 x : (x <= 0) = (x == 0).
Proof. by rewrite le_eqVlt (le_gtF (le0x _)) orbF. Qed.

Lemma ltx0 x : (x < 0) = false.
Proof. by rewrite lt_neqAle lex0 andNb. Qed.

Lemma lt0x x : (0 < x) = (x != 0).
Proof. by rewrite lt_neqAle le0x andbT eq_sym. Qed.

Variant eq0_xor_gt0 x : bool -> bool -> Set :=
    Eq0NotPOs : x = 0 -> eq0_xor_gt0 x true false
  | POsNotEq0 : 0 < x -> eq0_xor_gt0 x false true.

Lemma posxP x : eq0_xor_gt0 x (x == 0) (0 < x).
Proof. by rewrite lt0x; have [] := eqVneq; constructor; rewrite ?lt0x. Qed.

End BPOrderTheory.
End BPOrderTheory.

Module Import TPOrderTheory.
Section TPOrderTheory.
Context {T : eqType} {ord : {tPOrder T}}.
Let ord_dual := [bPOrder of dual_rel <=:ord].
Implicit Types (x y : T).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x < y" := (x <_ord y).
Local Notation "1" := (top ord).

Lemma lex1 (x : T) : x <= 1. Proof. exact: (@le0x _ ord_dual). Qed.
Lemma le1x x : (1 <= x) = (x == 1). Proof. exact: (@lex0 _ ord_dual). Qed.
Lemma lt1x x : (1 < x) = false. Proof. exact: (@ltx0 _ ord_dual). Qed.
Lemma ltx1 x : (x < 1) = (x != 1). Proof. exact: (@lt0x _ ord_dual). Qed.

End TPOrderTheory.
End TPOrderTheory.

Hint Extern 0 (is_true (le _ (bottom _) _)) => apply: le0x : core.
Hint Extern 0 (is_true (le _ _ (top _))) => apply: lex1 : core.

Module Import MeetTheory.
Section MeetTheory.
Context {L : eqType} {ord : {meetOrder L}}.
Implicit Types (x y : L).

Local Notation meet := (meet ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `&` y" := (meet x y).

Lemma meetC : commutative meet. Proof. by case: ord => ? ? ? [? []]. Qed.
Lemma meetA : associative meet. Proof. by case: ord => ? ? ? [? []]. Qed.
Lemma leEmeet x y : (x <= y) = (x `&` y == x).
Proof. by case: ord => ? ? ? [? []]. Qed.

Lemma meetxx : idempotent meet.
Proof. by move=> x; apply/eqP; rewrite -leEmeet. Qed.
Lemma meetAC : right_commutative meet.
Proof. by move=> x y z; rewrite -!meetA [X in _ `&` X]meetC. Qed.
Lemma meetCA : left_commutative meet.
Proof. by move=> x y z; rewrite !meetA [X in X `&` _]meetC. Qed.
Lemma meetACA : interchange meet meet.
Proof. by move=> x y z t; rewrite !meetA [X in X `&` _]meetAC. Qed.

Lemma meetKI y x : x `&` (x `&` y) = x `&` y.
Proof. by rewrite meetA meetxx. Qed.
Lemma meetIK y x : (x `&` y) `&` y = x `&` y.
Proof. by rewrite -meetA meetxx. Qed.
Lemma meetKIC y x : x `&` (y `&` x) = x `&` y.
Proof. by rewrite meetC meetIK meetC. Qed.
Lemma meetIKC y x : y `&` x `&` y = x `&` y.
Proof. by rewrite meetAC meetC meetxx. Qed.

(* interaction with order *)

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

Lemma meet_l x y : x <= y -> x `&` y = x. Proof. exact/meet_idPl. Qed.
Lemma meet_r x y : y <= x -> x `&` y = y. Proof. exact/meet_idPr. Qed.

Lemma leIidl x y : (x <= x `&` y) = (x <= y).
Proof. by rewrite !leEmeet meetKI. Qed.
Lemma leIidr x y : (x <= y `&` x) = (x <= y).
Proof. by rewrite !leEmeet meetKIC. Qed.

Lemma eq_meetl x y : (x `&` y == x) = (x <= y).
Proof. by apply/esym/leEmeet. Qed.

Lemma eq_meetr x y : (x `&` y == y) = (y <= x).
Proof. by rewrite meetC eq_meetl. Qed.

Lemma leI2 x y z t : x <= z -> y <= t -> x `&` y <= z `&` t.
Proof. by move=> xz yt; rewrite lexI !leIx2 ?xz ?yt ?orbT //. Qed.

End MeetTheory.
End MeetTheory.

Arguments meet_idPl {L ord x y}.
Arguments meet_idPr {L ord x y}.

Module Import BMeetTheory.
Section BMeetTheory.
Context {L : eqType} {ord : {bMeetOrder L}}.

Local Notation meet := (meet ord).
Local Notation "0" := (bottom ord).

Lemma meet0x : left_zero 0 meet. Proof. by move=> x; apply/meet_idPl. Qed.
Lemma meetx0 : right_zero 0 meet. Proof. by move=> x; apply/meet_idPr. Qed.

Canonical meet_muloid := Monoid.MulLaw meet0x meetx0.

End BMeetTheory.
End BMeetTheory.

Module Import TMeetTheory.
Section TMeetTheory.
Context {L : eqType} {ord : {tMeetOrder L}}.
Implicit Types (I : finType) (T : eqType) (x y : L).

Local Notation meet := (meet ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `&` y" := (meet x y).
Local Notation "1" := (top ord).

Lemma meetx1 : right_id 1 meet. Proof. by move=> x; apply/meet_idPl. Qed.
Lemma meet1x : left_id 1 meet. Proof. by move=> x; apply/meet_idPr. Qed.

Lemma meet_eq1 x y : (x `&` y == 1) = (x == 1) && (y == 1).
Proof. by rewrite !(@eq_le _ ord) !lex1 lexI. Qed.

Canonical meet_monoid := Monoid.Law meetA meet1x meetx1.
Canonical meet_comoid := Monoid.ComLaw meetC.

Lemma meet_inf_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) :
  x \in r -> P x -> \big[meet/1]_(i <- r | P i) F i <= F x.
Proof. by move=> xr Px; rewrite (big_rem x) ?Px //= leIl. Qed.

Lemma meet_max_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) (u : L) :
  x \in r -> P x -> F x <= u -> \big[meet/1]_(x <- r | P x) F x <= u.
Proof. by move=> ? ?; apply/le_trans/meet_inf_seq. Qed.

Lemma meets_inf I (j : I) (P : {pred I}) (F : I -> L) :
  P j -> \big[meet/1]_(i | P i) F i <= F j.
Proof. exact/meet_inf_seq/mem_index_enum. Qed.

Lemma meets_max I (j : I) (u : L) (P : {pred I}) (F : I -> L) :
  P j -> F j <= u -> \big[meet/1]_(i | P i) F i <= u.
Proof. exact/meet_max_seq/mem_index_enum. Qed.

Lemma meetsP_seq T (r : seq T) (P : {pred T}) (F : T -> L) (l : L) :
  reflect (forall x : T, x \in r -> P x -> l <= F x)
          (l <= \big[meet/1]_(x <- r | P x) F x).
Proof.
apply: (iffP idP) => leFm => [x xr Px|].
  exact/(le_trans leFm)/meet_inf_seq.
rewrite big_seq_cond; elim/big_rec: _ => //= i x /andP[ir Pi] lx.
by rewrite lexI lx leFm.
Qed.

Lemma meetsP I (l : L) (P : {pred I}) (F : I -> L) :
  reflect (forall i : I, P i -> l <= F i) (l <= \big[meet/1]_(i | P i) F i).
Proof. by apply: (iffP (meetsP_seq _ _ _ _)) => H ? ?; apply: H. Qed.

Lemma le_meets I (A B : {set I}) (F : I -> L) :
  A \subset B -> \big[meet/1]_(i in B) F i <= \big[meet/1]_(i in A) F i.
Proof. by move=> /subsetP AB; apply/meetsP => i iA; apply/meets_inf/AB. Qed.

Lemma meets_setU I (A B : {set I}) (F : I -> L) :
  \big[meet/1]_(i in (A :|: B)) F i =
  \big[meet/1]_(i in A) F i `&` \big[meet/1]_(i in B) F i.
Proof.

rewrite -!big_enum; have /= <- := @big_cat _ _ meet_comoid.
apply/eq_big_idem; first exact: meetxx.
by move=> ?; rewrite mem_cat !mem_enum inE.
Qed.

Lemma meet_seq I (r : seq I) (F : I -> L) :
  \big[meet/1]_(i <- r) F i = \big[meet/1]_(i in r) F i.
Proof.
by rewrite -big_enum; apply/eq_big_idem => ?; rewrite /= ?meetxx ?mem_enum.
Qed.

End TMeetTheory.
End TMeetTheory.

Module Import JoinTheory.
Section JoinTheory.
Context {L : eqType} {ord : {joinOrder L}}.
Let ord_dual := [meetOrder of dual_rel <=:ord].
Implicit Types (x y : L).

Local Notation join := (join ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `|` y" := (join x y).

Lemma joinC : commutative join. Proof. exact: (@meetC _ ord_dual). Qed.
Lemma joinA : associative join. Proof. exact: (@meetA _ ord_dual). Qed.
Lemma leEjoin x y : (x <= y) = (x `|` y == y).
Proof. by rewrite joinC; apply: (@leEmeet _ ord_dual). Qed.

Lemma joinxx : idempotent join. Proof. exact: (@meetxx _ ord_dual). Qed.
Lemma joinAC : right_commutative join. Proof. exact: (@meetAC _ ord_dual). Qed.
Lemma joinCA : left_commutative join. Proof. exact: (@meetCA _ ord_dual). Qed.
Lemma joinACA : interchange join join.
Proof. exact: (@meetACA _ ord_dual). Qed.

Lemma joinKU y x : x `|` (x `|` y) = x `|` y.
Proof. exact: (@meetKI _ ord_dual). Qed.
Lemma joinUK y x : (x `|` y) `|` y = x `|` y.
Proof. exact: (@meetIK _ ord_dual). Qed.
Lemma joinKUC y x : x `|` (y `|` x) = x `|` y.
Proof. exact: (@meetKIC _ ord_dual). Qed.
Lemma joinUKC y x : y `|` x `|` y = x `|` y.
Proof. exact: (@meetIKC _ ord_dual). Qed.

(* interaction with order *)
Lemma leUx x y z : (x `|` y <= z) = (x <= z) && (y <= z).
Proof. exact: (@lexI _ ord_dual). Qed.
Lemma lexUl x y z : x <= y -> x <= y `|` z.
Proof. exact: (@leIxl _ ord_dual). Qed.
Lemma lexUr x y z : x <= z -> x <= y `|` z.
Proof. exact: (@leIxr _ ord_dual). Qed.
Lemma lexU2 x y z : (x <= y) || (x <= z) -> x <= y `|` z.
Proof. exact: (@leIx2 _ ord_dual). Qed.

Lemma leUr x y : x <= y `|` x. Proof. exact: (@leIr _ ord_dual). Qed.
Lemma leUl x y : x <= x `|` y. Proof. exact: (@leIl _ ord_dual). Qed.

Lemma join_idPl {x y} : reflect (y `|` x = y) (x <= y).
Proof. exact: (@meet_idPl _ ord_dual). Qed.
Lemma join_idPr {x y} : reflect (x `|` y = y) (x <= y).
Proof. exact: (@meet_idPr _ ord_dual). Qed.

Lemma join_l x y : y <= x -> x `|` y = x. Proof. exact/join_idPl. Qed.
Lemma join_r x y : x <= y -> x `|` y = y. Proof. exact/join_idPr. Qed.

Lemma leUidl x y : (x `|` y <= y) = (x <= y).
Proof. exact: (@leIidr _ ord_dual). Qed.
Lemma leUidr x y : (y `|` x <= y) = (x <= y).
Proof. exact: (@leIidl _ ord_dual). Qed.

Lemma eq_joinl x y : (x `|` y == x) = (y <= x).
Proof. exact: (@eq_meetl _ ord_dual). Qed.
Lemma eq_joinr x y : (x `|` y == y) = (x <= y).
Proof. exact: (@eq_meetr _ ord_dual). Qed.

Lemma leU2 x y z t : x <= z -> y <= t -> x `|` y <= z `|` t.
Proof. exact: (@leI2 _ ord_dual). Qed.

End JoinTheory.
End JoinTheory.

Arguments join_idPl {L ord x y}.
Arguments join_idPr {L ord x y}.

Module Import BJoinTheory.
Section BJoinTheory.
Context {L : eqType} {ord : {bJoinOrder L}}.
Let ord_dual := [tMeetOrder of dual_rel <=:ord].
Implicit Types (I : finType) (T : eqType) (x y : L).

Local Notation join := (join ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `|` y" := (join x y).
Local Notation "0" := (bottom ord).

Lemma joinx0 : right_id 0 join. Proof. exact: (@meetx1 _ ord_dual). Qed.
Lemma join0x : left_id 0 join. Proof. exact: (@meet1x _ ord_dual). Qed.

Lemma join_eq0 x y : (x `|` y == 0) = (x == 0) && (y == 0).
Proof. exact: (@meet_eq1 _ ord_dual). Qed.

Canonical join_monoid := Monoid.Law joinA join0x joinx0.
Canonical join_comoid := Monoid.ComLaw joinC.

Lemma join_sup_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) :
  x \in r -> P x -> F x <= \big[join/0]_(i <- r | P i) F i.
Proof. exact: (@meet_inf_seq _ ord_dual). Qed.

Lemma join_min_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) (l : L) :
  x \in r -> P x -> l <= F x -> l <= \big[join/0]_(x <- r | P x) F x.
Proof. exact: (@meet_max_seq _ ord_dual). Qed.

Lemma join_sup I (j : I) (P : {pred I}) (F : I -> L) :
  P j -> F j <= \big[join/0]_(i | P i) F i.
Proof. exact: (@meets_inf _ ord_dual). Qed.

Lemma join_min I (j : I) (l : L) (P : {pred I}) (F : I -> L) :
  P j -> l <= F j -> l <= \big[join/0]_(i | P i) F i.
Proof. exact: (@meets_max _ ord_dual). Qed.

Lemma joinsP_seq T (r : seq T) (P : {pred T}) (F : T -> L) (u : L) :
  reflect (forall x : T, x \in r -> P x -> F x <= u)
          (\big[join/0]_(x <- r | P x) F x <= u).
Proof. exact: (@meetsP_seq _ ord_dual). Qed.

Lemma joinsP I (u : L) (P : {pred I}) (F : I -> L) :
  reflect (forall i : I, P i -> F i <= u) (\big[join/0]_(i | P i) F i <= u).
Proof. exact: (@meetsP _ ord_dual). Qed.

Lemma le_joins I (A B : {set I}) (F : I -> L) :
  A \subset B -> \big[join/0]_(i in A) F i <= \big[join/0]_(i in B) F i.
Proof. exact: (@le_meets _ ord_dual). Qed.

Lemma joins_setU I (A B : {set I}) (F : I -> L) :
  \big[join/0]_(i in (A :|: B)) F i =
  \big[join/0]_(i in A) F i `|` \big[join/0]_(i in B) F i.
Proof. exact: (@meets_setU _ ord_dual). Qed.

Lemma join_seq I (r : seq I) (F : I -> L) :
  \big[join/0]_(i <- r) F i = \big[join/0]_(i in r) F i.
Proof. exact: (@meet_seq _ ord_dual). Qed.

End BJoinTheory.
End BJoinTheory.

Module Import TJoinTheory.
Section TJoinTheory.
Context {L : eqType} {ord : {tJoinOrder L}}.
Let ord_dual := [bMeetOrder of dual_rel <=:ord].

Local Notation join := (join ord).
Local Notation "1" := (top ord).

Lemma joinx1 : right_zero 1 join. Proof. exact: (@meetx0 _ ord_dual). Qed.
Lemma join1x : left_zero 1 join. Proof. exact: (@meet0x _ ord_dual). Qed.

Canonical join_muloid := Monoid.MulLaw join1x joinx1.

End TJoinTheory.
End TJoinTheory.

Module Import LatticeTheory.
Section LatticeTheory.
Context {L : eqType} {ord : {lattice L}}.
Implicit Types (x y : L).

Local Notation min := (min ord).
Local Notation max := (max ord).
Local Notation lel_xor_gt := (lel_xor_gt ord).
Local Notation ltl_xor_ge := (ltl_xor_ge ord).
Local Notation comparel := (comparel ord).
Local Notation incomparel := (incomparel ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x < y" := (x <_ord y).
Local Notation "x >= y" := (x >=_ord y) (only parsing).
Local Notation "x > y" := (x >_ord y) (only parsing).
Local Notation "x >=< y" := (comparable ord x y).
Local Notation "x `&` y" := (meet ord x y).
Local Notation "x `|` y" := (join ord x y).

Lemma meetUK x y : (x `&` y) `|` y = y.
Proof. by apply/eqP; rewrite eq_joinr -eq_meetl meetIK. Qed.

Lemma meetUKC x y : (y `&` x) `|` y = y. Proof. by rewrite meetC meetUK. Qed.
Lemma meetKUC y x : x `|` (y `&` x) = x. Proof. by rewrite joinC meetUK. Qed.
Lemma meetKU y x : x `|` (x `&` y) = x. Proof. by rewrite meetC meetKUC. Qed.

Lemma joinIK x y : (x `|` y) `&` y = y.
Proof. by apply/eqP; rewrite eq_meetr -eq_joinl joinUK. Qed.

Lemma joinIKC x y : (y `|` x) `&` y = y. Proof. by rewrite joinC joinIK. Qed.
Lemma joinKIC y x : x `&` (y `|` x) = x. Proof. by rewrite meetC joinIK. Qed.
Lemma joinKI y x : x `&` (x `|` y) = x. Proof. by rewrite joinC joinKIC. Qed.

(* comparison predicates *)

Lemma lcomparableP x y : incomparel x y
  (min y x) (min x y) (max y x) (max x y)
  (y `&` x) (x `&` y) (y `|` x) (x `|` y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y) (y >=< x) (x >=< y).
Proof.
by case: (comparableP x) => [hxy|hxy|hxy|->]; do 1?have hxy' := ltW hxy;
   rewrite ?(meetxx, joinxx);
   rewrite ?(meet_l hxy', meet_r hxy', join_l hxy', join_r hxy');
   constructor.
Qed.

Lemma lcomparable_ltgtP x y : x >=< y ->
  comparel x y (min y x) (min x y) (max y x) (max x y)
               (y `&` x) (x `&` y) (y `|` x) (x `|` y)
               (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof. by case: (lcomparableP x) => // *; constructor. Qed.

Lemma lcomparable_leP x y : x >=< y ->
  lel_xor_gt x y (min y x) (min x y) (max y x) (max x y)
                 (y `&` x) (x `&` y) (y `|` x) (x `|` y) (x <= y) (y < x).
Proof. by case/lcomparable_ltgtP => [/ltW xy|xy|->]; constructor. Qed.

Lemma lcomparable_ltP x y : x >=< y ->
  ltl_xor_ge x y (min y x) (min x y) (max y x) (max x y)
                 (y `&` x) (x `&` y) (y `|` x) (x `|` y) (y <= x) (x < y).
Proof. by case/lcomparable_ltgtP => [xy|/ltW xy|->]; constructor. Qed.

End LatticeTheory.
End LatticeTheory.

Module Import DistrLatticeTheory.
Section DistrLatticeTheory.
Context {L : eqType} {ord : {distrLattice L}}.
Implicit Types (x y : L).

Local Notation meet := (meet ord).
Local Notation join := (join ord).

Local Notation "x `&` y" := (meet x y).
Local Notation "x `|` y" := (join x y).

Lemma meetUl : left_distributive meet join.
Proof. by case: ord => ? ? ? ? [? []]. Qed.

Lemma joinIl : left_distributive join meet.
Proof. by case: ord => ? ? ? ? [? []]. Qed.

Lemma meetUr : right_distributive meet join.
Proof. by move=> x y z; rewrite ![x `&` _]meetC meetUl. Qed.

Lemma joinIr : right_distributive join meet.
Proof. by move=> x y z; rewrite ![x `|` _]joinC joinIl. Qed.

End DistrLatticeTheory.
End DistrLatticeTheory.

Module Import BDistrLatticeTheory.
Section BDistrLatticeTheory.
Context {L : eqType} {ord : {bDistrLattice L}}.
Implicit Types (I : finType) (T : eqType) (x y z : L).

Local Notation meet := (meet ord).
Local Notation join := (join ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `&` y" := (meet x y).
Local Notation "x `|` y" := (join x y).
Local Notation "0" := (bottom ord).
(* Distributive lattice theory with 0 *)

Canonical join_addoid := Monoid.AddLaw (@meetUl _ ord) (@meetUr _ _).

Lemma leU2l_le y t x z : x `&` t = 0 -> x `|` y <= z `|` t -> x <= z.
Proof.
by move=> xIt0 /(leI2 (lexx x)); rewrite joinKI meetUr xIt0 joinx0 leIidl.
Qed.

Lemma leU2r_le y t x z : x `&` t = 0 -> y `|` x <= t `|` z -> x <= z.
Proof. by rewrite joinC [_ `|` z]joinC => /leU2l_le H /H. Qed.

Lemma disjoint_lexUl z x y : x `&` z = 0 -> (x <= y `|` z) = (x <= y).
Proof.
move=> xz0; apply/idP/idP=> xy; last by rewrite lexU2 ?xy.
by apply: (@leU2l_le x z); rewrite ?joinxx.
Qed.

Lemma disjoint_lexUr z x y : x `&` z = 0 -> (x <= z `|` y) = (x <= y).
Proof. by move=> xz0; rewrite joinC; rewrite disjoint_lexUl. Qed.

Lemma leU2E x y z t : x `&` t = 0 -> y `&` z = 0 ->
  (x `|` y <= z `|` t) = (x <= z) && (y <= t).
Proof.
move=> dxt dyz; apply/idP/andP; last by case=> ? ?; exact: leU2.
by move=> lexyzt; rewrite (leU2l_le _ lexyzt) // (leU2r_le _ lexyzt).
Qed.

Lemma joins_disjoint I (d : L) (P : {pred I}) (F : I -> L) :
   (forall i : I, P i -> d `&` F i = 0) -> d `&` \big[join/0]_(i | P i) F i = 0.
Proof.
move=> d_Fi_disj; have : \big[andb/true]_(i | P i) (d `&` F i == 0).
  rewrite big_all_cond; apply/allP => i _ /=.
  by apply/implyP => /d_Fi_disj ->.
elim/big_rec2: _ => [|i y]; first by rewrite meetx0.
case; rewrite (andbF, andbT) // => Pi /(_ isT) dy /eqP dFi.
by rewrite meetUr dy dFi joinxx.
Qed.

End BDistrLatticeTheory.
End BDistrLatticeTheory.

Module Import TDistrLatticeTheory.
Section TDistrLatticeTheory.
Context {L : eqType} {ord : {tDistrLattice L}}.
Let ord_dual := [bDistrLattice of dual_rel <=:ord].
Implicit Types (I : finType) (T : eqType) (x y z : L).

Local Notation meet := (meet ord).
Local Notation join := (join ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `&` y" := (meet x y).
Local Notation "x `|` y" := (join x y).
Local Notation "1" := (top ord).
(* Distributive lattice theory with 1 *)

Canonical meet_addoid := Monoid.AddLaw (@joinIl _ ord) (@joinIr _ _).

Lemma leI2l_le y t x z : y `|` z = 1 -> x `&` y <= z `&` t -> x <= z.
Proof. rewrite joinC; exact: (@leU2l_le _ ord_dual). Qed.

Lemma leI2r_le y t x z : y `|` z = 1 -> y `&` x <= t `&` z -> x <= z.
Proof. rewrite joinC; exact: (@leU2r_le _ ord_dual). Qed.

Lemma cover_leIxl z x y : z `|` y = 1 -> (x `&` z <= y) = (x <= y).
Proof. rewrite joinC; exact: (@disjoint_lexUl _ ord_dual). Qed.

Lemma cover_leIxr z x y : z `|` y = 1 -> (z `&` x <= y) = (x <= y).
Proof. rewrite joinC; exact: (@disjoint_lexUr _ ord_dual). Qed.

Lemma leI2E x y z t : x `|` t = 1 -> y `|` z = 1 ->
  (x `&` y <= z `&` t) = (x <= z) && (y <= t).
Proof. by move=> ? ?; apply: (@leU2E _ ord_dual); rewrite meetC. Qed.

Lemma meets_total I (d : L) (P : {pred I}) (F : I -> L) :
   (forall i : I, P i -> d `|` F i = 1) -> d `|` \big[meet/1]_(i | P i) F i = 1.
Proof. exact: (@joins_disjoint _ ord_dual). Qed.

End TDistrLatticeTheory.
End TDistrLatticeTheory.

Module Import TotalTheory.
Section TotalTheory.
Context {T : eqType} {ord : {totalOrder T}}.
Implicit Types (x y z t : T) (s : seq T).

Local Notation le := (le ord).
Local Notation lt := (lt ord).
Local Notation ge := (ge ord).
Local Notation min := (min ord).
Local Notation max := (max ord).
Local Notation arg_min := (arg_min ord).
Local Notation arg_max := (arg_max ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x < y" := (x <_ord y).
Local Notation "x >= y" := (x >=_ord y) (only parsing).
Local Notation "x > y" := (x >_ord y) (only parsing).
Local Notation "x >=< y" := (comparable ord x y).
Local Notation "x < y ?<= 'if' C" := (lteif ord x y C).
Local Notation "x `&` y" := (meet ord x y).
Local Notation "x `|` y" := (join ord x y).

Lemma le_total : total le. Proof. by case: ord => ? ? ? ? []. Qed.
Hint Resolve le_total : core.

Lemma ge_total : total ge. Proof. by move=> ? ?; apply: le_total. Qed.
Hint Resolve ge_total : core.

Lemma comparableT x y : x >=< y. Proof. exact: le_total. Qed.
Hint Resolve comparableT : core.

Lemma sort_le_sorted s : sorted le (sort le s).
Proof. exact: sort_sorted. Qed.
Hint Resolve sort_le_sorted : core.

Lemma sort_lt_sorted s : sorted lt (sort le s) = uniq s.
Proof. by rewrite lt_sorted_uniq_le sort_uniq sort_le_sorted andbT. Qed.

Lemma leNgt x y : (x <= y) = ~~ (y < x). Proof. exact: comparable_leNgt. Qed.

Lemma ltNge x y : (x < y) = ~~ (y <= x). Proof. exact: comparable_ltNge. Qed.

Definition ltgtP x y := LatticeTheory.lcomparable_ltgtP (comparableT x y).
Definition leP x y := LatticeTheory.lcomparable_leP (comparableT x y).
Definition ltP x y := LatticeTheory.lcomparable_ltP (comparableT x y).

Lemma wlog_le P :
     (forall x y, P y x -> P x y) -> (forall x y, x <= y -> P x y) ->
   forall x y, P x y.
Proof. by move=> sP hP x y; case: (leP x y) => [| /ltW] /hP // /sP. Qed.

Lemma wlog_lt P :
    (forall x, P x x) ->
    (forall x y, (P y x -> P x y)) -> (forall x y, x < y -> P x y) ->
  forall x y, P x y.
Proof. by move=> rP sP hP x y; case: (ltgtP x y) => [||->] // /hP // /sP. Qed.

Lemma neq_lt x y : (x != y) = (x < y) || (y < x). Proof. by case: ltgtP. Qed.

Lemma lt_total x y : x != y -> (x < y) || (y < x). Proof. by case: ltgtP. Qed.

Lemma eq_leLR x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (x <= y) = (z <= t).
Proof. by rewrite !ltNge => ? /contraTT ?; apply/idP/idP. Qed.

Lemma eq_leRL x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (z <= t) = (x <= y).
Proof. by move=> *; symmetry; apply: eq_leLR. Qed.

Lemma eq_ltLR x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (x < y) = (z < t).
Proof. by rewrite !leNgt => ? /contraTT ?; apply/idP/idP. Qed.

Lemma eq_ltRL x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (z < t) = (x < y).
Proof. by move=> *; symmetry; apply: eq_ltLR. Qed.

(* max and min is join and meet *)

Lemma meetEtotal x y : x `&` y = min x y. Proof. by case: leP. Qed.
Lemma joinEtotal x y : x `|` y = max x y. Proof. by case: leP. Qed.

(* max and min theory *)

Lemma minEgt x y : min x y = if x > y then y else x. Proof. by case: ltP. Qed.
Lemma maxEgt x y : max x y = if x > y then x else y. Proof. by case: ltP. Qed.
Lemma minEge x y : min x y = if x >= y then y else x. Proof. by case: leP. Qed.
Lemma maxEge x y : max x y = if x >= y then x else y. Proof. by case: leP. Qed.

Lemma minC : commutative min. Proof. by move=> x y; apply: comparable_minC. Qed.

Lemma maxC : commutative max. Proof. by move=> x y; apply: comparable_maxC. Qed.

Lemma minA : associative min.
Proof. by move=> x y z; apply: comparable_minA. Qed.

Lemma maxA : associative max.
Proof. by move=> x y z; apply: comparable_maxA. Qed.

Lemma minAC : right_commutative min.
Proof. by move=> x y z; apply: comparable_minAC. Qed.

Lemma maxAC : right_commutative max.
Proof. by move=> x y z; apply: comparable_maxAC. Qed.

Lemma minCA : left_commutative min.
Proof. by move=> x y z; apply: comparable_minCA. Qed.

Lemma maxCA : left_commutative max.
Proof. by move=> x y z; apply: comparable_maxCA. Qed.

Lemma minACA : interchange min min.
Proof. by move=> x y z t; apply: comparable_minACA. Qed.

Lemma maxACA : interchange max max.
Proof. by move=> x y z t; apply: comparable_maxACA. Qed.

Lemma eq_minr x y : (min x y == y) = (y <= x).
Proof. exact: comparable_eq_minr. Qed.

Lemma eq_maxl x y : (max x y == x) = (y <= x).
Proof. exact: comparable_eq_maxl. Qed.

Lemma min_idPr x y : reflect (min x y = y) (y <= x).
Proof. exact: comparable_min_idPr. Qed.

Lemma max_idPl x y : reflect (max x y = x) (y <= x).
Proof. exact: comparable_max_idPl. Qed.

Lemma le_minr z x y : (z <= min x y) = (z <= x) && (z <= y).
Proof. exact: comparable_le_minr. Qed.

Lemma le_minl z x y : (min x y <= z) = (x <= z) || (y <= z).
Proof. exact: comparable_le_minl. Qed.

Lemma lt_minr z x y : (z < min x y) = (z < x) && (z < y).
Proof. exact: comparable_lt_minr. Qed.

Lemma lt_minl z x y : (min x y < z) = (x < z) || (y < z).
Proof. exact: comparable_lt_minl. Qed.

Lemma le_maxr z x y : (z <= max x y) = (z <= x) || (z <= y).
Proof. exact: comparable_le_maxr. Qed.

Lemma le_maxl z x y : (max x y <= z) = (x <= z) && (y <= z).
Proof. exact: comparable_le_maxl. Qed.

Lemma lt_maxr z x y : (z < max x y) = (z < x) || (z < y).
Proof. exact: comparable_lt_maxr. Qed.

Lemma lt_maxl z x y : (max x y < z) = (x < z) && (y < z).
Proof. exact: comparable_lt_maxl. Qed.

Lemma minxK x y : max (min x y) y = y. Proof. exact: comparable_minxK. Qed.
Lemma minKx x y : max x (min x y) = x. Proof. exact: comparable_minKx. Qed.
Lemma maxxK x y : min (max x y) y = y. Proof. exact: comparable_maxxK. Qed.
Lemma maxKx x y : min x (max x y) = x. Proof. exact: comparable_maxKx. Qed.

Lemma max_minl : left_distributive max min.
Proof. by move=> x y z; apply: comparable_max_minl. Qed.

Lemma min_maxl : left_distributive min max.
Proof. by move=> x y z; apply: comparable_min_maxl. Qed.

Lemma max_minr : right_distributive max min.
Proof. by move=> x y z; apply: comparable_max_minr. Qed.

Lemma min_maxr : right_distributive min max.
Proof. by move=> x y z; apply: comparable_min_maxr. Qed.

Lemma leIx x y z : (y `&` z <= x) = (y <= x) || (z <= x).
Proof. by rewrite meetEtotal le_minl. Qed.

Lemma lexU x y z : (x <= y `|` z) = (x <= y) || (x <= z).
Proof. by rewrite joinEtotal le_maxr. Qed.

Lemma ltxI x y z : (x < y `&` z) = (x < y) && (x < z).
Proof. by rewrite !ltNge leIx negb_or. Qed.

Lemma ltIx x y z : (y `&` z < x) = (y < x) || (z < x).
Proof. by rewrite !ltNge lexI negb_and. Qed.

Lemma ltxU x y z : (x < y `|` z) = (x < y) || (x < z).
Proof. by rewrite !ltNge leUx negb_and. Qed.

Lemma ltUx x y z : (y `|` z < x) = (y < x) && (z < x).
Proof. by rewrite !ltNge lexU negb_or. Qed.

Definition ltexI := (@lexI _ ord, ltxI).
Definition lteIx := (leIx, ltIx).
Definition ltexU := (lexU, ltxU).
Definition lteUx := (@leUx _ ord, ltUx).

(* lteif *)

Lemma lteifNE x y C : x < y ?<= if ~~ C = ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: leP. Qed.

Lemma lteif_minr z x y C :
  (z < min x y ?<= if C) = (z < x ?<= if C) && (z < y ?<= if C).
Proof. by case: C; rewrite /= (le_minr, lt_minr). Qed.

Lemma lteif_minl z x y C :
  (min x y < z ?<= if C) = (x < z ?<= if C) || (y < z ?<= if C).
Proof. by case: C; rewrite /= (le_minl, lt_minl). Qed.

Lemma lteif_maxr z x y C :
  (z < max x y ?<= if C) = (z < x ?<= if C) || (z < y ?<= if C).
Proof. by case: C; rewrite /= (le_maxr, lt_maxr). Qed.

Lemma lteif_maxl z x y C :
  (max x y < z ?<= if C) = (x < z ?<= if C) && (y < z ?<= if C).
Proof. by case: C; rewrite /= (le_maxl, lt_maxl). Qed.

Section ArgExtremum.

Context (I : finType) (i0 : I) (P : {pred I}) (F : I -> T) (Pi0 : P i0).

Lemma arg_minP: extremum_spec le P F (arg_min i0 P F).
Proof. by apply: extremumP => //; apply: le_trans. Qed.

Lemma arg_maxP: extremum_spec ge P F (arg_max i0 P F).
Proof. by apply: extremumP => //; [apply: ge_refl | apply: ge_trans]. Qed.

End ArgExtremum.

End TotalTheory.

Hint Resolve le_total : core.
Hint Resolve ge_total : core.
Hint Resolve comparableT : core.
Hint Resolve sort_le_sorted : core.

Arguments min_idPr {T ord x y}.
Arguments max_idPl {T ord x y}.

(* contra lemmas *)

(* TODO:
Section ContraTheory.
Section TotalMonotonyTheory.
*)
End TotalTheory.

(* ========================================================================== *)

Local Open Scope fset_scope.

Section FsetOrderTheory.

Context {T : choiceType} (L : {pOrder T}).

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

(* ========================================================================== *)
Notation "ord ^~" := (dual_pOrder ord) (at level 8, format "ord ^~").

Module DualOrderTest.
Section DualOrderTest.
Variable (T : eqType) (ord : {pOrder T}).

Lemma le_dual_inv x y: x <=_((ord^~)^~) y = x <=_ord y.
Proof. by []. Qed.

Lemma lt_dual_inv x y: x <_((ord^~)^~) y = x <_ord y.
Proof. by []. Qed.

Goal POrder.class ord = POrder.class (ord^~)^~.
Proof. by []. Qed.

Goal [leo: (dual_rel <=:ord)] = ord^~.
Proof. by []. Qed.

Goal [lto: (dual_rel <:ord)] = ord^~.
Proof. by []. Qed.

Goal forall x y, x <_ord y -> y <_(ord^~) x.
Proof. by []. Qed.

Goal forall x y, x <=_ord y = y <=_(ord^~) x.
Proof. by []. Qed.

End DualOrderTest.
End DualOrderTest.

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

Module NatOrder.

Lemma leq_asym x y : (x <= y)%N -> (y <= x)%N -> x = y.
Proof. by move=> ? ?; apply/anti_leq/andP. Qed.

Lemma dltn_def x y : (y < x)%N = (x != y) && (y <= x)%N.
Proof. by rewrite ltn_neqAle eq_sym. Qed.

Lemma leqEminn x y : (x <= y)%N = (minn x y == x).
Proof. exact/minn_idPl/eqP. Qed.

Lemma leqEmaxn x y : (x >= y)%N = (maxn x y == x).
Proof. exact/maxn_idPl/eqP. Qed.

Definition nat_pOrderMixin :=
  POrder.Mixin leqnn leq_asym leq_trans ltn_neqAle dltn_def.

Local Canonical nat_pOrder := POrder leq ltn nat_pOrderMixin.
(* BUG, TODO: the packager [BPOrder] can infer the [pOrder] instance only     *)
(* from the symbol [leq]. If [leq] is replaced with [nosimpl leq] above, the  *)
(* following declaration fails.                                               *)
Local Canonical nat_bPOrder := BPOrder leq ltn 0 leq0n.
Local Canonical nat_meetOrder :=
  MeetOrder leq ltn minn (Meet.Mixin minnC minnA leqEminn).
Local Canonical nat_bMeetOrder := [bMeetOrder of leq].
Local Canonical nat_joinOrder :=
  JoinOrder leq ltn maxn (Meet.Mixin maxnC maxnA leqEmaxn).
Local Canonical nat_bJoinOrder := [bJoinOrder of leq].
Local Canonical nat_lattice := [lattice of leq].
Local Canonical nat_bLattice := [bLattice of leq].
Local Canonical nat_distrLattice :=
  DistrLattice leq ltn minn maxn (DistrLattice.Mixin minn_maxl maxn_minl).
Local Canonical nat_bDistrLattice := [bDistrLattice of leq].
Local Canonical nat_totalOrder := TotalOrder leq ltn minn maxn leq_total.
Local Canonical nat_bTotalOrder := [bTotalOrder of leq].

End NatOrder.

(* ===================================================================== *)

Module PreLattice.
Section ClassDef.

Context {T : choiceType}.

Set Primitive Projections.
  
Record class (r : {pOrder T}) := Class
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
  pack_order : {pOrder T};
  pack_class : class pack_order
}.

Unset Primitive Projections.

Local Coercion pack_order : pack >-> POrder.order.

Variable (phr : phant T) (m : pack phr).

Definition order_of := POrder.Pack phr (POrder.class m).
Definition clone (r : {pOrder T}) :=
  fun (pl : pack phr) & phant_id (pack_order pl) r =>
  pl.

End ClassDef.


(* ---------------------------------------------------------------------- *)

Module Exports.

Canonical order_of.
Coercion pack_order : pack >-> POrder.order.
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
    by rewrite lt_neqAle eq_sym yNbot bot_le_y.
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
