Require Import Snoclist.
Import SnoclistNotations.
Require Import Types.

Require Import LabeledLambda.

Require List.

Definition type_eq : Type := type * type.
Definition constraints : Type := list type_eq.

Inductive is_bidir_syn : forall {a : nat}, context a -> sterm a -> type -> constraints -> Prop :=
| bidir_abs {n} ty1 gamma (st : sterm (S n)) ty2 const :
  is_bidir_syn (gamma :: ty1) st ty2 const -> 
  is_bidir_syn  gamma (SAbs st) (TImp ty1 ty2) const
| bidir_cir {n} (a : nat) gamma (ct : cterm n) const :
  is_bidir_chk gamma ct (TVar a) const ->
  is_bidir_syn gamma (SCir a ct) (TVar a) const

with is_bidir_chk : forall {a : nat}, context a -> cterm a -> type -> constraints -> Prop :=
| bidir_var ty : is_bidir_chk [ty] CVar ty List.nil
| bidir_app {n m} gamma delta (ct1 : cterm n) (st2 : sterm m) ty1 ty2 const1 const2 :
  is_bidir_chk gamma ct1 (TImp ty1 ty2) const1 ->
  is_bidir_syn delta st2 ty1 const2 ->
  is_bidir_chk (gamma ++ delta) (CApp ct1 st2) ty2 (List.app const1 const2)
| bidir_squ {n} gamma (st : sterm n) ty1 ty2 const :
  is_bidir_syn gamma st ty1 const ->
  is_bidir_chk gamma (CSqu st) ty2 (List.cons (ty1, ty2) const).

Inductive is_bidir : forall {a : nat}, context a -> lterm a -> type -> constraints -> Prop :=
| Sbidir {n} gamma (st : sterm n) ty const :
  is_bidir_syn gamma st ty const ->
  is_bidir gamma (LSyn st) ty const
| Cbidir {n} gamma (ct : cterm n) ty const :
  is_bidir_chk gamma ct ty const ->
  is_bidir gamma (LChk ct) ty const.