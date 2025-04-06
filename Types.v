
Require Import String.

Require Import Aux.
Require Import Snoclist.
Import SnoclistNotations.
Require Import PlanarLambda.

Inductive type : Type :=
| TVar : nat -> type
| TImp : type -> type -> type.

Fixpoint softy (ty : type) : string :=
match ty with
| TVar n => sofn n
| TImp ty1 ty2 =>
  match (ty1, ty2) with
  | (TVar n, TVar m) => sofn n ++ " -> " ++ sofn m
  | (TVar n, _) => sofn n ++ " -> " ++ softy ty2
  | (_, TVar m) => "(" ++ softy ty1 ++ ") -> " ++ sofn m 
  | _ => "(" ++ softy ty1 ++ ") -> " ++ softy ty2
  end
end.

(* Typing *)

Definition context n : Type := snoclist type n.

Inductive is_typed : forall {a : nat}, context a -> pterm a -> type -> Prop :=
| typed_var ty : is_typed [ty] PVar ty
| typed_abs {n} ty1 gamma (pt : pterm (S n)) ty2 :
  is_typed (gamma :: ty1) pt ty2 -> is_typed gamma (PAbs pt) (TImp ty1 ty2)
| typed_app {n m} gamma delta (pt1 : pterm n) (pt2 : pterm m) ty1 ty2:
  is_typed gamma pt1 (TImp ty1 ty2) -> is_typed delta pt2 ty1 ->
  is_typed (gamma ++ delta) (PApp pt1 pt2) ty2.

Definition type_eq : Type := type * type.
Definition constraints : Type := list type_eq.

Inductive not_FTV : nat -> type -> Prop :=
| nFTV_var a b : a <> b -> not_FTV a (TVar b)
| nFTV_imp a ty1 ty2 :
  not_FTV a ty1 ->
  not_FTV a ty2 ->
  not_FTV a (TImp ty1 ty2).