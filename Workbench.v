
Require Import Snoclist.
Import SnoclistNotations.
Require Import PlanarLambda.
Require Import Types.

Definition context : Type := snoclist type.

Inductive test (n : nat) (pt : pterm n) : Type :=
| Test : test n pt.

Inductive test2 : nat -> Type :=
| Test2 : test2 0.

Check test2.

(*
Inductive is_typed : context -> pterm (a : nat) -> type -> Prop :=
| type_var ty : is_typed [ty] PVar ty.
*)
