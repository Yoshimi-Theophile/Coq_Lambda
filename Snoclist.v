Require Import Arith.

Inductive snoclist (A : Type) : nat -> Type :=
| nil : snoclist A 0
| snoc : forall n : nat, snoclist A n -> A -> snoclist A (S n).

Arguments nil {A}.
Arguments snoc {A} {n} l a.

Declare Scope snoclist_scope.
Delimit Scope snoclist_scope with snoclist.
Bind Scope snoclist_scope with snoclist.

Open Scope snoclist_scope.

Infix "::" := snoc (at level 60, right associativity) : snoclist_scope.

Module SnoclistNotations.
Notation "[ ]" := nil (format "[ ]"): snoclist_scope.
Notation "[ x ]" := (snoc nil x): snoclist_scope.
(*
Notation "[ x ; y ; .. ; z ]" := (snoc (snoc .. (snoc nil x) .. y) z)
  (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]"): snoclist_scope.
*)
End SnoclistNotations.

Import SnoclistNotations.

(*Definition length {A : Type} {n : nat} : snoclist A n -> nat := fix length l := n.*)

Theorem snoclist_comm {A : Type} {n m : nat} : snoclist A (m + n) -> snoclist A (n + m).
Proof. rewrite Nat.add_comm. intro h. apply h. Qed.

Fixpoint app {A : Type} {n m : nat} (l : snoclist A n) (r : snoclist A m) : snoclist A (n + m) :=
match r in (snoclist _ m) return (snoclist _ (m + n) -> snoclist _ (n + m)) -> snoclist _ (n + m) with
| nil => fun H => H l
| r' :: a => fun H => H ( snoclist_comm (app l r') :: a)
end snoclist_comm.

Infix "++" := app (right associativity, at level 60) : snoclist_scope.

Section Facts.

Variable A : Type.

(*
Theorem nil_snoc (x:A) (l:snoclist A) : [] <> l :: x.
Proof.
discriminate.
Qed.
*)

End Facts.
