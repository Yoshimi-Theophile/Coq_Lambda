
Inductive snoclist (A : Type) : Type :=
| nil : snoclist A
| snoc : snoclist A -> A -> snoclist A.

Arguments nil {A}.
Arguments snoc {A} l a.

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

Definition length {A : Type} : snoclist A -> nat :=
  fix length l :=
  match l with
   | nil => O
   | l' :: _ => S (length l')
  end.

Definition app {A : Type} : snoclist A -> snoclist A -> snoclist A :=
  fix app l m :=
  match m with
   | nil => l
   | m' :: a => app l m' :: a
  end.

Infix "++" := app (right associativity, at level 60) : snoclist_scope.

Section Facts.

Variable A : Type.

Theorem nil_snoc (x:A) (l:snoclist A) : [] <> l :: x.
Admitted.

End Facts.
