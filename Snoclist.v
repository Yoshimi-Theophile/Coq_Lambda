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

Theorem snoclist_comm {A : Type} {n m : nat} : snoclist A (m + n) -> snoclist A (n + m).
Proof. rewrite Nat.add_comm. intro h. apply h. Qed.

Theorem snoclist_asso_1 {A : Type} {n m : nat} : snoclist A (S m + n) -> snoclist A (m + S n).
Proof. rewrite Nat.add_succ_comm. intro h. apply h. Qed.

(*
Theorem snoclist_nil {A : Type} {m : nat} : snoclist A (m + 0) -> snoclist A m.
Proof. rewrite Nat.add_comm. intro h. apply h. Qed.

Fixpoint app {A : Type} {n m : nat} (l : snoclist A n) (r : snoclist A m) : snoclist A (n + m) :=
match r in (snoclist _ m) return (snoclist _ (m + n) -> snoclist _ (n + m)) -> snoclist _ (n + m) with
| nil => fun H => H l
| r' :: a => fun _ => (app l r') :: a
end snoclist_nil.
*)

Fixpoint app {A : Type} {n m : nat} (l : snoclist A n) (r : snoclist A m) : snoclist A (n + m) :=
match r in (snoclist _ m) return (snoclist _ (m + n) -> snoclist _ (n + m)) -> snoclist _ (n + m) with
| nil => fun H => H l
| r' :: a => fun H => H ( snoclist_comm (app l r') :: a)
end snoclist_comm.

Infix "++" := app (right associativity, at level 60) : snoclist_scope.

Section Facts.

Require Import Coq.Program.Equality.

Lemma zero_len : forall (A : Type) (l : snoclist A 0), l = [].
Proof.
intros A l.
dependent destruction l. reflexivity.
Qed.

Lemma comm_nil : forall (A : Type), snoclist_comm [] (A := A) (m := 0) (n := 0) = [].
Proof.
intro A. rewrite zero_len with (l := snoclist_comm [] (m := 0) (n := 0)).
reflexivity.
Qed.

Axiom comm_appnil : forall (A : Type) (n : nat) (l : snoclist A n) (a : A),
  snoclist_comm (l :: a) (m := 0) (n := S n) = snoclist_comm l (m := 0) (n := n) :: a.

Axiom comm_nilapp : forall (A : Type) (n : nat) (l : snoclist A n) (a : A),
  snoclist_comm (snoclist_comm ([] ++ l) :: a) (m := S n) (n := 0) = l :: a.

Axiom comm_consapp_asso : forall (A : Type) (m n : nat) (l : snoclist A m) (r : snoclist A n) (a : A),
  snoclist_comm (snoclist_comm (l ++ r) (m := m) (n := n) :: a) (m := S n) (n := m) =
  snoclist_asso_1 ((l ++ r) :: a).

Axiom comm_consapp_asso' : forall (A : Type) (m n : nat) (l : snoclist A m) (r : snoclist A n) (a b : A),
  snoclist_comm (snoclist_comm ((l :: a) ++ r) (m := S m) (n := n) :: b) (m := S n) (n := S m) =
  snoclist_asso_1 ((l :: a) ++ r) :: b.

Axiom asso_eq : forall {A : Type} {m n : nat} (l1 l2 : snoclist A (S m + n)),
  snoclist_asso_1 l1 (m := m) (n := n) = snoclist_asso_1 l2 (m := m) (n := n) -> l1 = l2.

Axiom P_asso : forall {A : Type} (m n : nat) (l : snoclist A (S m + n))
  (P : forall {n : nat}, snoclist A n -> snoclist A n),
  P (snoclist_asso_1 l) = snoclist_asso_1 (P l).

Axiom P_comm : forall {A : Type} (m n : nat) (l : snoclist A (m + n))
  (P : forall {n : nat}, snoclist A n -> snoclist A n),
  P (snoclist_comm l) = snoclist_comm (P l).

End Facts.

(* Lemmas *)

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

Lemma snoc_eq : forall {A : Type} {n : nat} (l1 l2 : snoclist A n) (a : A),
  l1 :: a = l2 :: a -> l1 = l2.
Proof.
intros A n l1 l2 a eq.
inversion eq.
apply inj_pair2_eq_dec in H0.
- apply H0.
- apply eq_nat_dec.
Qed.

(*
Redefine app
Prove some of those axioms maybe
Redefine sat_xi (subst ty1 = subst ty2)
x = y -> P x -> P y?
*)


