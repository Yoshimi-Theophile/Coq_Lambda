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

Definition snoclist_npz {A : Type} {n : nat} (l : snoclist A n) : snoclist A (n + 0) :=
eq_rect n (snoclist A) l (n + 0) (eq_sym (Nat.add_0_r n)).

Definition snoclist_asso_1 {A : Type} {m n : nat} (l : snoclist A (S m + n)) : snoclist A (m + S n) :=
eq_rect (S m + n) (snoclist A) l (m + S n) (Nat.add_succ_comm m n).

Fixpoint app {A : Type} {m n : nat} (l : snoclist A m) (r : snoclist A n) :=
match r with
| [] => snoclist_npz l
| r' :: a => snoclist_asso_1 ((app l r') :: a)
end.

(*
with snoclist_npz {A : Type} {n : nat} (l : snoclist A n) : snoclist A (n + 0) :=
match l with
| [] => []
| l' :: a => snoclist_npz l' :: a
end

with snoclist_asso_1 {A : Type} {m n : nat} (l : snoclist A (S m + n)) : snoclist A (m + S n) :=
match l in (snoclist _ len) return (len <> 0) -> snoclist _ (m + S n) with
| [] => fun H => match H eq_refl with end
| l' :: a => fun _ => 
  match l' with
  | [] => aux l
  | _ => (snoclist_asso_1 l') :: a
  end
end Nat.neq_succ_0

with aux {A : Type} (l : snoclist A 1) : snoclist A (0 + 1) := l.
*)

Infix "++" := app (right associativity, at level 60) : snoclist_scope.

Section Facts.

Require Import Coq.Program.Equality.

Lemma zero_len : forall (A : Type) (l : snoclist A 0), l = [].
Proof.
intros A l.
dependent destruction l. reflexivity.
Qed.

Lemma nil_npz : forall {A : Type},
  snoclist_npz [] (A := A) = [].
Proof.
intro A.
rewrite zero_len with (l := snoclist_npz []).
reflexivity.
Qed.

Axiom snoc_npz : forall {A : Type} (n : nat) (l : snoclist A n) (a : A),
  snoclist_npz (l :: a) = (snoclist_npz l) :: a.

Lemma map_npz : forall {A : Type} (n : nat) (l : snoclist A n)
  (P : forall {n : nat}, snoclist A n -> snoclist A n)
  (f : A -> A),
  (forall {n : nat} (l : snoclist A n) (a : A), P (l :: a) = P l :: f a) ->
  P (snoclist_npz l) = snoclist_npz (P l).
Proof.
intros A n l P f h.
induction l.
- simpl.
  rewrite zero_len with (l := snoclist_npz []).
  rewrite zero_len with (l := snoclist_npz (P 0 [])).
  rewrite zero_len with (l := P 0 []).
  reflexivity.
- simpl.
  rewrite snoc_npz.
  rewrite ? h.
  rewrite snoc_npz.
  rewrite IHl.
  reflexivity.
Qed.

(* TODO *)
Axiom map_asso : forall {A : Type} (m n : nat) (l : snoclist A (S m + n))
  (P : forall {n : nat}, snoclist A n -> snoclist A n)
  (f : A -> A),
  (forall {n : nat} (l : snoclist A n) (a : A), P (l :: a) = P l :: f a) ->
  P (snoclist_asso_1 l) = snoclist_asso_1 (P l).

(*
Axiom P_npz : forall {A : Type} (n : nat) (l : snoclist A n)
  (P : forall {n : nat}, snoclist A n -> snoclist A n),
  P (snoclist_npz l) = snoclist_npz (P l).

Axiom P_asso : forall {A : Type} (m n : nat) (l : snoclist A (S m + n))
  (P : forall {n : nat}, snoclist A n -> snoclist A n),
  P (snoclist_asso_1 l) = snoclist_asso_1 (P l).
*)

Axiom sing_asso : forall {A : Type} (a : A),
  snoclist_asso_1 ([a]) (m := 0) (n := 0) = [a].

Axiom snoc_asso : forall {A : Type} (m n : nat) (l : snoclist A (S m + n)) (a : A),
  snoclist_asso_1 (l :: a) (m := (S m)) (n := n) =
  snoclist_asso_1 l :: a.

(*
Lemma map_asso : forall {A : Type} (m n : nat) (l : snoclist A (m + n)) (a : A)
  (P : forall {n : nat}, snoclist A n -> snoclist A n)
  (f : A -> A),
  (forall {n : nat} (l : snoclist A n) (a : A), P (l :: a) = P l :: f a) ->
  P (snoclist_asso_1 (l :: a)) = snoclist_asso_1 (P (l :: a)).
Proof.
intros A m n l a P f h.
dependent induction l.
- rewrite h.
  dependent destruction n.
  dependent destruction m.
  + simpl.
    simpl in l0.
    rewrite zero_len with (l := l0).
    rewrite zero_len with (l := P 0 []).
    rewrite ? sing_asso.
    rewrite h.
    rewrite zero_len with (l := P 0 []).
    reflexivity.
  + simpl in x0.
    apply eq_sym in x0.
    apply (Nat.neq_succ_0 (m + 0)) in x0.
    contradiction.
  + rewrite <- Nat.add_succ_comm in x0.
    simpl in x0.
    apply eq_sym in x0.
    apply (Nat.neq_succ_0 (m + n)) in x0.
    contradiction.
- rewrite h.
  dependent destruction n.
  dependent destruction m.
  + simpl in x0.
    apply (Nat.neq_succ_0 (n0)) in x0.
    contradiction.
  + rewrite snoc_asso.
*)



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
Prove some of those axioms maybe
Redefine sat_xi (subst ty1 = subst ty2)
x = y -> P x -> P y?
*)

(*
Fixpoint app {A : Type} {n m : nat} (l : snoclist A n) (r : snoclist A m) : snoclist A (n + m) :=
match r in (snoclist _ m) return (snoclist _ (m + n) -> snoclist _ (n + m)) -> snoclist _ (n + m) with
| nil => fun H => H l
| r' :: a => fun H => H ( snoclist_comm (app l r') :: a)
end snoclist_comm.
*)

(*
Lemma app_aux {A : Type} {m n : nat} :
match n with
| 0 => snoclist A m -> snoclist A (m + 0)
| S n => snoclist A (S m + n) -> snoclist A (m + S n)
end.
Proof.
destruct n.
apply snoclist_npz.
apply snoclist_asso_1.
Qed.

Fixpoint app {A : Type} {m n : nat} (l : snoclist A m) (r : snoclist A n) : snoclist A (m + n) :=
match r as r in (snoclist _ n) return
 (match n return Type with
  | 0 => (snoclist _ m -> snoclist _ (m + 0))
  | S n => (snoclist A (S m + n) -> snoclist A (m + S n))
  end) ->
  snoclist A (m + n)
with
| [] => fun H => H l
| r' :: a => fun H => H ((app l r') :: a)
end app_aux.
*)
