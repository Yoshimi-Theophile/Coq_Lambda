Require Import PlanarLambda.

(* ===== Labeled Terms ===== *)

Inductive sterm : nat -> Type :=
| SAbs {n} : sterm (S n) -> sterm n
| SCir {n} : nat -> cterm n -> sterm n

with cterm : nat -> Type :=
| CVar : cterm 1
| CApp {n} {m} : cterm n -> sterm m -> cterm (n + m)
| CSqu {n} : sterm n -> cterm n.

Inductive lterm : nat -> Type :=
| LSyn {n} : sterm n -> lterm n
| LChk {n} : cterm n -> lterm n.

(* -- Strip -- *)

Fixpoint strip_syn {n : nat} (t : sterm n) : pterm n :=
match t with
| SAbs t' => PAbs (strip_syn t')
| SCir a t' => strip_chk t'
end
with strip_chk {n : nat} (t : cterm n) : pterm n :=
match t with
| CVar => PVar
| CApp ct st => PApp (strip_chk ct) (strip_syn st)
| CSqu t' => strip_syn t'
end.

Definition strip_labels {n : nat} (t : lterm n) : pterm n :=
match t with
| LSyn st => strip_syn st
| LChk ct => strip_chk ct
end.

(* -- Label -- *)

Fixpoint label_minus {n : nat} (t : pterm n) : sterm n :=
match t with
| PVar => SCir 0 CVar
| PAbs t' => SAbs (label_minus t')
| PApp t1 t2 => SCir 0 (CApp (CSqu (label_minus t1)) (label_minus t2))
end.

Fixpoint label_plus {n : nat} (t : pterm n) : cterm n :=
match t with
| PVar => CVar
| PAbs t' => CSqu (SAbs (SCir 0 (label_plus t')))
| PApp t1 t2 => CApp (label_plus t1) (SCir 0 (label_plus t2))
end.

Lemma label_strip_minus : forall {n : nat} (t : pterm n), strip_syn (label_minus t) = t.
Proof.
intros n t. induction t.
- simpl. reflexivity.
- simpl. rewrite IHt. reflexivity.
- simpl. rewrite IHt1. rewrite IHt2. reflexivity.
Qed.

Lemma label_strip_plus : forall {n : nat} (t : pterm n), strip_chk (label_plus t) = t.
Proof.
intros n t. induction t.
- simpl. reflexivity.
- simpl. rewrite IHt. reflexivity.
- simpl. rewrite IHt1. rewrite IHt2. reflexivity.
Qed.