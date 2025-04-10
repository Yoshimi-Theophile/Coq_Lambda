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

(* -- Unique -- *)


(*
Inductive not_FCV_syn : forall {n : nat}, nat -> sterm n -> Prop :=
| nFCV_abs st : not_FCV_syn st -> not_FCV_syn (SAbs st)
| nFCV_cir a ct : 
*)

(*
Inductive is_uniq_syn : forall {n : nat}, sterm n -> Prop :=
| uniq_abs st : is_uniq_syn st -> is_uniq_syn (SAbs st)
| uniq_cir a ct :
  is_uniq_chk ct ->
  (* not_FTV a ct -> *)
  is_uniq_syn (SCir a ct)

with is_uniq_chk : forall {n : nat}, cterm n -> Prop :=
| uniq_var : is_uniq_chk CVar
| uniq_app ct1 st2 :
  is_uniq_chk ct1 ->
  is_uniq_syn st2 ->
*)


Fixpoint uniq_circ_syn {n : nat} (t : sterm n) (a : nat) : (sterm n * nat) :=
match t with
| SAbs t' => 
  let (tnew, a') := uniq_circ_syn t' a in
  (SAbs tnew, a')
| SCir _ t' =>
  let (tnew, a') := uniq_circ_chk t' (S a) in
  (SCir a tnew, a')
end
with uniq_circ_chk {n : nat} (t : cterm n) (a : nat) : (cterm n * nat) :=
match t with
| CVar => (CVar, a)
| CApp t1 t2 =>
  let (tnew1, a1) := uniq_circ_chk t1 a in
  let (tnew2, a2) := uniq_circ_syn t2 a1 in
  (CApp tnew1 tnew2, a2)
| CSqu t' =>
  let (tnew, a') := uniq_circ_syn t' a in
  (CSqu tnew, a')
end.

Definition uniq_circ {n : nat} (t : lterm n) : lterm n :=
match t with
| LSyn st => let (res, _) := uniq_circ_syn st 0 in LSyn res
| LChk ct => let (res, _) := uniq_circ_chk ct 0 in LChk res
end.