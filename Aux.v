
Require Import String.

Fixpoint sofn (n : nat) : string :=
match n with
| 0 => "0"
| S (S (S (S (S (S (S (S (S (S 0))))))))) => "X"
| S (S (S (S (S (S (S (S (S (S n))))))))) => "X" ++ sofn n
| S (S (S (S (S 0)))) => "V"
| S (S (S (S (S n)))) => "V" ++ sofn n
| S 0 => "i"
| S n => "i" ++ sofn n
end.

(*Require Import Coq.Logic.JMeq.*)

(*
Inductive pterm_JMeq : forall {a b : nat}, pterm a -> pterm b -> Prop :=
| JMeq_var : pterm_JMeq PVar PVar
| JMeq_abs {n m} (tl : pterm (S n)) (tr : pterm (S m)) :
  pterm_JMeq tl tr -> pterm_JMeq (PAbs tl) (PAbs tr)
| JMeq_app {nl nr ml mr} (tl1 : pterm nl) (tl2 : pterm ml) (tr1 : pterm nr) (tr2 : pterm mr) :
  pterm_JMeq tl1 tr1 -> pterm_JMeq tl2 tr2 -> pterm_JMeq (PApp tl1 tl2) (PApp tr1 tr2)
| JMeq_sym {n m} (tl : pterm n) (tr : pterm m) : pterm_JMeq tl tr -> pterm_JMeq tr tl
| JMeq_trans {n m p} (tl : pterm n) (tm : pterm m) (tr : pterm p) :
  pterm_JMeq tl tm -> pterm_JMeq tm tr -> pterm_JMeq tl tr
| JMeq_refl {n} (t : pterm n) : pterm_JMeq t t.

Lemma pterm_JMeq_is_eq : forall {a b : nat} (t1 : pterm a) (t2 : pterm b),
  pterm_JMeq t1 t2 -> a = b.
Proof. intros a b t1 t2 h.
induction h.
- reflexivity.
- apply (eq_add_S n m IHh).
- apply (f_equal2_plus nl nr ml mr IHh1 IHh2).
- apply (Nat.eq_sym IHh).
- apply (Nat.eq_trans IHh1 IHh2).
- reflexivity.
Qed.

Lemma pterm_JMeq_refl : forall {a : nat} (t : pterm a), pterm_JMeq t t.
Admitted.

Check eq_ind.

Lemma pt_ind : forall {n : nat} {x : pterm n} (P : forall {n' : nat}, pterm n' -> Prop),
  P x -> forall {m : nat} {y : pterm m}, n = m -> JMeq x y -> P y.
Admitted.

Lemma pt_JMeq : forall {a b : nat} (t1 : pterm a) (t2 : pterm b), JMeq t1 t2 <-> pterm_JMeq t1 t2.
Admitted.
*)

(*
Inductive pterm_eq : forall {a : nat}, pterm a -> pterm a -> Prop :=
| eq_var : pterm_eq PVar PVar
| eq_abs {n} (tl tr : pterm (S n)) :
  pterm_eq tl tr -> pterm_eq (PAbs tl) (PAbs tr)
| eq_app {n m} (tl1 : pterm n) (tl2 : pterm m) (tr1 : pterm n) (tr2 : pterm m) :
  pterm_eq tl1 tr1 -> pterm_eq tl2 tr2 -> pterm_eq (PApp tl1 tl2) (PApp tr1 tr2)
| eq_sym {n} (tl tr : pterm n) : pterm_eq tl tr -> pterm_eq tr tl
| eq_trans {n} (tl tm tr : pterm n) :
  pterm_eq tl tm -> pterm_eq tm tr -> pterm_eq tl tr.

Lemma pt_eq : forall {a : nat} (t1 t2 : pterm a), t1 = t2 <-> pterm_eq t1 t2.
Proof.
intros a t1 t2. split.
- intro eq. 
  induction t2.
  + rewrite eq. apply eq_var.
  + rewrite eq.
    apply (eq_abs t2 t2 (IHt2 t2 eq_refl)).
  + rewrite eq.
    apply (eq_app t2_1 t2_2 t2_1 t2_2 (IHt2_1 t2_1 eq_refl) (IHt2_2 t2_2 eq_refl)).
- intro pt_eq.
  induction pt_eq.
  + apply eq_refl.
  + rewrite IHpt_eq. apply eq_refl.
  + rewrite IHpt_eq1. rewrite IHpt_eq2. apply eq_refl.
  + rewrite IHpt_eq. apply eq_refl.
  + rewrite IHpt_eq1. rewrite IHpt_eq2. apply eq_refl.
Qed.
*)