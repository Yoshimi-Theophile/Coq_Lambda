Require Import Nat.
Require Import Snoclist.
Import SnoclistNotations.
Require Import PlanarLambda.
Require Import Types.

Require Import Coq.Program.Equality.
Require Import Arith.
Require Import Coq.Logic.JMeq.
Require List.

Definition context n : Type := snoclist type n.

Inductive is_typed : forall {a : nat}, context a -> pterm a -> type -> Prop :=
| typed_var ty : is_typed [ty] PVar ty
| typed_abs {n} ty1 gamma (pt : pterm (S n)) ty2 :
  is_typed (gamma :: ty1) pt ty2 -> is_typed gamma (PAbs pt) (TImp ty1 ty2)
| typed_app {n m} gamma delta (pt1 : pterm n) (pt2 : pterm m) ty1 ty2:
  is_typed gamma pt1 (TImp ty1 ty2) -> is_typed delta pt2 ty1 ->
  is_typed (gamma ++ delta) (PApp pt1 pt2) ty2.

(* ===== Substitution ===== *)

Definition s_rule : Type := nat * type.
Definition s_rules : Type := list s_rule.

Fixpoint subst1_ty (rul : s_rule) (ty : type) : type :=
match ty with
| TVar n => let (m, u) := rul in
  match eqb n m with
  | true => u
  | false => ty
  end
| TImp ty1 ty2 => TImp (subst1_ty rul ty1) (subst1_ty rul ty2)
end.

Fixpoint subst_ty (sigma : s_rules) (ty : type) : type :=
match sigma with
| List.nil => ty
| List.cons rul sigma' =>
  subst_ty sigma' (subst1_ty rul ty)
end.

Fixpoint subst1_ctx {n : nat} (rul : s_rule) (ctx : context n) : context n :=
match ctx with
| [] => []
| ctx' :: ty => (subst1_ctx rul ctx') :: (subst1_ty rul ty)
end.

Fixpoint subst_ctx {n : nat} (sigma : s_rules) (ctx : context n) : context n :=
match sigma with
| List.nil => ctx
| List.cons rul sigma' =>
  subst_ctx sigma' (subst1_ctx rul ctx)
end.


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

Import EqNotations.

Lemma pterm_JMeq_refl : forall {a : nat} (t : pterm a), pterm_JMeq t t.
Admitted.

Check eq_ind.

Lemma pt_ind : forall {n : nat} {x : pterm n} (P : forall {n' : nat}, pterm n' -> Prop),
  P x -> forall {m : nat} {y : pterm m}, n = m -> JMeq x y -> P y.
Admitted.

Lemma pt_JMeq : forall {a b : nat} (t1 : pterm a) (t2 : pterm b), JMeq t1 t2 <-> pterm_JMeq t1 t2.
Admitted.


Lemma subst1_typed : forall {n : nat} (rul : s_rule) (ctx : context n) (pt : pterm n) (ty : type),
  is_typed ctx pt ty -> is_typed (subst1_ctx rul ctx) pt (subst1_ty rul ty).
Proof.
intro n.
case_eq n.
- intro eq. intros rul ctx pt ty.
  dependent destruction ctx.
  case ty.
  case rul.
  + intros target ty' atom h.
    dependent destruction pt.
    dependent destruction h.
Admitted.

Lemma subst_typed : forall {n : nat} (sigma : s_rules) (ctx : context n) (pt : pterm n) (ty : type),
  is_typed ctx pt ty -> is_typed (subst_ctx sigma ctx) pt (subst_ty sigma ty).
Proof.
intros n sigma.
induction sigma.
- simpl. intros ctx pt ty h. apply h.
- simpl. intros ctx pt ty h. apply IHsigma. apply subst1_typed. apply h.
Qed.

Definition is_princ : Type := forall {n : nat} (ctx : context n) (pt : pterm n) (ty : type),
  is_typed ctx pt ty -> forall (ctx' : context n) (ty' : type), is_typed ctx' pt ty' ->
  sig (fun (sigma : s_rules) => ctx' = subst_ctx sigma ctx /\ ty' = subst_ty sigma ty).

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

(*
Inductive is_typed : forall {a : nat}, context a -> pterm a -> type -> Prop :=
| typed_var ty : is_typed [ty] PVar ty
| typed_abs {n} ty1 gamma (pt : pterm (S n)) ty2 :
  is_typed (gamma :: ty1) pt ty2 -> is_typed gamma (PAbs pt) (TImp ty1 ty2)
| typed_app {n m} gamma delta (pt1 : pterm n) (pt2 : pterm m) ty1 ty2:
  is_typed gamma pt1 (TImp ty1 ty2) -> is_typed delta pt2 ty1 ->
  is_typed (gamma ++ delta) (PApp pt1 pt2) ty2.
*)

Definition type_eq : Type := type * type.
Definition constraints : Type := list type_eq.

Inductive is_bidir_syn : forall {a : nat}, context a -> sterm a -> type -> constraints -> Prop :=
| bidir_abs {n} ty1 gamma (st : sterm (S n)) ty2 const :
  is_bidir_syn (gamma :: ty1) st ty2 const -> 
  is_bidir_syn  gamma (SAbs st) (TImp ty1 ty2) const
| bidir_cir {n} (a : nat) gamma (ct : cterm n) ty const :
  is_bidir_chk gamma ct ty const ->
  is_bidir_syn gamma (SCir a ct) ty const

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

(*
Lemma typed_lp : forall {a : nat} (ctx : context a) (lt : lterm a) (ty : type) (const : constraints),
  is_bidir ctx lt ty const -> is_typed ctx (strip_labels lt) ty.
Proof.
intros a ctx lt ty const.
induction lt.
induction s.
intro h.
case ty in h.
induction h.
- 
  case_eq ty.
  + admit.
  + simpl. apply 
*)

(* ===== Inference ===== *)






(*
Inductive b_synth : forall {a : nat} (newout : nat), context a -> pterm a -> type -> constraints -> Prop :=
| syn_var (ctx : context 1) :
  chk_test newout ctx PVar (S newout)
| syn_test ty : b_synth  0 [ty] PVar ty List.nil

with b_check : forall {a : nat} (newin : nat), context a -> pterm a -> type -> constraints -> Prop :=
| chk_test ty : b_check 0 [ty] PVar ty List.nil.
*)



(*
Fixpoint Bidir_synth {n : nat} (fresh : nat) (t : pterm n) : (nat * context n * type * constraints) :=
match t in pterm n return (nat * context n * type * constraints) with
| PAbs t' =>
  let (temp, const) := Bidir_synth fresh t' in
  let (temp', B) := temp in
  let (fresh', ctx') := temp' in
  match ctx' in snoclist _ (S n) return (nat * context n * type * constraints) with
  | ctx'' :: A => (fresh', ctx'', TImp A B, const)
  end
| PVar =>
  let (temp, const) := Bidir_check (S fresh) PVar (TVar fresh) in
  let (fresh', ctx') := temp in
  (fresh', ctx', (TVar fresh), const)
| PApp pt1 pt2 =>
  let (temp, const) := Bidir_check (S fresh) (PApp pt1 pt2) (TVar fresh) in
  let (fresh', ctx') := temp in
  (fresh', ctx', (TVar fresh), const)
end

with Bidir_check {n : nat} (fresh : nat) (t : pterm n) : type -> (nat * context n * constraints) :=
fix Bidir_check fresh t ty :=
match t in pterm n return (nat * context n * constraints) with
| PVar => (fresh, [ty], List.nil)
| PApp pt1 pt2 =>
  let (temp, const2) := Bidir_synth fresh pt2 in
  let (temp', A) := temp in
  let (fresh', ctx2) := temp' in
  let (temp, const1) := Bidir_check fresh' pt1 (TImp A ty) in
  let (fresh'', ctx1) := temp' in
  (fresh'', ctx1 ++ ctx2, List.app const1 const2)
| PAbs t' =>
  let (temp, const) := Bidir_synth fresh (PAbs t') in
  let (temp', A) := temp in
  let (fresh', ctx') := temp' in
  (fresh', ctx', List.cons (A, ty) const)
end.

*)














