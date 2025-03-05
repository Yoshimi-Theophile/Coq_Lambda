Require Import Nat.
Require Import Snoclist.
Import SnoclistNotations.
Require Import PlanarLambda.
Require Import Types.

Require Import Coq.Program.Equality.
Require Import Arith.
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

(*
Axiom comm_comm : forall {A : Type} {n : nat} (l : snoclist A n),
  snoclist_comm (l ++ []) = l.
*)

Axiom comm_nil : forall (A : Type), snoclist_comm [] (A := A) (m := 0) (n := 0) = [].

Axiom comm_cons : forall (A : Type) (n : nat) (l : snoclist A n) (a : A),
  snoclist_comm (l :: a) (m := 0) (n := S n) = snoclist_comm l (m := 0) (n := n) :: a.

(*
Axiom comm_cons' : forall (A : Type) (m n : nat) (l : snoclist A (m + n)) (a : A),
  snoclist_comm (l :: a) (m := 0) (n := S m + n) = snoclist_comm l (m := 0) (n := m + n) :: a.

Axiom comm_comm_cons : forall (A : Type) (m n : nat) (l : snoclist A (m + n)) (a : A),
  snoclist_comm (snoclist_comm l (m := m) (n := n) :: a) (m := 0) (n := S n + m) =
  snoclist_comm (snoclist_comm l (m := m) (n := n)) (m := 0) (n := n + m) :: a.
*)

Axiom comm_nilapp : forall (A : Type) (n : nat) (l : snoclist A n) (a : A),
  snoclist_comm (snoclist_comm ([] ++ l) :: a) (m := S n) (n := 0) = l :: a.

Axiom comm_consapp : forall (A : Type) (m n : nat) (l : snoclist A m) (r : snoclist A n) (a : A),
  snoclist_comm (snoclist_comm (l ++ r) (m := m) (n := n) :: a) (m := S n) (n := m) =
  l ++ r :: a.

(*
Lemma comm_nilapp : forall (A : Type) (n : nat) (l : snoclist A n) (a : A),
  snoclist_comm ((snoclist_comm ([] ++ l)) :: a) (m := S n) (n := 0) = l :: a.
Proof.
intros A n l a.
induction l.
- rewrite comm_cons' with (l := snoclist_comm ([] ++ [])) (a := a).
*)

Lemma subst_ctx_app : forall {n m : nat} (rul : s_rule) (ctx1 : context n) (ctx2 : context m),
  subst1_ctx rul (ctx1 ++ ctx2) = subst1_ctx rul ctx1 ++ subst1_ctx rul ctx2.
Proof.
intros n m rul ctx1 ctx2.
induction ctx1.
- simpl. induction ctx2.
  + simpl.
    rewrite comm_nil.
    simpl. reflexivity.
  + simpl.
    rewrite ? comm_nilapp.
    simpl. reflexivity.
- simpl. induction ctx2.
  + simpl in IHctx1. simpl.
    rewrite ? comm_cons.
    simpl. rewrite IHctx1.
    reflexivity.
  + simpl in IHctx1.
    rewrite ? comm_consapp in IHctx1.
    
    simpl.
    rewrite ? comm_consapp.

    
    

Admitted.

Lemma subst1_typed : forall {n : nat} (rul : s_rule) (ctx : context n) (pt : pterm n) (ty : type),
  is_typed ctx pt ty -> is_typed (subst1_ctx rul ctx) pt (subst1_ty rul ty).
Proof.
intro n.
intros rul ctx pt ty h.
induction h.
- simpl. apply typed_var.
- simpl. apply typed_abs. simpl in IHh. apply IHh.
- rewrite subst_ctx_app.
  apply typed_app with (ty1 := subst1_ty rul ty1).
  simpl in IHh1. apply IHh1. apply IHh2.
Qed.

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



Definition type_eq : Type := type * type.
Definition constraints : Type := list type_eq.

Inductive is_bidir_syn : forall {a : nat}, context a -> sterm a -> type -> constraints -> Prop :=
| bidir_abs {n} ty1 gamma (st : sterm (S n)) ty2 const :
  is_bidir_syn (gamma :: ty1) st ty2 const -> 
  is_bidir_syn  gamma (SAbs st) (TImp ty1 ty2) const
| bidir_cir {n} (a : nat) gamma (ct : cterm n) const :
  is_bidir_chk gamma ct (TVar a) const ->
  is_bidir_syn gamma (SCir a ct) (TVar a) const

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
intros a ctx lt ty const h.
induction h.
induction H.
- Admitted.
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














