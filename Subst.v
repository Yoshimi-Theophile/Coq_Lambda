Require Import Nat.
Require Import Snoclist.
Import SnoclistNotations.
Require Import PlanarLambda.
Require Import Types.

Require Import Coq.Program.Equality.
Require Import Arith.
Require List.

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

Fixpoint subst1_ctx (rul : s_rule) {n : nat} (ctx : context n) : context n :=
match ctx with
| [] => []
| ctx' :: ty => (subst1_ctx rul ctx') :: (subst1_ty rul ty)
end.

Fixpoint subst_ctx (sigma : s_rules) {n : nat} (ctx : context n) : context n :=
match sigma with
| List.nil => ctx
| List.cons rul sigma' =>
  subst_ctx sigma' (subst1_ctx rul ctx)
end.

(* Lemmas *)

Lemma subst_asso : forall {m n : nat} (rul : s_rule) (ctx : context (S m + n)),
  subst1_ctx rul (snoclist_asso_1 ctx) = 
  snoclist_asso_1 (subst1_ctx rul ctx).
Proof. intros m n rul ctx. apply P_asso. Qed.

Lemma app_subst1_ctx : forall {n m : nat} (rul : s_rule) (ctx1 : context n) (ctx2 : context m),
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
    rewrite ? comm_appnil.
    simpl. rewrite IHctx1.
    reflexivity.
  + simpl.
    rewrite ? comm_consapp_asso'.
    simpl in IHctx1.
    rewrite ? comm_consapp_asso in IHctx1.
    assert (
      subst1_ctx rul (snoclist_asso_1 ((ctx1 ++ ctx2) :: a0)) = 
      snoclist_asso_1 (subst1_ctx rul ((ctx1 ++ ctx2) :: a0))
    ) by apply subst_asso.
    rewrite H in IHctx1. simpl in IHctx1.
    assert (
      subst1_ctx rul (ctx1 ++ ctx2) =
      subst1_ctx rul ctx1 ++ subst1_ctx rul ctx2
    ).
    apply snoc_eq with (a := subst1_ty rul a0).
    apply asso_eq. apply IHctx1.
    simpl.
    assert (
      subst1_ctx rul (snoclist_asso_1 ((ctx1 :: a) ++ ctx2)) = 
      snoclist_asso_1 (subst1_ctx rul ((ctx1 :: a) ++ ctx2))
    ) by apply subst_asso.
    rewrite H1.
    assert (
      subst1_ctx rul ((ctx1 :: a) ++ ctx2) =
      (subst1_ctx rul ctx1 :: subst1_ty rul a) ++ subst1_ctx rul ctx2
    ) by (apply IHctx2; apply H0).
    rewrite H2. reflexivity.
Qed.

Lemma dist_subst1_ty : forall (rul : s_rule) (ty1 ty2 : type),
  subst1_ty rul (TImp ty1 ty2) = TImp (subst1_ty rul ty1) (subst1_ty rul ty2).
Proof. simpl. reflexivity. Qed.

Lemma dist_subst_ty : forall (sigma : s_rules) (ty1 ty2 : type),
  subst_ty sigma (TImp ty1 ty2) = TImp (subst_ty sigma ty1) (subst_ty sigma ty2).
Proof.
intro sigma. induction sigma.
- simpl. reflexivity.
- simpl. intros. apply IHsigma.
Qed.

Lemma cons_subst_ctx : forall {n : nat} (sigma : s_rules) (gamma : context n) (ty : type),
  subst_ctx sigma (gamma :: ty) =
  subst_ctx sigma gamma :: subst_ty sigma ty.
Proof.
intros n sigma. induction sigma.
- simpl. reflexivity.
- simpl. intros gamma ty. apply IHsigma.
Qed.

Lemma single_subst_ctx : forall (sigma : s_rules) (ty : type),
  subst_ctx sigma [ty] = [subst_ty sigma ty].
Proof.
intro sigma. induction sigma.
- simpl. reflexivity.
- simpl. intros ty. apply IHsigma.
Qed.

Lemma app_subst_ctx : forall {m n : nat} (sigma : s_rules) (ctx1 : context n) (ctx2 : context m),
  subst_ctx sigma (ctx1 ++ ctx2) = subst_ctx sigma ctx1 ++ subst_ctx sigma ctx2.
Proof.
intros m n sigma. induction sigma.
- simpl. reflexivity.
- simpl. intros ctx1 ctx2.
  rewrite app_subst1_ctx.
  apply IHsigma.
Qed.

(* Typing *)

Lemma subst1_typed : forall {n : nat} (rul : s_rule) (ctx : context n) (pt : pterm n) (ty : type),
  is_typed ctx pt ty -> is_typed (subst1_ctx rul ctx) pt (subst1_ty rul ty).
Proof.
intro n.
intros rul ctx pt ty h.
induction h.
- simpl. apply typed_var.
- simpl. apply typed_abs. simpl in IHh. apply IHh.
- rewrite app_subst1_ctx.
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