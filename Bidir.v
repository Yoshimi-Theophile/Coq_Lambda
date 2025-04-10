Require Import Snoclist.
Import SnoclistNotations.
Require Import Types.
Require Import Subst.
Require Import LabeledLambda.

Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require List.

Inductive sat_xi : s_rules -> constraints -> Prop :=
| sat_nil sigma : sat_xi sigma List.nil
| sat_cons sigma ty1 ty2 const :
  sat_xi sigma const ->
  subst_ty sigma ty1 = subst_ty sigma ty2 ->
  sat_xi sigma (List.cons (ty1, ty2) const).

(* -- taut -- *)

Inductive is_taut : constraints -> Prop :=
| taut_nil : is_taut List.nil
| taut_cons ty1 ty2 const :
  is_taut const -> ty1 = ty2 ->
  is_taut ((ty1, ty2) :: const)%list.

Lemma nil_sat_taut : forall (const : constraints),
  sat_xi List.nil const -> is_taut const.
Proof.
intros const h.
dependent induction h.
apply taut_nil.
simpl in H.
apply taut_cons.
apply IHh.
apply JMeq_refl.
apply H.
Qed.

Lemma taut_sat_xi : forall (sigma : s_rules) (const : constraints),
  is_taut const -> sat_xi sigma const.
Proof.
intros sigma const h.
induction h.
- apply sat_nil.
- rewrite H.
  apply sat_cons.
  apply IHh.
  reflexivity.
Qed.

(* -- *)

Lemma app_sat_xi : forall (sigma : s_rules) (const1 const2 : constraints),
  sat_xi sigma const1 -> sat_xi sigma const2 -> sat_xi sigma (const1 ++ const2)%list.
Proof.
intros sigma const1 const2 h1 h2.
induction const1.
- simpl. apply h2.
- simpl.
  dependent destruction h1.
  apply sat_cons.
  apply IHconst1.
  apply h1.
  apply H.
Qed.

Lemma perm_sat_xi : forall (sigma : s_rules) (const1 const2 : constraints),
  Permutation const1 const2 -> sat_xi sigma const1 -> sat_xi sigma const2.
Proof.
intros sigma const1 const2 hp.
induction hp.
- intro hs. apply hs.
- case x. intros ty1 ty2.
  intro hs. dependent destruction hs.
  apply sat_cons.
  + apply IHhp. apply hs.
  + apply H.
- case x. intros ty1 ty2.
  case y. intros ty1' ty2'.
  intro hs.
  dependent destruction hs.
  dependent destruction hs.
  apply sat_cons. apply sat_cons.
  + apply hs.
  + apply H0.
  + apply H.
- intro hl.
  apply IHhp2.
  apply IHhp1.
  apply hl.
Qed.

Lemma extra_sat_xi : forall (sigma : s_rules) (x : type_eq) (const : constraints),
  sat_xi sigma (x :: const)%list -> sat_xi sigma const.
Proof. intros. dependent destruction H. apply H. Qed.

Lemma split_sat_xi : forall (sigma : s_rules) (const1 const2 : constraints),
  sat_xi sigma (const1 ++ const2)%list -> sat_xi sigma const1 /\ sat_xi sigma const2.
Proof.
intros.
split.
---
induction const2.
- rewrite List.app_nil_r in H.
  apply H.
- apply IHconst2.
  assert (sat_xi sigma (a :: const1 ++ const2)%list).
  apply perm_sat_xi with (const1 := (const1 ++ a :: const2)%list).
  apply Permutation_sym.
  apply Permutation_middle.
  apply H.
  apply extra_sat_xi with (x := a).
  apply H0.
---
induction const1; simpl in H.
- apply H.
- apply IHconst1.
  apply extra_sat_xi with (x := a).
  apply H.
Qed.

Lemma appleft_sat_xi : forall (sigma : s_rules) (const1 const2 : constraints),
  sat_xi sigma (List.app const1 const2) -> sat_xi sigma const1.
Proof.
induction const2.
- rewrite List.app_nil_r. intro h. apply h.
- intro h. apply IHconst2.
  assert (Permutation (const1 ++ a :: const2)%list (a :: (const1 ++ const2))%list).
  apply (Permutation_sym (Permutation_cons_app
    (l := (const1 ++ const2)) const1 const2 a
    (Permutation_refl (const1 ++ const2)))).
  assert (sat_xi sigma (a :: const1 ++ const2)%list).
  apply perm_sat_xi with (const1 := (const1 ++ a :: const2)%list).
  apply H. apply h.
  apply extra_sat_xi with (x := a).
  apply H0.
Qed.

Lemma appright_sat_xi : forall (sigma : s_rules) (const1 const2 : constraints),
  sat_xi sigma (List.app const1 const2) -> sat_xi sigma const2.
Proof.
induction const1.
- simpl. intros const2 h. apply h.
- intros const2 h. apply IHconst1.
  simpl in h.
  apply extra_sat_xi with (x := a).
  apply h.
Qed.

(* ===== *)

Definition is_mgu (sigma : s_rules) (const : constraints) : Prop :=
  sat_xi sigma const /\
  forall (sigma' : s_rules),
    sat_xi sigma' const ->
    exists (tau : s_rules),
      forall (ty : type),
        subst_ty sigma' ty = subst_ty tau (subst_ty sigma ty).

(* -- bidir -- *)

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

Theorem bidir_typed_syn :
  forall {n : nat} (gamma : context n) (st : sterm n) (ty : type) (const : constraints) (sigma : s_rules),
  is_bidir_syn gamma st ty const ->
  sat_xi sigma const ->
  is_typed (subst_ctx sigma gamma) (strip_syn st) (subst_ty sigma ty)

with bidir_typed_chk :
  forall {n : nat} (gamma : context n) (ct : cterm n) (ty : type) (const : constraints) (sigma : s_rules),
  is_bidir_chk gamma ct ty const ->
  sat_xi sigma const ->
  is_typed (subst_ctx sigma gamma) (strip_chk ct) (subst_ty sigma ty).

Proof.
- intros n gamma st ty const sigma hb hs.
  induction hb.
  + simpl.
    rewrite dist_subst_ty.
    apply typed_abs.
    rewrite <- cons_subst_ctx.
    apply IHhb. apply hs.
  + simpl.
    apply bidir_typed_chk
    with (const := const).
    apply H. apply hs.
- intros n gamma ct ty const sigma hb hs.
  induction hb.
  + simpl.
    rewrite single_subst_ctx.
    apply (typed_var (subst_ty sigma ty)).
  + simpl.
    rewrite app_subst_ctx.
    apply typed_app
    with (ty1 := (subst_ty sigma ty1)).
    * rewrite <- dist_subst_ty.
      apply IHhb.
      apply appleft_sat_xi
      with (const2 := const2).
      apply hs.
    * apply bidir_typed_syn
      with (const := const2).
      apply H.
      apply appright_sat_xi
      with (const1 := const1).
      apply hs.
  + simpl.
    dependent destruction hs.
    rewrite <- H0.
    apply bidir_typed_syn
    with (const := const).
    apply H. apply hs.
Qed.

(* -- inter -- *)

Inductive is_inter_syn : forall {a : nat}, context a -> sterm a -> type -> Prop :=
| inter_abs {n} ty1 gamma (st : sterm (S n)) ty2 :
  is_inter_syn (gamma :: ty1) st ty2 -> 
  is_inter_syn  gamma (SAbs st) (TImp ty1 ty2)
| inter_cir {n} (a : nat) gamma (ct : cterm n) sigma :
  is_inter_chk gamma ct (TVar a) sigma ->
  is_inter_syn (subst_ctx sigma gamma) (SCir a ct) (subst_ty sigma (TVar a))

with is_inter_chk : forall {a : nat}, context a -> cterm a -> type -> s_rules -> Prop :=
| inter_var ty : is_inter_chk [ty] CVar ty List.nil
| inter_app {n m} gamma delta (ct1 : cterm n) (st2 : sterm m) ty1 ty2 sigma :
  is_inter_chk gamma ct1 (TImp ty1 ty2) sigma ->
  is_inter_syn delta st2 ty1 ->
  is_inter_chk (gamma ++ delta) (CApp ct1 st2) ty2 sigma
| inter_squ {n} gamma (st : sterm n) ty1 ty2 sigma :
  is_inter_syn gamma st ty1 ->
  is_mgu sigma ((ty1, ty2) :: List.nil)%list ->
  is_inter_chk gamma (CSqu st) ty2 sigma.

Inductive is_inter : forall {a : nat}, context a -> lterm a -> type -> Prop :=
| Sinter {n} gamma (st : sterm n) ty :
  is_inter_syn gamma st ty ->
  is_inter gamma (LSyn st) ty
| Cinter {n} gamma (ct : cterm n) ty :
  is_inter_chk gamma ct ty List.nil ->
  is_inter gamma (LChk ct) ty.

Theorem inter_typed_syn :
  forall {n : nat} (gamma : context n) (st : sterm n) (ty : type),
  is_inter_syn gamma st ty ->
  is_typed gamma (strip_syn st) ty

with inter_typed_chk :
  forall {n : nat} (gamma : context n) (ct : cterm n) (ty : type) (sigma : s_rules),
  is_inter_chk gamma ct ty sigma ->
  is_typed (subst_ctx sigma gamma) (strip_chk ct) (subst_ty sigma ty).

Proof.
- intros n gamma st ty h.
  induction h.
  + simpl.
    apply typed_abs.
    apply IHh.
  + simpl.
    apply inter_typed_chk.
    apply H.
- intros n gamma st ty sigma h.
  induction h.
  + simpl. apply typed_var.
  + simpl.
    rewrite app_subst_ctx.
    apply typed_app with (ty1 := subst_ty sigma ty1).
    * rewrite <- dist_subst_ty.
      apply IHh.
    * apply subst_typed.
      apply inter_typed_syn.
      apply H.
  + simpl.
    destruct H0.
    dependent destruction H0.
    rewrite <- H1.
    apply subst_typed.
    apply inter_typed_syn.
    apply H.
Qed.
































