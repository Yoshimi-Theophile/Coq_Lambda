Require Import Nat.
Require Import Snoclist.
Import SnoclistNotations.
Require Import PlanarLambda.
Require Import Types.

Require Import Subst.
Require Import LabeledLambda.
Require Import Bidir.

Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Arith.
Require List.

Inductive good_rule : s_rule -> Prop :=
| good_id a : good_rule (a, TVar a)
| good_nFTV a ty :
  not_FTV a ty ->
  good_rule (a, ty).

Inductive good_rules : s_rules -> Prop :=
| good_nil : good_rules List.nil
| good_cons rul sigma :
  good_rule rul ->
  good_rules sigma ->
  good_rules (rul :: sigma)%list.

Lemma good_app : forall (sigma1 sigma2 : s_rules),
  good_rules sigma1 -> good_rules sigma2 -> good_rules (sigma1 ++ sigma2)%list.
Proof.
intros sigma1 sigma2 h1 h2.
induction h1.
- simpl. apply h2.
- simpl. apply good_cons.
  apply H. apply IHh1.
Qed.

Lemma subst1_ty_nFTV : forall (a : nat) (ty ty' : type),
  not_FTV a ty -> subst1_ty (a, ty') ty = ty.
Proof.
intros a ty ty' h.
induction h.
- simpl.
  case_eq (b =? a).
  + intro eq. apply Nat.eqb_eq in eq.
    apply eq_sym in eq. apply H in eq.
    contradiction.
  + reflexivity.
- simpl.
  rewrite IHh1.
  rewrite IHh2.
  reflexivity.
Qed.

Lemma subst1_ty_idem : forall (rul : s_rule) (ty : type),
  good_rule rul ->
  subst1_ty rul (subst1_ty rul ty) = subst1_ty rul ty.
Proof.
intros rul ty h.
induction h; induction ty.
- simpl.
  case_eq (n =? a); intro eq; simpl.
  + case_eq (a =? a); reflexivity.
  + rewrite eq. reflexivity.
- simpl. rewrite IHty1. rewrite IHty2.
  reflexivity.
- simpl.
  case_eq (n =? a); intro eq.
  + apply subst1_ty_nFTV.
    apply H.
  + simpl. rewrite eq.
    reflexivity.
- simpl.
  rewrite IHty1.
  rewrite IHty2.
  reflexivity.
Qed.

Lemma subst1_ty_id : forall (a : nat) (ty : type),
  good_rule (a, ty) ->
  ty = subst1_ty (a, ty) ty.
Proof.
intros a ty h.
dependent induction h.
- simpl. case (a =? a); reflexivity.
- rewrite subst1_ty_nFTV. reflexivity.
  apply H.
Qed.

Lemma subst1_const_nil : forall (rul : s_rule) (const : constraints),
  subst1_const rul const = List.nil ->
  const = List.nil.
Proof.
intros rul const h.
induction const.
- reflexivity.
- assert
  (List.length (subst1_const rul (a :: const)%list) =
   List.length Datatypes.nil (A := type_eq)).
  rewrite h. reflexivity.
  destruct a.
  simpl in H.
  discriminate.
Qed.

Lemma subst_sat_xi : forall (sigma : s_rules) (const : constraints) (a : nat) (ty : type),
  sat_xi sigma (subst1_const (a, ty) const) ->
  sat_xi ((a, ty) :: sigma)%list const.
Proof.
intros sigma const a ty h.
induction const.
- apply sat_nil.
- destruct a0. apply sat_cons.
  + apply IHconst.
    apply extra_sat_xi with
    (x := (subst1_ty (a, ty) t, subst1_ty (a, ty) t0)).
    simpl in h. apply h.
  + simpl.
    simpl in h.
    dependent destruction h.
    apply H.
Qed.

(* -- Build -- *)

Inductive build_subst : s_rules -> constraints -> Prop :=
| build_nil : build_subst List.nil List.nil
| build_consleft sigma const a ty :
  build_subst sigma (subst1_const (a, ty) const) ->
  build_subst ((a, ty) :: sigma)%list ((TVar a, ty) :: const)%list
| build_consright sigma const b ty :
  build_subst sigma (subst1_const (b, ty) const) ->
  build_subst ((b, ty) :: sigma)%list ((ty, TVar b) :: const)%list
| build_consimp rul sigma const tyA tyB tyC tyD :
  build_subst (rul :: sigma)%list ((tyC, tyA) :: (tyB, tyD) :: const)%list ->
  build_subst (rul :: sigma)%list ((TImp tyA tyB, TImp tyC tyD) :: const)%list.

Lemma build_sat : forall (sigma : s_rules) (const : constraints),
  build_subst sigma const ->
  good_rules sigma ->
  sat_xi sigma const.
Proof.
intros sigma const h good.
induction h.
- apply sat_nil.
- dependent destruction good.
  apply sat_cons.
  + apply subst_sat_xi.
    apply IHh. apply good.
  + dependent destruction H.
* reflexivity.
* simpl.
  case_eq (a =? a); intro eq.
  -- rewrite <- subst1_ty_id.
     reflexivity.
     apply good_nFTV. apply H.
  -- rewrite Nat.eqb_refl in eq.
     apply Bool.diff_true_false in eq.
     contradiction.
- dependent destruction good.
  apply sat_cons.
  + apply subst_sat_xi.
    apply IHh. apply good.
  + dependent destruction H.
* reflexivity.
* simpl.
  case_eq (b =? b); intro eq.
  -- rewrite <- subst1_ty_id.
     reflexivity.
     apply good_nFTV. apply H.
  -- rewrite Nat.eqb_refl in eq.
     apply Bool.diff_true_false in eq.
     contradiction.
- assert (sat_xi (rul :: sigma)%list ((tyC, tyA) :: (tyB, tyD) :: const)%list).
  apply IHh. apply good.
  apply sat_cons.
  + apply extra_sat_xi with (x := (tyB, tyD)).
    apply extra_sat_xi with (x := (tyC, tyA)).
    apply H.
  + dependent destruction H.
    dependent destruction H.
    rewrite ? dist_subst_ty.
    rewrite H0. rewrite H1.
    reflexivity.
Qed.

(* Bidir *)

Axiom cons_inj : forall {A : Type} (a1 a2 : A) (l1 l2 : list A),
  (a1 :: l1)%list = (a2 :: l2)%list ->
  a1 = a2 /\ l1 = l2.

Lemma build_app : forall (const1 const2 : constraints) (sigma : s_rules) ,
  build_subst sigma (const1 ++ const2)%list ->
  exists sigma1 sigma2: s_rules,
  build_subst sigma1 const1 /\
  build_subst sigma2 (subst_const sigma1 const2) /\
  sigma = (sigma1 ++ sigma2)%list.
Proof.
intros.
dependent induction H.
--
dependent destruction const1; simpl in x.
- exists List.nil. exists List.nil.
  rewrite <- x. simpl.
  split. apply build_nil.
  split. apply build_nil.
  reflexivity.
- discriminate.
--
dependent destruction const1;
dependent destruction const2.
- simpl in x. discriminate.
- simpl in x.
  exists List.nil. simpl.
  exists ((a, ty) :: sigma)%list.
  split. apply build_nil.
  split. rewrite <- x.
  apply build_consleft. apply H.
  reflexivity.
- rewrite List.app_nil_r in x.
  exists ((a, ty) :: sigma)%list.
  exists List.nil. simpl. rewrite List.app_nil_r.
  split. rewrite <- x.
  apply build_consleft. apply H.
  split. rewrite subst_const_nil. apply build_nil.
  reflexivity.
- simpl in x. apply cons_inj in x. destruct x.
  assert (
    exists sigma1 sigma2 : s_rules,
    build_subst sigma1 (subst1_const (a, ty) const1) /\
    build_subst sigma2 (subst_const sigma1 (subst1_const (a, ty) (t0 :: const2)%list)) /\
    sigma = (sigma1 ++ sigma2)%list
  ). apply IHbuild_subst.
  rewrite <- app_subst1_const.
  rewrite <- H1.
  apply JMeq_refl.
  destruct H2. destruct H2.
  exists ((a, ty) :: x)%list.
  exists x0.
  split. rewrite <- H0.
  apply build_consleft. apply H2.
  split. rewrite <- step_subst_const. apply H2.
  simpl. destruct H2. destruct H3. rewrite H4.
  reflexivity.
--
dependent destruction const1;
dependent destruction const2.
- simpl in x. discriminate.
- simpl in x.
  exists List.nil. simpl.
  exists ((b, ty) :: sigma)%list.
  split. apply build_nil.
  split. rewrite <- x.
  apply build_consright. apply H.
  reflexivity.
- rewrite List.app_nil_r in x.
  exists ((b, ty) :: sigma)%list.
  exists List.nil. simpl. rewrite List.app_nil_r.
  split. rewrite <- x.
  apply build_consright. apply H.
  split. rewrite subst_const_nil. apply build_nil.
  reflexivity.
- simpl in x. apply cons_inj in x. destruct x.
  assert (
    exists sigma1 sigma2 : s_rules,
    build_subst sigma1 (subst1_const (b, ty) const1) /\
    build_subst sigma2 (subst_const sigma1 (subst1_const (b, ty) (t0 :: const2)%list)) /\
    sigma = (sigma1 ++ sigma2)%list
  ). apply IHbuild_subst.
  rewrite <- app_subst1_const.
  rewrite <- H1.
  apply JMeq_refl.
  destruct H2. destruct H2.
  exists ((b, ty) :: x)%list.
  exists x0.
  split. rewrite <- H0.
  apply build_consright. apply H2.
  split. rewrite <- step_subst_const. apply H2.
  simpl. destruct H2. destruct H3. rewrite H4.
  reflexivity.
--
dependent destruction const1;
dependent destruction const2.
- simpl in x. discriminate.
- simpl in x.
  exists List.nil. simpl.
  exists (rul :: sigma)%list.
  split. apply build_nil.
  split. rewrite <- x.
  apply build_consimp. apply H.
  reflexivity.
- rewrite List.app_nil_r in x.
  exists (rul :: sigma)%list.
  exists List.nil. simpl. rewrite List.app_nil_r.
  split. rewrite <- x.
  apply build_consimp. apply H.
  split. rewrite subst_const_nil. apply build_nil.
  reflexivity.
- simpl in x. apply cons_inj in x. destruct x.
  assert (
    exists sigma1 sigma2 : s_rules,
    build_subst sigma1 ((tyC, tyA) :: (tyB, tyD) :: const1)%list /\
    build_subst sigma2 (subst_const sigma1 (t0 :: const2)%list) /\
    (rul :: sigma)%list = (sigma1 ++ sigma2)%list
  ). apply IHbuild_subst. simpl.
  rewrite H1.
  apply JMeq_refl.
  destruct H2. destruct H2.
  destruct H2. destruct H3.
  dependent destruction x.
  dependent destruction H2.
  exists (s :: x)%list. exists x0.
  split. rewrite <- H0.
  apply build_consimp. apply H2.
  split. rewrite <- step_subst_const. apply H3.
  rewrite H4. reflexivity.
Qed.

Lemma build_bidir_good_syn :
  forall {n : nat} (gamma : context n) (st : sterm n)
  (ty : type) (const : constraints) (sigma : s_rules),
  is_bidir_syn gamma st ty const ->
  build_subst sigma const ->
  good_rules sigma

with build_bidir_good_chk :
  forall {n : nat} (gamma : context n) (ct : cterm n)
  (ty : type) (const : constraints) (sigma : s_rules),
  is_bidir_chk gamma ct ty const ->
  build_subst sigma const ->
  good_rules sigma.

Proof.
- intros n gamma st ty const sigma hb h.
  dependent induction hb.
  + apply IHhb. apply h.
  + apply build_bidir_good_chk with
    (n := n) (gamma := gamma) (ct := ct)
    (ty := (TVar a)) (const := const).
    apply H. apply h.
- intros n gamma st ty const sigma hb h.
  dependent induction hb.
  + dependent destruction h. apply good_nil.
  + apply build_app in h.
    destruct h.
    destruct H0.
    destruct H0.
    destruct H1.
    rewrite H2.
    apply good_app.
    apply build_bidir_good_chk with
    (n := n) (gamma := gamma) (ct := ct1)
    (ty := TImp ty1 ty2) (const := const1).
    apply hb. apply H0.
    apply build_bidir_good_syn with
    (n := m) (gamma := delta) (st := st2)
    (ty := ty1) (const := const2). (* (const := (subst_const x const2)). *)
    apply H. admit.
  + admit.
Admitted.

(* End goal *)

Lemma add_sat_xi : forall (sigma : s_rules) (rul : s_rule) (const : constraints),
  sat_xi sigma const -> sat_xi (rul :: sigma)%list const.
Proof.
intro sigma.
induction sigma; intros.
- apply taut_sat_xi.
  apply nil_sat_taut.
  apply H.
- admit.
Admitted.

Lemma join_sat_xi : forall (sigma1 sigma2 : s_rules) (const : constraints),
  sat_xi sigma1 const \/ sat_xi sigma2 const -> sat_xi (sigma1 ++ sigma2)%list const.
Proof.
intros. destruct H.
--
induction sigma2.
- rewrite List.app_nil_r. apply H.
- induction sigma1.
  + simpl.

Admitted.

Theorem build_bidir_mgu_syn :
  forall {n : nat} (gamma : context n) (st : sterm n)
  (ty : type) (const : constraints) (sigma : s_rules),
  is_bidir_syn gamma st ty const ->
  build_subst sigma const ->
  is_mgu sigma const

with build_bidir_mgu_chk :
  forall {n : nat} (gamma : context n) (ct : cterm n)
  (ty : type) (const : constraints) (sigma : s_rules),
  is_bidir_chk gamma ct ty const ->
  build_subst sigma const ->
  is_mgu sigma const.

Proof.

--

intros.
dependent induction H.
- apply IHis_bidir_syn. apply H0.
- apply build_bidir_mgu_chk with (n := n) (gamma := gamma) (ct := ct) (ty := (TVar a)).
  apply H. apply H0.

--

intros.
dependent induction H.
---
split. apply sat_nil.
dependent destruction H0. simpl.
intro sigma'. exists sigma'.
reflexivity.
---
apply build_app in H1.
destruct H1. destruct H1.
destruct H1. destruct H2.
rewrite H3.
split.
-
apply app_sat_xi.
(*
assert (sat_xi (x0 ++ x)%list const1).
apply perm_sat_xi with ().
*)
admit.
admit.
-
admit.
---
admit.
Admitted.





















