Require Import Nat.
Require Import Snoclist.
Import SnoclistNotations.
Require Import PlanarLambda.
Require Import Types.

Require Import Subst.
Require Import LabeledLambda.
Require Import Bidir.
Require Import Build.

Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Arith.
Require List.

(* -- *)

(* -- Princ -- *)

(*
Definition is_princ {n : nat} (gamma : context n) (pt : pterm n) (ty : type) : Prop :=
  is_typed gamma pt ty /\
  forall (gamma' : context n) (ty' : type),
  is_typed gamma' pt ty' ->
  (exists (sigma : s_rules), gamma' = subst_ctx sigma gamma) ->
  (exists (sigma : s_rules), gamma' = subst_ctx sigma gamma /\ ty' = subst_ty sigma ty).
*)

(*
Definition is_princ {n : nat} (gamma : context n) (pt : pterm n) (ty : type) : Prop :=
  is_typed gamma pt ty /\
  forall (ty' : type),
  is_typed gamma pt ty' ->
  exists (sigma : s_rules),
  ty' = subst_ty sigma ty.
*)

Definition is_princ {n : nat} (gamma : context n) (pt : pterm n) (ty : type) : Prop :=
  is_typed gamma pt ty /\
  forall (gamma' : context n) (ty' : type),
  is_typed gamma' pt ty' ->
  exists (sigma : s_rules),
  gamma' = subst_ctx sigma gamma /\ ty' = subst_ty sigma ty.

(* -- Bidir -- *)

(*
Theorem bidir_princ_syn :
  forall {n : nat} (gamma : context n) (st : sterm n) (ty : type) (const : constraints) (sigma : s_rules),
  is_bidir_syn gamma st ty const ->
  is_mgu sigma const ->
  is_princ (subst_ctx sigma gamma) (strip_syn st) (subst_ty sigma ty).
Proof.
intros.
destruct H0. split.
--
apply bidir_typed_syn with (const := const).
apply H. apply H0.
--
intros. destruct H3.
assert (
  exists (sigma' : s_rules),
  sat_xi sigma' const /\
  ty' = subst_ty sigma' ty
). admit. (* apply bidir_sigma_syn with (st := st). apply H. apply H2. *)
destruct H4.
assert (
 exists tau : s_rules,
 forall ty : type, subst_ty x0 ty = subst_ty tau (subst_ty sigma ty)
). apply H1. apply H4.
destruct H5.
exists x0. split.
- rewrite <- subst_forall_ctx with (sigma' := x0).
rewrite <- H4. apply H3.
Admitted.
Qed.

 destruct H3. split.
rewrite H4. rewrite H5.
assert (
 exists tau : s_rules,
 forall ty : type, subst_ty x ty = subst_ty tau (subst_ty sigma ty)
). apply H1. apply H3.
destruct H6. 
exists x0. split.
- apply subst_forall_ctx. apply H6.
- apply H6.
Qed.
*)

(*
Lemma bidir_sigma_syn :
  forall {n : nat} (gamma : context n) (st : sterm n) (ty : type) (const : constraints) (sigma : s_rules),
  is_bidir_syn gamma st ty const ->
  is_mgu sigma const ->
  forall (ty' : type),
  is_typed (subst_ctx sigma gamma) (strip_syn st) ty' ->
  exists (sigma' : s_rules),
  sat_xi sigma' const /\ ty' = subst_ty sigma' ty.
Proof.
intros n gamma st ty const sigma hb.
dependent induction hb; intros hm ty' ht.
-
dependent destruction ht.

assert (ty0 = subst_ty sigma ty1). admit.

assert (
  exists sigma' : s_rules, sat_xi sigma' const /\ ty3 = subst_ty sigma' ty2
). apply IHhb. apply hm.

rewrite cons_subst_ctx. rewrite <- H. apply ht.

destruct H0. exists x.
split. apply H0.
rewrite dist_subst_ty.
destruct H0.
rewrite <- H1.
admit.

-
Admitted.

(* ---------------- *)

Theorem bidir_princ_syn :
  forall {n : nat} (gamma : context n) (st : sterm n) (ty : type) (const : constraints) (sigma : s_rules),
  is_bidir_syn gamma st ty const ->
  is_mgu sigma const ->
  is_princ (subst_ctx sigma gamma) (strip_syn st) (subst_ty sigma ty).
Proof.
intros.
split.
--
destruct H0.
apply bidir_typed_syn with (const := const).
apply H. apply H0.
--
intros.
assert (
  exists (sigma' : s_rules),
  sat_xi sigma' const /\
  ty' = subst_ty sigma' ty
). apply bidir_sigma_syn with (sigma := sigma) (gamma := gamma) (st := st).
apply H. apply H0. apply H1.
destruct H0.
destruct H2. destruct H2.
rewrite H4.
assert (
 exists tau : s_rules,
 forall ty : type, subst_ty x ty = subst_ty tau (subst_ty sigma ty)
). apply H3. apply H2.
destruct H5. 
exists x0.
apply H5.
Qed.
*)

Lemma bidir_sigma_syn :
  forall {n : nat} (gamma : context n) (st : sterm n) (ty : type) (const : constraints),
  is_bidir_syn gamma st ty const ->
  forall (gamma' : context n) (ty' : type),
  is_typed gamma' (strip_syn st) ty' ->
  exists (sigma : s_rules),
  sat_xi sigma const /\
  gamma' = subst_ctx sigma gamma /\ ty' = subst_ty sigma ty.
Proof.
intros.
Admitted.

(*
dependent induction H.


--
assert (
  exists sigma : s_rules,
  sat_xi sigma const /\
  gamma' :: ty1 = subst_ctx sigma (gamma :: ty1) /\
  ty2 = subst_ty sigma ty2
). apply IHis_bidir_syn. admit.
destruct H1.
exists x.
split. apply H1.
split. admit.
rewrite dist_subst_ty. admit.

dependent destruction H0.
*)

Theorem bidir_princ_syn :
  forall {n : nat} (gamma : context n) (st : sterm n) (ty : type) (const : constraints) (sigma : s_rules),
  is_bidir_syn gamma st ty const ->
  is_mgu sigma const ->
  is_princ (subst_ctx sigma gamma) (strip_syn st) (subst_ty sigma ty).
Proof.
intros.
destruct H0. split.
apply bidir_typed_syn with (const := const).
apply H. apply H0.
intros.
assert (
  exists (sigma' : s_rules),
  sat_xi sigma' const /\
  gamma' = subst_ctx sigma' gamma /\ ty' = subst_ty sigma' ty
). apply bidir_sigma_syn with (st := st). apply H. apply H2.
destruct H3. destruct H3. destruct H4.
rewrite H4. rewrite H5.
assert (
 exists tau : s_rules,
 forall ty : type, subst_ty x ty = subst_ty tau (subst_ty sigma ty)
). apply H1. apply H3.
destruct H6. 
exists x0. split.
- apply subst_forall_ctx. apply H6.
- apply H6.
Qed.

(* -- Inter -- *)

(*
Theorem inter_typed_syn :
  forall {n : nat} (gamma : context n) (st : sterm n) (ty : type),
  is_inter_syn gamma st ty ->
  is_princ gamma (strip_syn st) ty

with inter_typed_chk :
  forall {n : nat} (gamma : context n) (ct : cterm n) (ty : type) (sigma : s_rules),
  is_inter_chk gamma ct ty sigma ->
  is_princ (subst_ctx sigma gamma) (strip_chk ct) (subst_ty sigma ty).

Proof.

--
intros. split.
apply inter_typed_syn. apply H.

dependent induction H; intros.
- 
Admitted.



*)




























