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


Inductive not_FTV : nat -> type -> Prop :=
| nFTV_var a b : a <> b -> not_FTV a (TVar b)
| nFTV_imp a ty1 ty2 :
  not_FTV a ty1 ->
  not_FTV a ty2 ->
  not_FTV a (TImp ty1 ty2).

(*
Inductive not_FCV_syn : forall {n : nat}, nat -> sterm n -> Prop :=
| nFCV_abs st : not_FCV_syn st -> not_FCV_syn (SAbs st)
| nFCV_cir a ct : 
*)

(* Unique Atomic Names *)

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

(* Tautology *)

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

(* Planar Lambda Typing Properties *)

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

Lemma build_app : forall (const1 const2 : constraints) (sigma : s_rules) ,
  build_subst sigma (const2 ++ const1)%list ->
  exists sigma2 sigma1 : s_rules,
  build_subst sigma2 const2 /\
  build_subst sigma1 const1 /\
  sigma = (sigma2 ++ sigma1)%list.
Proof.
intros const1 const2.
induction const2; intros sigma h.
- exists List.nil. exists sigma.
  split. apply build_nil.
  split. simpl in h. apply h.
  simpl. reflexivity.
- simpl in h.
  dependent destruction h.
  + assert (
      exists sigma2 sigma1 : s_rules,
      build_subst sigma2 (subst1_const (a0, ty) const2) /\
      build_subst sigma1 const1 /\ sigma = (sigma2 ++ sigma1)%list
    ). admit.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    exists ((a0, ty) :: x)%list.
    exists x0.
    split. apply build_consleft. apply H.
    split. apply H0.
    simpl. rewrite H1. reflexivity.
Admitted.

(*

  assert (
      exists sigma2 sigma1 : s_rules,
      build_subst sigma2 const2 /\
      build_subst sigma1 const1 /\ ((a0, ty) :: sigma)%list = (sigma2 ++ sigma1)%list
    ). apply IHconst2.
    destruct const2.
    destruct const1.
    simpl in h. simpl. dependent destruction.
    

  assert (
    exists sigma2 sigma1 : s_rules,
    build_subst sigma2 const2 /\
    build_subst sigma1 const1 /\ sigma = (sigma2 ++ sigma1)%list
  ).
  apply IHconst2.


  dependent destruction h.
  + assert (
      exists sigma2 sigma1 : s_rules,
      build_subst sigma2 const2 /\
      build_subst sigma1 const1 /\ ((a0, ty) :: sigma)%list = (sigma2 ++ sigma1)%list
    ).
    apply IHconst2.
    apply build_consleft.

  

destruct const2; destruct const1.
- exists List.nil. exists List.nil.
  split. apply build_nil. split. apply build_nil.
  simpl. simpl in h.
  dependent destruction h.
  reflexivity.
- simpl in h.
  exists List.nil. exists sigma.
  split. apply build_nil.
  split. apply h.
  simpl. reflexivity.
- simpl in h. rewrite List.app_nil_r in h.
  exists sigma. exists List.nil.
  split. apply h.
  split. apply build_nil.
  rewrite List.app_nil_r.
  reflexivity.
- assert (
    exists sigma2 sigma1 : s_rules,
    build_subst sigma2 const2 /\
    build_subst sigma1 (t0 :: const1)%list /\ sigma = (sigma2 ++ sigma1)%list
  ).
  


dependent induction h.
- dependent destruction const2.
  dependent destruction const1.
  exists List.nil.
  exists List.nil.
  split. apply build_nil.
  split. apply build_nil.
  simpl. reflexivity.
  simpl in x. discriminate.
  simpl in x. discriminate.
- 
Admitted.
*)

Lemma good_app : forall (sigma1 sigma2 : s_rules),
  good_rules sigma1 -> good_rules sigma2 -> good_rules (sigma1 ++ sigma2)%list.
Proof.
intros sigma1 sigma2 h1 h2.
induction h1.
- simpl. apply h2.
- simpl. apply good_cons.
  apply H. apply IHh1.
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
    apply build_bidir_good_syn with
    (n := m) (gamma := delta) (st := st2)
    (ty := ty1) (const := const2).
    apply H. apply H0.
    apply build_bidir_good_chk with
    (n := n) (gamma := gamma) (ct := ct1)
    (ty := TImp ty1 ty2) (const := const1).
    apply hb. apply H1.
  + admit.
Admitted.

(* Principality *)

Inductive subst_dom : s_rules -> s_rules -> constraints -> Prop :=
| dom_nil sigma : subst_dom sigma List.nil List.nil
| dom_cons sigma1 sigma2 ty1 ty2 const :
  subst_dom sigma1 sigma2 const ->
  subst_ty sigma1 (subst_ty sigma2 ty1) = subst_ty sigma1 ty1 ->
  subst_ty sigma1 (subst_ty sigma2 ty2) = subst_ty sigma1 ty2 ->
  subst_dom sigma1 sigma2 ((ty1, ty2) :: const)%list.

Definition is_principal (sigma : s_rules) (const : constraints) : Prop :=
  sat_xi sigma const /\
  (forall (sigma' : s_rules),
   sat_xi sigma' const ->
   forall (const' : constraints),
   subst_dom sigma' sigma const').

Lemma build_princ : forall (sigma : s_rules) (const : constraints),
  build_subst sigma const ->
  good_rules sigma ->
  is_principal sigma const.
Proof.
intros sigma const hb good.
split.
- apply build_sat. apply hb. apply good.
- intros sigma' hs. dependent induction hb.
  + intros. apply dom_nil.
  + admit.
  + admit.
  + admit.
Admitted.

(* Unification *)

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
  sat_xi sigma ((ty1, ty2) :: List.nil)%list ->
  is_inter_chk gamma (CSqu st) ty2 sigma.

Inductive is_inter : forall {a : nat}, context a -> lterm a -> type -> Prop :=
| Sbidir {n} gamma (st : sterm n) ty :
  is_inter_syn gamma st ty ->
  is_inter gamma (LSyn st) ty
| Cbidir {n} gamma (ct : cterm n) ty :
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
    dependent destruction H0.
    rewrite <- H1.
    apply subst_typed.
    apply inter_typed_syn.
    apply H.
Qed.

(* Principal Typing *)

(*
Inductive is_comp_sigma : s_rules -> s_rules -> Prop :=
| comp_nil sigma : is_comp_sigma sigma List.nil
| comp_id sigma : is_comp_sigma sigma sigma
| comp_cons sigma :
*)

Definition is_princ := forall {n : nat} (ctx : context n) (pt : pterm n) (ty : type),
  is_typed ctx pt ty -> forall (ctx' : context n) (ty' : type), is_typed ctx' pt ty' ->
  sig (fun (sigma : s_rules) => ctx' = subst_ctx sigma ctx /\ ty' = subst_ty sigma ty).


