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

Inductive sat_xi : s_rules -> constraints -> Prop :=
| sat_nil sigma : sat_xi sigma List.nil
| sat_cons sigma ty1 ty2 const :
  sat_xi sigma const ->
  subst_ty sigma ty1 = subst_ty sigma ty2 ->
  sat_xi sigma (List.cons (ty1, ty2) const).

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

(* Unification *)

(*
Theorem bidir_subst_syn :
  forall {n : nat} (gamma : context n) (st : sterm n) (ty : type) (const : constraints) (sigma1 sigma2 : s_rules),
  is_bidir_syn gamma st ty const ->
  sat_xi sigma1 const ->
  Permutation sigma1 sigma2 ->
  sat_xi sigma2 const

with bidir_subst_chk :
  forall {n : nat} (gamma : context n) (ct : cterm n) (ty : type) (const : constraints) (sigma1 sigma2 : s_rules),
  is_bidir_chk gamma ct ty const ->
  sat_xi sigma1 const ->
  Permutation sigma1 sigma2 ->
  sat_xi sigma2 const.
Proof.
- intros n gamma st ty const sigma1 sigma2 hb hs hp.
  induction hb.
  + apply IHhb. apply hs.
  + apply bidir_subst_chk with
    (n := n) (gamma := gamma)
    (ct := ct) (ty := TVar a)
    (sigma1 := sigma1).
    apply H. apply hs. apply hp.
- intros n gamma st ty const sigma1 sigma2 hb hs hp.
  einduction hb.
  + apply sat_nil.
  + assert (sat_xi sigma1 const1).
    apply appleft_sat_xi with (const2 := const2). apply hs.
    assert (sat_xi sigma1 const2).
    apply appright_sat_xi with (const1 := const1). apply hs.
    assert (sat_xi sigma2 const1).
    apply IHi. apply i. apply H0.
    assert (sat_xi sigma2 const2).
    apply bidir_subst_syn with
    (n := m) (gamma := delta)
    (st := st2) (ty := ty1)
    (sigma1 := sigma1).
    apply H. apply H1. apply hp.
    apply app_sat_xi.
    apply H2. apply H3.
  + dependent destruction hs.
    apply sat_cons.
    apply bidir_subst_syn with
    (n := n) (gamma := gamma)
    (st := st) (ty := ty1)
    (sigma1 := sigma).
    apply H0. apply hs. apply hp.

induction hp.
* simpl. simpl in H. apply H.
* simpl. simpl in H.
*)

Inductive build_subst : s_rules -> constraints -> Prop :=
| build_nil : build_subst List.nil List.nil
| build_consleft sigma const a ty :
  build_subst sigma const ->
  build_subst (sigma ++ (a, ty) :: List.nil)%list ((TVar a, ty) :: const)%list
| build_consright sigma const b ty :
  build_subst sigma const ->
  build_subst (sigma ++ (b, ty) :: List.nil)%list ((ty, TVar b) :: const)%list
| build_consimp sigma const tyA tyB tyC tyD :
  build_subst sigma ((tyC, tyA) :: (tyB, tyD) :: const)%list ->
  build_subst sigma ((TImp tyA tyC, TImp tyB tyD) :: const)%list.

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

Lemma subst_ty_last : forall (sigma : s_rules) (rul : s_rule) (ty : type),
  subst_ty (sigma ++ rul :: Datatypes.nil)%list ty = 
  subst1_ty rul (subst_ty sigma ty).
Proof.
intro sigma. induction sigma.
- simpl. reflexivity.
- intros rul ty. simpl.
  apply IHsigma.
Qed.

Lemma skip_sat_xi : forall (sigma : s_rules) (rul : s_rule) (const : constraints),
  sat_xi sigma const-> sat_xi (sigma ++ rul :: List.nil)%list const.
Proof.
intros.
induction H.
- apply sat_nil.
- apply sat_cons.
  apply IHsat_xi.
  rewrite ? subst_ty_last.
  rewrite H0.
  reflexivity.
Qed.

(*
Lemma build_sat : forall (sigma : s_rules) (const : constraints),
  build_subst sigma const ->
  sat_xi sigma const.
Proof.
intros sigma const h.
induction h.
- apply sat_nil.
- apply sat_cons.
  + apply skip_sat_xi. apply IHh.
  + rewrite ? subst_ty_last.
    simpl.


  induction const.
  + apply sat_nil.
  + case_eq a0.
    intros t1 t2 eq.
    apply sat_cons.
*)

(*

(*
Consider: 
unif_extra      only when !=Nil
unif_perm_sigma ..
unif_perm_const ..

unif_taut sigma ty const:
  sat_xi sigma (List.cons (ty, ty) const) ->
  sat_xi sigma const
*)

Inductive sat_xi : s_rules -> constraints -> Prop :=
| unif_empty : sat_xi List.nil List.nil
| unif_left (n : nat) (ty : type) sigma const :
  sat_xi sigma const ->
  sat_xi (List.cons (n, ty) sigma) (List.cons (TVar n, ty) const)
| unif_right (n : nat) (ty : type) sigma const :
  sat_xi sigma const ->
  sat_xi (List.cons (n, ty) sigma) (List.cons (ty, TVar n) const)
| unif_imp (tyl1 tyl2 tyr1 tyr2 : type) rul sigma const :
  sat_xi (List.cons rul sigma) (List.cons (tyl2, tyr2) (List.cons (tyr1, tyl1) const)) ->
  sat_xi (List.cons rul sigma) (List.cons (TImp tyl1 tyl2, TImp tyr1 tyr2) const)
| unif_skip rul sigma const :
  sat_xi sigma const -> sat_xi (List.cons rul sigma) const
| unif_extra sigma eq const :
  sat_xi sigma (List.cons eq const) -> sat_xi sigma const
| unif_perm_sigma sigma1 sigma2 const :
  sat_xi sigma1 const -> Permutation sigma1 sigma2 ->
  sat_xi sigma2 const
| unif_perm_const sigma const1 const2 :
  sat_xi sigma const1 -> Permutation const1 const2 ->
  sat_xi sigma const2.

Lemma skipall_sat_xi : forall (sigma : s_rules), sat_xi sigma List.nil.
Proof.
intro sigma. induction sigma.
- apply unif_empty.
- apply unif_skip. apply IHsigma.
Qed.

Lemma appleft_sat_xi : forall (sigma : s_rules) (const1 const2 : constraints),
  sat_xi sigma (List.app const1 const2) -> sat_xi sigma const1.
Proof.
induction const2.
- rewrite List.app_nil_r. intro h. apply h.
- intro h. apply IHconst2.
  assert (Permutation (const1 ++ a :: const2)%list (a :: (const1 ++ const2))%list).
  Check Permutation_cons_app.
  apply (Permutation_sym (Permutation_cons_app
    (l := (const1 ++ const2)) const1 const2 a
    (Permutation_refl (const1 ++ const2)))).
  assert (sat_xi sigma (a :: const1 ++ const2)%list).
  apply (unif_perm_const sigma (const1 ++ a :: const2)%list (a :: (const1 ++ const2))%list).
  apply h. apply H.
  apply unif_extra with (eq := a).
  apply H0.
Qed.

Lemma appright_sat_xi : forall (sigma : s_rules) (const1 const2 : constraints),
  sat_xi sigma (List.app const1 const2) -> sat_xi sigma const2.
Proof.
induction const1.
- simpl. intros const2 h. apply h.
- intros const2 h. apply IHconst1.
  simpl in h. apply unif_extra with (eq := a).
  apply h.
Qed.

(* TODO *)
Lemma nil_rules : forall (const : constraints) (ty1 ty2 : type),
  sat_xi List.nil (List.cons (ty1, ty2) const) ->
  ty1 <> ty2.
Proof.
intros const ty1 ty2 h.
dependent induction h.
- apply IHh with (const := const).
Admitted.

(* TODO *)
Lemma subst_converge : forall (sigma : s_rules) (const : constraints) (ty1 ty2 : type),
  sat_xi sigma ((ty1, ty2) :: const)%list ->
  subst_ty sigma ty1 = subst_ty sigma ty2.
Proof.
intros sigma const ty1 ty2 h.
induction sigma.
- dependent destruction h.
  + simpl. admit.
  + simpl. destruct sigma1.
    * admit.
    * apply Permutation_sym in H.
      assert (~Permutation Datatypes.nil (s :: sigma1))
        by (apply (Permutation_nil_cons (l := sigma1) (x := s))).
      apply H0 in H. contradiction.
  + simpl. destruct const1.
    * admit.
    * admit.
- dependent destruction h.
Admitted.

(* Theorem *)

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
    apply (
      typed_abs
      (subst_ty sigma ty1) (subst_ctx sigma gamma)
      (strip_syn st) (subst_ty sigma ty2)
    ).
    rewrite <- cons_subst_ctx.
    apply IHhb. apply hs.
  + simpl. apply bidir_typed_chk with (const := const).
    apply H. apply hs.
- intros n gamma ct ty const sigma hb hs.
  induction hb.
  + simpl.
    rewrite single_subst_ctx.
    apply (typed_var (subst_ty sigma ty)).
  + simpl.
    rewrite app_subst_ctx.
    apply (
      typed_app
      (subst_ctx sigma gamma) (subst_ctx sigma delta)
      (strip_chk ct1) (strip_syn st2)
      (subst_ty sigma ty1) (subst_ty sigma ty2)
    ).
    * rewrite <- dist_subst_ty.
      apply IHhb.
      apply appleft_sat_xi with (const2 := const2).
      apply hs.
    * apply bidir_typed_syn with (const := const2).
      apply H.
      apply appright_sat_xi with (const1 := const1).
      apply hs.
  + simpl.
    assert (subst_ty sigma ty1 = subst_ty sigma ty2).
    apply subst_converge with (const := const).
    apply hs.
    rewrite <- H0.
    apply bidir_typed_syn with (const := const).
    apply H.
    apply unif_extra with (eq := (ty1, ty2)).
    apply hs.
Qed.
*)

(* TODO: Principal Typing *)

Definition is_princ : Type := forall {n : nat} (ctx : context n) (pt : pterm n) (ty : type),
  is_typed ctx pt ty -> forall (ctx' : context n) (ty' : type), is_typed ctx' pt ty' ->
  sig (fun (sigma : s_rules) => ctx' = subst_ctx sigma ctx /\ ty' = subst_ty sigma ty).















