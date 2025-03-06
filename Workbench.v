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

(* TODO: Principal Typing *)

Definition is_princ : Type := forall {n : nat} (ctx : context n) (pt : pterm n) (ty : type),
  is_typed ctx pt ty -> forall (ctx' : context n) (ty' : type), is_typed ctx' pt ty' ->
  sig (fun (sigma : s_rules) => ctx' = subst_ctx sigma ctx /\ ty' = subst_ty sigma ty).















