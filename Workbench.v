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

(* Unification *)

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

Check ex.

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



Inductive subst_dom : s_rules -> s_rules -> constraints -> Prop :=
| dom_nil sigma1 sigma2 : subst_dom sigma1 sigma2 List.nil
| dom_cons sigma1 sigma2 ty1 ty2 const :
  subst_dom sigma1 sigma2 const ->
  subst_ty sigma1 (subst_ty sigma2 ty1) = subst_ty sigma1 ty1 ->
  subst_ty sigma1 (subst_ty sigma2 ty2) = subst_ty sigma1 ty2 ->
  subst_dom sigma1 sigma2 ((ty1, ty2) :: const)%list.

(* ================== *)

Inductive is_primitive : s_rules -> Prop :=
| prim (sigma : s_rules) (const : constraints) :
  sat_xi sigma const ->
  (forall (sigma' : s_rules),
   sat_xi sigma' const ->
   subst_dom sigma' sigma const) ->
  is_primitive sigma.

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


