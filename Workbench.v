Require Import Nat.
Require Import Snoclist.
Import SnoclistNotations.
Require Import PlanarLambda.
Require Import Types.

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

Fixpoint subst (rul : s_rule) (ty : type) : type :=
match ty with
| TVar n => let (m, u) := rul in
  match eqb n m with
  | true => u
  | false => ty
  end
| TImp ty1 ty2 => TImp (subst rul ty1) (subst rul ty2)
end.

Fixpoint subst_ty (sigma : s_rules) (ty : type) : type :=
match sigma with
| List.nil => ty
| List.cons rul sigma' =>
  subst_ty sigma' (subst rul ty)
end.

Fixpoint subst_ctx {n : nat} (sigma : s_rules) (ctx : context n) : context n :=
match ctx with
| [] => []
| ctx' :: ty => (subst_ctx sigma ctx') :: (subst_ty sigma ty)
end.

Lemma subst_typed : forall {n : nat} (sigma : s_rules) (ctx : context n) (pt : pterm n) (ty : type),
  is_typed ctx pt ty -> is_typed (subst_ctx sigma ctx) pt (subst_ty sigma ty).
Admitted.

Definition is_princ : Type := forall {n : nat} (ctx : context n) (pt : pterm n) (ty : type),
  is_typed ctx pt ty -> forall (ctx' : context n) (ty' : type), is_typed ctx' pt ty' ->
  sig (fun (sigma : s_rules) => ctx' = subst_ctx sigma ctx /\ ty' = subst_ty sigma ty).

(* ===== Inference ===== *)

Definition type_eq : Type := type * type.
Definition constraints : Type := list type_eq.

Definition length {A : Type} {n : nat} : snoclist A n -> nat := fix length l := n.

(*Check let (pair a b, c) := (pair 1 2, 3) in a.*)

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














