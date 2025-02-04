(*
Require Import String.
Require Import List.
Require Bool.
Import ListNotations.
Import StringSyntax.

Definition s_eq (a b : string) : Prop :=
if eqb a b then True else False.

Inductive term : Type :=
| Var : string -> term
| Abs : string -> term -> term
| App : term -> term -> term.

Inductive stype : Type :=
| TVar : string -> stype
| TImp : stype -> stype -> stype.

(* String Representation *)

Fixpoint s_of_term (t : term) : string :=
match t with
| Var x => x
| Abs x t' =>
  match t' with
  | (Var y) => "L " ++ x ++ "." ++ y
  | (Abs _ _) => 
    match s_of_term t' with
    | String _ s => "L " ++ x ++ s
    | _ => ""
    end
  | App _ _ => "L " ++ x ++ ".(" ++ s_of_term t' ++ ")"
  end
| App t1 t2 =>
  match t1 with
  | Abs x t1' => "(" ++ s_of_term t1 ++ ") " ++ s_of_term t2
  | _ => s_of_term t1 ++ " " ++ s_of_term t2
  end
end.

Eval compute in s_of_term (Abs "x" (Var "x")).
Eval compute in s_of_term (Abs "x" (Abs "y" (App (Var "x") (Var "y")))).
Eval compute in s_of_term (Abs "x" (Abs "y" (App (App (Abs "z" (Var "z")) (Var "x")) (Var "y")))).

Fixpoint s_of_stype (ty : stype) : string :=
match ty with
| TVar x => x
| TImp ty1 ty2 =>
  match (ty1, ty2) with
  | (TVar x, TVar y) => x ++ " -> " ++ y
  | (TVar x, _) => x ++ " -> " ++ s_of_stype ty2
  | (_, TVar y) => "(" ++ s_of_stype ty1 ++ ") -> " ++ y 
  | _ => "(" ++ s_of_stype ty1 ++ ") -> " ++ s_of_stype ty2
  end
end.

Eval compute in s_of_stype (TImp (TImp (TImp (TVar "a") (TVar "b")) (TVar "a")) (TVar "b")).
Eval compute in s_of_stype (TImp (TImp (TVar "a") (TVar "b")) (TImp (TVar "a") (TVar "b"))).

(* Free Variables *)

Definition FVcontext : Type := list string.

Fixpoint inb (v:string) (ctx:FVcontext) : bool :=
match ctx with
| [] => false
| x :: ctx' => if (eqb v x) then true else inb v ctx'
end.

Fixpoint inp (v:string) (ctx:FVcontext) : Prop :=
match ctx with
| [] => False
| x :: ctx' => if (eqb v x) then True else inp v ctx'
end.

Lemma in_b_p : forall (v:string) (ctx:FVcontext), inb v ctx = true <-> inp v ctx.
Proof.
intros v ctx.
split.
- induction ctx.
  + intro h.
    simpl in h.
    apply Bool.diff_false_true in h.
    contradiction.
  + simpl.
    case (eqb v a). reflexivity. assumption.
- induction ctx.
  + intro h.
    simpl in h.
    contradiction.
  + simpl.
    case (eqb v a). reflexivity. assumption.
Qed.

Fixpoint isFV (v:string) (t:term) : bool :=
match t with
| Var x => eqb v x
| Abs x t' => if (eqb v x) then false else isFV v t'
| App t1 t2 => (isFV v t1) || (isFV v t2)
end.

Fixpoint getFVs (ctx:FVcontext) (t:term) : FVcontext :=
match t with
| Var x => if (inb x ctx) then [] else [x]
| Abs x t' => getFVs (x :: ctx) t'
| App t1 t2 => (getFVs ctx t1) ++ (getFVs ctx t2)
end.

(* Permutations *)

Inductive perm : FVcontext -> FVcontext -> Prop :=
| perm_nil : perm [] []
| perm_skip x l l' : perm l l' -> perm (x :: l) (x :: l')
| perm_swap x y l : perm (y::x::l) (x::y::l)
| perm_trans l l' l'' : perm l l' -> perm l' l'' -> perm l l''.

(* Linear Terms *)

Inductive linear : FVcontext -> term -> Type :=
| lin_var x : linear [x] (Var x)
| lin_abs x t ctx : linear (x :: ctx) t -> linear ctx (Abs x t)
| lin_app t1 t2 ctx1 ctx2 :
  linear ctx1 t1 -> linear ctx2 t2 -> linear (ctx2 ++ ctx1) (App t1 t2)
| lin_perm ctx1 ctx2 t :
  linear ctx1 t -> perm ctx1 ctx2 -> linear ctx2 t.

Inductive linc : term -> Prop := lin_closure t : linear [] t -> linc t.

Lemma idlin : linc (Abs "x" (Var "x")).
Proof.
apply lin_closure.
apply lin_abs.
apply lin_var.
Qed.

Lemma truelin : linc (Abs "x" (Abs "y" (App (Var "x") (Var "y")))).
Proof.
apply lin_closure.
apply lin_abs. apply lin_abs.
apply (lin_app (Var "x") (Var "y") ["x"%string] ["y"%string]).
apply lin_var. apply lin_var.
Qed.

Lemma falselin : linc (Abs "x" (Abs "y" (App (Var "y") (Var "x")))).
Proof.
apply lin_closure.
apply lin_abs. apply lin_abs.
apply (lin_perm ["x"%string; "y"%string] ["y"%string; "x"%string] (App (Var "y") (Var "x"))).
apply (lin_app (Var "y") (Var "x") ["y"%string] ["x"%string]).
apply lin_var. apply lin_var.
apply perm_swap.
Qed.

Inductive lterm : Type :=
| Linear ctx t : linear ctx t -> lterm.

(* Typing *)

(* Definition context : Type := list (string * stype). *)

Inductive context : FVcontext -> Type :=
| envNil : context []
| envCons x ctx: stype -> context ctx -> context (x :: ctx).

Inductive searchkey (ctx : FVcontext) : Type :=
| Value x : inp x ctx -> searchkey ctx.

Definition constraints : Type := list (stype * stype).

Lemma empty_search : searchkey [] -> False.
Proof. intro key. case key. simpl. intros x c. apply c. Qed.

Lemma empty_search' : forall (fvs : FVcontext), (fvs = []) -> searchkey fvs -> False.
Proof. intros fvs h. rewrite h. apply empty_search. Qed.

Lemma eq_FVcontext : forall fvs : FVcontext, fvs = fvs. Proof. reflexivity. Qed.

Lemma search_not_empty : forall (fvs : FVcontext), searchkey fvs -> fvs <> [].
Proof. intros fvs key. case key. intros x h. case_eq fvs.
- intro eq. rewrite eq in h. simpl in h. contradiction.
- intros s l eq contr. apply eq_sym in contr. apply nil_cons in contr. contradiction.
Qed.


(*
Fixpoint getType {fvs : FVcontext} (ctx : context fvs) (key : searchkey fvs) : stype :=
match fvs return (fvs <> []) -> stype with
| [] => fun lemma => match lemma eq_refl with end
| x :: fvs' => fun lemma =>
  match key with
  | Value y inprop =>
    if (eqb x y) then 
    else 
  end
end (search_not_empty fvs key).
*)


(*
Fixpoint getType {fvs : FVcontext} (ctx : context fvs) (key : searchkey fvs) : stype :=
match fvs as fvs' return (fvs = fvs') -> (searchkey fvs -> False) -> stype with
| [] => fun (e : fvs = []) lemma => match lemma key with end
| _ => fun _ _ => TVar "temp"
end (empty_search' fvs eq_refl).
*)

(*
Fixpoint constraint_typing (env : context) (lt : lterm) : (stype * constraints) :=
match lt with
| Linear _ _ lin =>
  match lin with
  | lin_var x => (TVar "placeholder", [])
  | lin_abs x t ctx lin' =>
  end
end.
*)

*)






