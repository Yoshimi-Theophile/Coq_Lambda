
Require Import String.
Require Import Bool.
Require Import Arith.

Require Import Aux.

Inductive pterm : nat -> Type :=
| PVar : pterm 1
| PAbs {n} : pterm (S n) -> pterm n
| PApp {n} {m} : pterm n -> pterm m -> pterm (n + m).

Fixpoint s_of_pterm {k : nat} (i o : nat) (pt : pterm k) : nat * nat * string :=
match pt with
| PVar => (i, S o, sofn o)
| PAbs pt' =>
  match pt' with
  | PVar =>
    let s := ("L " ++ (sofn i) ++ "." ++ (sofn i))%string in
    (S i, S o, s)
  | PAbs _ =>
    let (io', s') := s_of_pterm (S i) o pt' in
    match s' with
    | String _ s'' =>
      let s := ("L " ++ (sofn i) ++ s'')%string in
      (io', s)
    | _ => (0, 0, ""%string)
    end
  | PApp _ _ =>
    let (io', s') := s_of_pterm (S i) o pt' in
    let s := ("L " ++ (sofn i) ++ ".(" ++ s' ++ ")")%string in
    (io', s)
  end
| PApp pt1 pt2 =>
  let (io1, s1) := s_of_pterm i o pt1 in
  let (i1, o1) := io1 in
  let (io2, s2) := s_of_pterm i1 o1 pt2 in
  let s := match pt1 with
  | PAbs _ => ("(" ++ s1 ++ ") " ++ s2)%string
  | _ => (s1 ++ " " ++ s2)%string
  end in
  (io2, s)
end.

Definition sofpt {a : nat} (pt : pterm a) : string :=
  let (_, s) := s_of_pterm 0 0 pt in s.

Fixpoint sofpt' {k : nat} (pt : pterm k) : string :=
match pt with
| PVar => "v"
| PAbs pt' =>
  match pt' with
  | PVar => "L.v"
  | PAbs _ => "L" ++ sofpt' pt'
  | PApp _ _ => "L.(" ++ sofpt' pt' ++ ")"
  end
| PApp pt1 pt2 =>
  match pt1 with
  | PAbs _ => "(" ++ sofpt' pt1 ++ ") " ++ sofpt' pt2
  | _ => sofpt' pt1 ++ " " ++ sofpt' pt2
  end
end.

Eval compute in sofpt (PAbs (PAbs (PApp PVar (PAbs (PApp PVar PVar))))).
Eval compute in sofpt' (PAbs (PAbs (PApp PVar (PAbs (PApp PVar PVar))))).

(* Reductions *)

Theorem pterm_comm {A : Type} {n m : nat} : pterm (m + n) -> pterm (n + m).
Proof. rewrite Nat.add_comm. intro h. apply h. Qed.

Fixpoint psubst {a b : nat} (u : pterm a) (pt : pterm (S b)) : pterm (a + b) :=
match pt in pterm (S b) return (pterm (b + a) -> pterm (a + b)) -> pterm (a + b) with
| PVar => fun H => H u
| PAbs pt' => fun _ => PAbs (psubst u pt')
| PApp pt1 pt2 => fun _ => PApp (psubst u pt1) pt2
end pterm_comm.

(* pterm (S b) + c *)



(* Abscount *)

(*
Inductive reduced : nat -> Prop :=
| Failure (a : nat) : reduced a
| Success {a : nat} : pterm a -> reduced a.

Fixpoint reduce {a : nat} (pt : pterm (S a)) : reduced a :=
match pt with
| PVar => Failure 0
| PAbs pt' =>
  match reduce pt' with
  | Success pt'' => Success (PAbs pt'')
  | Failure => Failure
  end
| PApp (PAbs pt1) pt2 =>
  Success (psubst pt2 pt1)
| PApp pt1 pt2 =>
  match reduce pt1 with
  | Success pt1' => Success (PApp pt1' pt2)
  | Failure =>
    match reduce pt2 with
    | Success pt2' => Success (PApp pt1 pt2')
    | Failure => Failure
    end
  end
end.
*)



