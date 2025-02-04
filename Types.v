
Require Import String.

Require Import Aux.

Inductive type : Type :=
| TVar : nat -> type
| TImp : type -> type -> type.

Fixpoint softy (ty : type) : string :=
match ty with
| TVar n => sofn n
| TImp ty1 ty2 =>
  match (ty1, ty2) with
  | (TVar n, TVar m) => sofn n ++ " -> " ++ sofn m
  | (TVar n, _) => sofn n ++ " -> " ++ softy ty2
  | (_, TVar m) => "(" ++ softy ty1 ++ ") -> " ++ sofn m 
  | _ => "(" ++ softy ty1 ++ ") -> " ++ softy ty2
  end
end.