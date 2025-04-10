
Require Import String.

Fixpoint sofn (n : nat) : string :=
match n with
| 0 => "0"
| S (S (S (S (S (S (S (S (S (S 0))))))))) => "X"
| S (S (S (S (S (S (S (S (S (S n))))))))) => "X" ++ sofn n
| S (S (S (S (S 0)))) => "V"
| S (S (S (S (S n)))) => "V" ++ sofn n
| S 0 => "i"
| S n => "i" ++ sofn n
end.
