Require Import CSDL.Binary.

Equations(nocomp) bits_succ_le {t} (c : bits t) : bits t * overflow :=
bits_succ_le O v := (v, true) ;
bits_succ_le (S n) (Vcons true n v) := let (v', rest) := bits_succ_le v in
  (Vcons false v', rest) ;
bits_succ_le (S n) (Vcons false n v) := (Vcons true v, false).

Fixpoint binary_of_nat_le (t : nat) (c : nat) : option (bits t) :=
  match c with
    | 0 => Some zero
    | 1 => match t with 
             | 0 => None
             | S n => Some (Vcons true zero)
           end
    | S m => 
      match binary_of_nat_le t m with
        | None => None
        | Some m' => 
          let (m', overflow) := bits_succ_le m' in
            if overflow then None
            else Some m'
      end
  end.

Definition one {n : nat} : bits n := 
  fst (bits_succ_le zero).

Global Transparent bits_succ_le.

Eval compute in (binary_of_nat_le 16 548).
Eval compute in (binary_of_nat_le 8 255).
Eval compute in (binary_of_nat_le 8 3).


Equations(nocomp) nat_of_binary_le {t : nat} (c : bits t) : nat :=
nat_of_binary_le ?(O) Vnil := O ;
nat_of_binary_le ?(S n) (Vcons b n v) := let rest := nat_of_binary_le v in
  if b then 1 + 2 * rest else 2 * rest.

Global Transparent nat_of_binary_le.
