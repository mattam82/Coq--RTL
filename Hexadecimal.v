Require Import CSDL.Binary CSDL.Vector CSDL.BinaryBe.
Require Import Show.

Inductive hexa_base :=
| H0 | H1 | H2 | H3 | H4 | H5 | H6 | H7 | H8 | H9 | A | B | C | D | E | F.

Open Local Scope char_scope.

Definition print_hexa_base h :=
  match h with
    | H0 => "0"
    | H1 => "1"
    | H2 => "2"
    | H3 => "3"
    | H4 => "4"
    | H5 => "5"
    | H6 => "6"
    | H7 => "7"
    | H8 => "8"
    | H9 => "9"
    | A => "a"
    | B => "b"
    | C => "c"
    | D => "d"
    | E => "e"
    | F => "f"
  end.

Definition hexa_succ h :=
  match h with
    | H0 => H1
    | H1 => H2
    | H2 => H3
    | H3 => H4
    | H4 => H5
    | H5 => H6
    | H6 => H7
    | H7 => H8
    | H8 => H9
    | H9 => A
    | A => B
    | B => C
    | C => D
    | D => E
    | E => F
    | F => H0
  end.

Definition to_hexa (v : vector bit 4) : hexa_base :=
  let fix aux n acc :=
    match n with
      | 0 => acc
      | S n => aux n (hexa_succ acc)
    end
  in aux (nat_of_binary_be v) H0.

Notation hexa_byte := (vector hexa_base 2).

Open Local Scope string_scope.

Fixpoint hexa_of_bytes {n} : bits (n * 4) -> vector hexa_base n :=
  match n with
    | O => λ _, Vnil
    | S n => λ b, 
      let '(high, low) := vector_split (n:=4) (m:=n * 4) b in
        Vcons (to_hexa high) (hexa_of_bytes low)
  end.

Definition print_hexa_bytes {n} (h : vector hexa_base n) : string :=
 vfold_left (λ rest base, rest ++ [print_hexa_base base]) h "0x".

Definition show_hex_mult_4 n : Show (bits (n * 4)) := 
  print_hexa_bytes ∘ hexa_of_bytes.

Definition string_of_bits {n} (h : bits n) : string :=
 vfold_left (λ rest (b : bool), rest ++ [char_of_bool b]) h "0b".

Definition show_bits n : Show (bits n) := string_of_bits.

(*
Lemma mult_n_Sm n m : (n * S m = n + n * m)%nat.
Proof. induction n ; simpl. reflexivity.
  intros.
  rewrite IHn. omega.
Defined.

Lemma mult_comm_trans (n m : nat) : (n * m = m * n)%nat.
Proof. intros n m. revert n. induction m ; intros. simpl. 
  induction n ; simpl. reflexivity. assumption.

  simpl. rewrite <- IHm. rewrite mult_n_Sm. reflexivity.
Defined.

Program Definition build_show n : Show (bits n) :=
  let '(quotient, remainder) := euclid n 4 in
    match remainder with
      | O => show_hex_mult_4 quotient
      | _ => show_bits n
    end.

  Next Obligation.
    pose (euclid_spec _ _ _ _ (symmetry Heq_anonymous)).
    destruct a. subst. rewrite mult_comm. rewrite plus_comm. simpl. reflexivity.
  Defined.

Eval compute in (euclid 32 4).

Hint Extern 4 (Show (bits ?n)) => idtac n ; apply (build_show n) : typeclass_instances. *)

Ltac build_show n :=
  let res := eval compute in (euclid n 4) in
    match res with
      | (?q, O) => apply (show_hex_mult_4 q)
      | _ => apply (show_bits n)
    end.

Hint Extern 4 (Show (bits ?n)) => build_show n : typeclass_instances.

Open Local Scope string_scope.

Require Import Representable.

Eval vm_compute in (print (max_int 4)).
Eval vm_compute in (print (max_int 64)).
Eval vm_compute in (print (max_int 128)).
Eval vm_compute in (print (max_int 512)).
Eval vm_compute in (print (bin_plus (max_int 4) (Binary.zero))).
Eval vm_compute in (print (bin_minus (max_int 4) BinaryBe.one)).
Eval vm_compute in (eq_refl : (print (fst (bin_mult (representation 8 4) (representation 8 5)))) = "0x14").
Eval vm_compute in (print (bin_mult (max_int 4) BinaryBe.one)).
Eval vm_compute in (print [: fst (bin_mult (representation 8 4) (representation _ 5))]).
