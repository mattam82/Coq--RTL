Require Import CSDL.Binary CSDL.BinaryBe CSDL.BinaryLe.

(** * Representation of naturals in binary. 

   The [Representable t c] class allows to check at compile-time that a
   natural number [c] is representable as a binary number on [t] bytes.
   The representation is big-endian.
   *)

Class Representable (e : endianness) (t : nat) (c : nat) := mkRepresentable {
  representation : bits t ;
  is_representation : 
    if e then binary_of_nat_be t c = Some representation
    else binary_of_nat_le t c = Some representation }.

(** This instance tries to run a conversion function and produces a proof 
   that the natural is representable. *)

Hint Extern 2 (Representable LittleEndian ?t ?c) => 
  exact (mkRepresentable LittleEndian t c _ eq_refl) : typeclass_instances.
Hint Extern 5 (Representable ?e ?t ?c) => 
  apply (@mkRepresentable BigEndian t c _ eq_refl) : typeclass_instances.

(* let x := eval compute in (binary_of_nat_be t c) in *)
  (* match x with *)
  (*   | Some ?x =>  *) 
    (* | None =>  *)
    (*   fail 3 c " is not representable on " t " bytes" *)
  (* end *)

Implicit Arguments representation [ [e] [Representable] ].

Eval compute in (representation (e:=BigEndian) 3 7).
Eval compute in (representation 3 7).

Lemma nat_of_binary_representation `{R : Representable BigEndian t n} : 
  nat_of_binary_be (representation t n) = n.
Proof with auto with *.
  intros. destruct R. now apply nat_of_binary_inverse.
Qed.

Definition fourty_five := (representation 32 45).
Definition ninety := (representation 32 90).

Check (convertible (fst (binary_minus_be ninety fourty_five)) fourty_five).
Check (convertible (nat_of_binary_be (fst (binary_minus_be fourty_five ninety))) 45).

Eval compute in (binary_minus_be (one (n:=4)) zero). 
Eval compute in (nat_of_binary_be (fst (binary_minus_be (one (n:=4)) (representation _ 5)))).
Eval compute in (nat_of_binary_be (fst (binary_minus_be (representation 5 5) (representation _ 5)))).
Eval compute in (binary_minus_be (representation 5 5) (representation _ 5)).


Eval compute in (binary_shiftl (one (n:=4))).
Eval compute in (binary_shiftl (fst (binary_shiftl (one (n:=4))))).
Eval compute in (binary_shiftl (fst (binary_shiftl (one (n:=1))))).
Eval compute in (binary_shiftl_n (one (n:=4)) 0).
Eval compute in (binary_shiftl_n (one (n:=4)) 4).
Eval compute in (binary_shiftl_n (one (n:=4)) 5).

Eval compute in (binary_mult_be (one (n:=4)) (one (n:=4))).
Eval compute in (binary_mult_be (one (n:=3)) (representation 4 3)).
Eval compute in (binary_mult_be (representation 4 2) (representation 4 3)).
Eval compute in (nat_of_binary_be (fst (binary_mult_be (representation 4 2) (representation 4 3)))).
Eval compute in (nat_of_binary_be (fst (binary_mult_be (representation 10 16) (representation 10 2)))).
Eval compute in (nat_of_binary_be (fst (binary_mult_be (representation 10 16) (representation 10 0)))).
Eval compute in (nat_of_binary_be (fst (binary_mult_be (representation 10 0) (representation 10 4)))).
Eval compute in (nat_of_binary_be (fst (binary_mult_be (representation 10 0) (representation 10 4)))).
Eval compute in (nat_of_binary_be (fst (binary_mult_be (representation 10 1) (representation 10 4)))).
Eval compute in (nat_of_binary_be (fst (binary_mult_be (representation 10 2) (representation 10 4)))).
Eval compute in (nat_of_binary_be (fst (binary_mult_be (representation 10 2) (representation 10 4)))).
Eval compute in (nat_of_binary_be (fst (binary_mult_be (representation 10 3) (representation 10 3)))).


Eval compute in (nat_of_bin (fst (bin_plus (representation 32 16) (representation 32 4)))).
Eval compute in (nat_of_bin (fst (bin_plus (representation 32 90) (representation 32 45)))).
Eval compute in (nat_of_bin (fst (bin_plus fourty_five ninety))).

Eval compute in (nat_of_bin (fst (bin_minus fourty_five ninety))).
Eval compute in (nat_of_bin (fst (bin_minus ninety fourty_five))).
