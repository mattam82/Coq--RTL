Require Import CSDL.Binary CSDL.Vector CSDL.BinaryBe.
Require Import Show.

Equations(nocomp) vmap {A B n} (f : A -> B) (v : vector A n) : vector B n :=
vmap A B ?(0) f Vnil := Vnil ;
vmap A B ?(S n) f (Vcons a n v) := Vcons (f a) (vmap f v).

Equations(nocomp) vector_split {A n m} (v : vector A (n + m)) : vector A n * vector A m :=
vector_split A O m v := (Vnil, v) ;
vector_split A (S n) m (Vcons a _ v') := let '(l, r) := vector_split v' in
  (Vcons a l, r).

Equations vfold_left {A B n} (f : B -> A -> B) (v : vector A n) (b : B) : B :=
vfold_left A B ?(0) f Vnil b := b ;
vfold_left A B ?(S n) f (Vcons a n v) b := vfold_left f v (f b a).

Global Transparent vfold_left.

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

Definition byte := vector bit 8.

Notation hexa_byte := (vector hexa_base 2).

Open Local Scope string_scope.

Equations(nocomp noind) print_hexa_byte (h : vector hexa_base 2) : string :=
print_hexa_byte (Vcons h _ (Vcons l _ Vnil)) := "0x" +++ [print_hexa_base h] +++ [print_hexa_base l].

Global Transparent print_hexa_byte.

Definition hexa_of_byte (b : byte) :=
  let '(high, low) := vector_split (n:=4) (m:=4) b in
    Vcons (to_hexa high) (Vcons (to_hexa low) Vnil).

Global Transparent vector_split.

Require Import Representable.
Eval compute in (hexa_of_byte (representation 8 5)).

Eval compute in (hexa_of_byte (representation 8 5)).
  
Instance: Show hexa_byte := { show := print_hexa_byte }.

Open Local Scope string_scope.

Definition print `{Show T} (a : T) : String.string := shows (show a).

Eval compute in (print (hexa_of_byte (representation 8 6))).
Eval compute in (print (hexa_of_byte (representation 8 45))).
Eval compute in (print (hexa_of_byte (representation 8 90))).
Eval compute in (print (hexa_of_byte (representation 8 127))).
Time Eval vm_compute in (print (hexa_of_byte (representation 8 255))).

(* Time Eval vm_compute in (binary_of_nat_be 32 (pow_of_2 16 - 1)). *)

Require Import BinPos.
Print positive.
Open Local Scope positive_scope.
Obligation Tactic := idtac.
Program Fixpoint binary_of_pos_le (n : nat) : forall (p : positive) `{Hs : Have (Psize p = n)}, bits n :=
  match n with
    | 0%nat => λ p Hp, !
    | S n => λ p Hp, 
      match p with
        | 1 => Vcons true Vnil
        | p~0 => Vcons false (binary_of_pos_le n p _)
        | p~1 => Vcons true (binary_of_pos_le n p _)
      end
  end.

Print eq_add_S.
About le_S_n.
Lemma le_S_n_trans n m : (S n <= S m -> n <= m)%nat.
Proof. intros. depind H. apply le_n.
  destruct m. inversion H. apply le_S. apply IHle ; auto.
Defined.

Hint Resolve le_S_n_trans.

Lemma eq_add_S_trans n m : S n = S m -> n = m.
Proof. intros. congruence. Defined.
Hint Resolve eq_add_S_trans.

Obligation Tactic := program_simplify.


  Next Obligation. unfold Have in *. intros. revert Hp. destruct p; simpl; absurd_arith. Qed.

  Next Obligation. unfold Have in *. simpl in Hp. apply eq_add_S_trans in Hp. assumption. Defined.

  Next Obligation. 
    unfold Have in *. 
    simpl in Hp. apply eq_add_S_trans in Hp. assumption.
  Defined.

  Next Obligation. 
    unfold Have in *. 
    simpl in Hp. apply eq_add_S_trans in Hp. assumption.
  Defined.

Implicit Arguments binary_of_pos_le [ [ Hs ] ].

Program Fixpoint binary_of_pos_be (n : nat) : forall (p : positive) `{Hs : Have (Psize p <= n)%nat}, 
  bits n :=
  match n with
    | 0%nat => λ p Hp, !
    | S n => λ p Hp, 
      match p with
        | 1 => vector_append_one zero true
        | p~0 => vector_append_one (binary_of_pos_be n p _) false
        | p~1 => vector_append_one (binary_of_pos_be n p _) true
      end
  end.

  Next Obligation. unfold Have in *. intros. revert Hp. destruct p; simpl; absurd_arith. Qed.

  Next Obligation. unfold Have in *. simpl in Hp. apply le_S_n_trans. assumption. Defined.

  Next Obligation. 
    unfold Have in *. 
    simpl in Hp. apply le_S_n_trans in Hp. assumption.
  Defined.

Implicit Arguments binary_of_pos_be [ [ Hs ] ].

Fixpoint pos_be_of_le (p : positive) (acc : positive -> positive) : positive :=
  match p with
    | 1 => acc 1
    | p~0 => pos_be_of_le p (fun x => xO (acc x))
    | p~1 => pos_be_of_le p (fun x => xI (acc x))
  end.

Set Printing All.
Eval compute in (5%positive).

Eval compute in (pos_be_of_le (5%positive) (fun x => x)).

Hint Extern 3 (Have (Psize _ = _)) => reflexivity : typeclass_instances.

About leb_complete.

Hint Extern 3 (Have (Psize ?x <= ?y)%nat) => apply (@leb_complete (Psize x) y eq_refl) : typeclass_instances.

Unset Printing All.
Eval compute in (binary_of_pos_le 3 (5%positive)).
Eval compute in (binary_of_pos_le 3 (pos_be_of_le (6%positive) (fun x => x))).

Eval compute in (binary_of_pos_be 3 (5%positive)).
Eval compute in (binary_of_pos_be 3 (6%positive)).

Eval compute in (binary_of_pos_be 32 (6%positive)).

Eval compute in (binary_of_pos_be 32 (255%positive)).

Require Import BinPos.

Fixpoint pow_of_2_pos (n : nat) : positive :=
  match n with
    | O => 1
    | S n => (pow_of_2_pos n)~0
  end.

Eval compute in (binary_of_pos_be 32 (pow_of_2_pos 32 - 1)).

Program Definition max_int n : bits n := 
  match n with O => (@zero 0) | S n => (@binary_of_pos_be (S n) (pow_of_2_pos (S n) - 1) _) end.

  Next Obligation. red. induction n0. simpl. auto. 
    simpl. case_eq_rew (pow_of_2_pos n0); simpl in *; omega.
  Qed.

Eval compute in (max_int 32).

Fixpoint hexa_of_bytes {n} : bits (n * 4) -> vector hexa_base n :=
  match n with
    | O => λ _, Vnil
    | S n => λ b, 
      let '(high, low) := vector_split (n:=4) (m:=n * 4) b in
        Vcons (to_hexa high) (hexa_of_bytes low)
  end.

About vfold_right.


Definition print_hexa_bytes {n} (h : vector hexa_base n) : string :=
 vfold_left (λ rest base, rest ++ [print_hexa_base base]) h "0x".

Definition show_hex_mult_4 n : Show (bits (n * 4)) := 
  print_hexa_bytes ∘ hexa_of_bytes.

Require Import Ascii.

Definition char_of_bool (b : bool) : ascii := (if b then "1" else "0")%char.

Definition print_bits {n} (h : bits n) : string :=
 vfold_left (λ rest (b : bool), rest ++ [char_of_bool b]) h "0b".

Definition show_bits n : Show (bits n) := print_bits.

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

(* Hint Extern 4 (Show (bits ?n)) => idtac n ; apply (build_show n) : typeclass_instances. *)

Ltac build_show n :=
  let res := eval compute in (euclid n 4) in
    match res with
      | (?q, O) => apply (show_hex_mult_4 q)
      | _ => apply (show_bits n)
    end.

Hint Extern 4 (Show (bits ?n)) => build_show n : typeclass_instances.

Open Local Scope string_scope.

Eval vm_compute in (print (max_int 64)).
Eval vm_compute in (print (max_int 128)).
Eval vm_compute in (print (max_int 512)).
Eval vm_compute in (print (bin_plus (max_int 4) (Binary.zero))).

Eval vm_compute in (print (bin_minus (max_int 4) BinaryBe.one)).

Eval vm_compute in (eq_refl : (print (fst (bin_mult (representation 8 4) (representation 8 5)))) = "0x14").

Eval vm_compute in (print (bin_mult (max_int 4) BinaryBe.one)).
Eval vm_compute in (print [: fst (bin_mult (representation 8 4) (representation _ 5))]).
