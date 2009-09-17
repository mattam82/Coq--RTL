Require Export CSDL.Basics Bvector List Arith Euclid.

Definition bit := bool.
Definition bits (n : nat) := vector bit n.
Definition overflow := bool.

Program Definition modulo_nat (n m : nat) `{Have (m > 0)} : nat :=
  modulo m _ n.

Program Definition quotient_nat (n m : nat) `{Have (m > 0)} : nat :=
  quotient m _ n.

Equations(nocomp) div2_rest (n : nat) : nat * bit :=
div2_rest O := (0, false) ;
div2_rest (S O) := (0, true) ;
div2_rest (S (S n)) := let (n', rest) := (div2_rest n) in (S n', rest).

Equations(nocomp) div2 (n : nat) : nat :=
div2 O := 0 ;
div2 (S O) := 0 ;
div2 (S (S n)) := S (div2 n).

Equations(nocomp) pow_of_2 (n : nat) : nat :=
pow_of_2 O := 1 ;
pow_of_2 (S n) := 2 * pow_of_2 n.

Equations(nocomp) constant_vector {A} (n : nat) (x : A) : vector A n :=
constant_vector A O x := Vnil ;
constant_vector A (S n) x := Vcons x (constant_vector n x).

Equations(nocomp) vector_append {A} {n m : nat} (v : vector A n) (w : vector A m) : vector A (n + m) :=
vector_append A ?(O) m Vnil w := w ;
vector_append A ?(S n) m (Vcons a n x) w := Vcons a (vector_append x w).

Equations vector_append_one {A} {n : nat} (v : vector A n) (a : A) : vector A (S n) :=
vector_append_one A ?(O) Vnil w := Vcons w Vnil ;
vector_append_one A ?(S n) (Vcons a n x) w := Vcons a (vector_append_one x w).

Equations(nocomp) bits_succ (t : nat) (c : bits t) : bits t * overflow :=
bits_succ O v := (v, true) ;
bits_succ (S n) (Vcons true n v) := let (v', rest) := bits_succ n v in
  (Vcons false v', rest) ;
bits_succ (S n) (Vcons false n v) := (Vcons true v, false).

Equations(nocomp) bits_succ_be (t : nat) (c : bits t) : bits t * overflow :=
bits_succ_be O v := (v, true) ;
bits_succ_be (S n) (Vcons true n v) := let (v', rest) := bits_succ_be n v in
  (Vcons true v', rest) ;
bits_succ_be (S n) (Vcons false n v) := let (v', rest) := bits_succ_be n v in
  if rest then (Vcons true (constant_vector n false), false) 
  else (Vcons false v', false).

Hint Extern 4 => progress (unfold hide_pattern in *) : Below.

Fixpoint binary_of_nat_le (t : nat) (c : nat) : option (bits t) :=
  match c with
    | 0 => match t with 
             | 0 => None
             | S n => Some (constant_vector (S n) false)
           end
    | 1 => match t with 
             | 0 => None
             | S n => Some (Vcons true (constant_vector n false))
           end
    | S m => 
      match binary_of_nat_le t m with
        | None => None
        | Some m' => 
          let (m', overflow) := bits_succ t m' in
            if overflow then None
            else Some m'
      end
  end.

Fixpoint binary_of_nat_be (t : nat) (c : nat) : option (bits t) :=
  match c with
    | 0 => match t with 
             | 0 => None
             | S n => Some (constant_vector (S n) false)
           end
    | 1 => match t with 
             | 0 => None
             | S n => Some (vector_append_one (constant_vector n false) true)
           end
    | S m => 
      match binary_of_nat_be t m with
        | None => None
        | Some m' => 
          let (m', overflow) := bits_succ_be t m' in
            if overflow then None
            else Some m'
      end
  end.
    
(*
Equations(nostruct) binary_of_nat (t : nat) (c : nat) : option (bits t) :=
binary_of_nat t c ! c ;

binary_of_nat O _ := None ;
binary_of_nat (S n) O := Some (constant_vector (S n) false) ;
binary_of_nat (S n) (S O) := Some (Vcons true (constant_vector n false)) ;
binary_of_nat (S n) (S m) <= binary_of_nat (S n) m => {
  binary_of_nat (S n) (S m) None := None ;
  binary_of_nat (S n) (S m) (Some m') :=
    let (m', overflow) := bits_succ (S n) m' in
      if overflow then None
        else Some m' }.
*)    
    
  (* Next Obligation. *)
  (*   revert c. induction t. constructor. *)
  (*   destruct c. *)
  (*   constructor. *)
  (*   destruct c. *)
  (*   econstructor. *)
  (*   autorewrite with binary_of_nat. *)
  (*   constructor. destruct (div2_rest c). simp binary_of_nat.  *)
  (* Defined. *)

Global Transparent div2 div2_rest pow_of_2 bits_succ bits_succ_be vector_append_one constant_vector 
  binary_of_nat_le binary_of_nat_be.

Delimit Scope bin_scope with bin.
Bind Scope bin_scope with bits.

Notation " x |:| y " := (@Vcons _ x _ y) (at level 20, right associativity) : bin_scope.
Notation " [[ x .. y ]] " := (Vcons x .. (Vcons y Vnil) ..) : bin_scope.
Notation " [[]] " := Vnil : bin_scope.

Notation "1" := true : bin_scope.
Notation "0" := false : bin_scope.

Eval compute in (binary_of_nat_le 16 548).
Eval compute in (binary_of_nat_le 8 255).
Eval compute in (binary_of_nat_le 8 3).
Eval compute in (binary_of_nat_be 8 1).
Eval compute in (binary_of_nat_be 8 255).

Lemma binary_of_nat_le_O n : binary_of_nat_le 0 n = None.
Proof.
  induction n ; simpl ; auto. destruct n ; auto.
  rewrite IHn. reflexivity.
Qed.

Lemma binary_of_nat_be_O n : binary_of_nat_be 0 n = None.
Proof.
  induction n ; simpl ; auto. destruct n ; auto.
  rewrite IHn. reflexivity.
Qed.

(** The [Representable t c] class allows to check at compile-time that a
   natural number [c] is representable as a binary number on [t] bytes.
   The representation is big-endian.
   *)

Class Representable (t : nat) (c : nat) := mkRepresentable {
  representation : bits t ;
  is_representation : binary_of_nat_be t c = Some representation }.

(** This instance tries to run a conversion function and produces a proof 
   that the natural is representable. *)

Hint Extern 4 (Representable ?t ?c) => exact (mkRepresentable t c _ eq_refl) : typeclass_instances.

(* let x := eval compute in (binary_of_nat_be t c) in *)
  (* match x with *)
  (*   | Some ?x =>  *) 
    (* | None =>  *)
    (*   fail 3 c " is not representable on " t " bytes" *)
  (* end *)

Implicit Arguments representation [ [Representable] ].
Eval compute in (representation 3 7).
(* Eval compute in (representation 3 8). *)

Equations(nocomp) nat_of_binary_be {t : nat} (c : bits t) : nat :=
nat_of_binary_be ?(O) Vnil := O ;
nat_of_binary_be ?(S n) (Vcons b n v) := let rest := nat_of_binary_be v in
  if b then pow_of_2 n + rest else rest.

Equations(nocomp) nat_of_binary_le {t : nat} (c : bits t) : nat :=
nat_of_binary_le ?(O) Vnil := O ;
nat_of_binary_le ?(S n) (Vcons b n v) := let rest := nat_of_binary_le v in
  if b then 1 + 2 * rest else 2 * rest.

  Next Obligation.
  Proof. induction c. constructor.
    rewrite nat_of_binary_le_equation_2.
    constructor. assumption.
  Defined.

Global Transparent nat_of_binary_be nat_of_binary_le.

Eval compute in (nat_of_binary_be (representation 3 7)).

Lemma bits_succ_be_overflow (t : nat) (b : bits t) (c : bits t) : bits_succ_be t b = (c, true) ->
  b = c /\ b = constant_vector t true.
Proof with auto with *.
  intros. Opaque bits_succ_be. funind (bits_succ_be t b) indbits.

    now depelim c.

    destruct recres. destruct o... simpdep.
    simp bits_succ_be in indbits. 
    destruct_call bits_succ_be. destruct o ; simpdep... intuition (repeat subst ; auto).

    destruct recres. destruct o...
Qed.

Lemma nat_of_binary_bits_succ_be (t : nat) (b : bits t) (c : bits t) : bits_succ_be t b = (c, false) -> 
  nat_of_binary_be c = S (nat_of_binary_be b).
Proof with auto with *.
  intros.
  Opaque bits_succ_be binary_of_nat_be nat_of_binary_be.
  funind (bits_succ_be t b) indbits.
     
  destruct recres. program_simpl.
  simp bits_succ_be in indbits. case_eq (bits_succ_be n v); intros.
  rewrite H in *. simpdep.
  Transparent nat_of_binary_be. simpl.
  rewrite IHbits_succ_be_ind. ring.

  destruct recres. simp bits_succ_be in indbits.
  case_eq (bits_succ_be n v) ; intros. rewrite H in *. 
  case_eq o0; case_eq o; simpdep.
  apply bits_succ_be_overflow in H. program_simpl. 
  clear. induction n... simpl. rewrite plus_assoc, plus_0_r, <- plus_assoc. rewrite IHn.
  ring.

  simpl. assumption.
Qed.

Lemma binary_of_nat_be_n_O n : binary_of_nat_be (S n) 0 = Some (constant_vector (S n) false).
Proof with auto with *.
  induction n ; intros...
Qed.

Lemma nat_of_binary_inverse `{R : Representable t n} : 
  nat_of_binary_be (representation t n) = n.
Proof with auto with *.
  intros. destruct R. generalize dependent t. induction n ; intros...
  Opaque binary_of_nat_be. simpl.

  induction t... rewrite binary_of_nat_be_n_O in is_representation0. simpdep.
  simpl. clear. induction t...

  simpl in *. Transparent binary_of_nat_be. simpl in *. destruct n.
  destruct t... simpdep. clear. induction t...

  case_eq (binary_of_nat_be t (S n)); intros.
  rewrite H in is_representation0.
  specialize (IHn _ _ H).

  case_eq (bits_succ_be t b) ; intros.
  rewrite H0 in *. destruct o... program_simpl.
  now apply nat_of_binary_bits_succ_be in H0.

  now rewrite H in *.
Qed.
