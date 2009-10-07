Require Export CSDL.Basics CSDL.Vector List Arith Euclid.

Open Local Scope vect_scope.

Inductive endianness := BigEndian | LittleEndian.

Definition overflow := bool.
Definition borrow := bool.

Class Binary (en : endianness) (T : Type) := {
  bin_size : T -> nat ;
  
  bin_of_nat : nat -> option T ;
  nat_of_bin : T -> nat ;
  nat_of_bin_of_nat : forall n t, bin_of_nat n = Some t -> nat_of_bin t = n ;
  bin_of_nat_of_bin : forall t, bin_of_nat (nat_of_bin t) = Some t ;

  bin_succ : T -> T * overflow;
  bin_succ_correct : forall t t', bin_succ t = (t', false) -> 
    nat_of_bin t' = S (nat_of_bin t) ;

  bin_plus : T -> T -> T * overflow;
  bin_plus_correct : forall t t' tt', bin_plus t t' = (tt', false) ->
    nat_of_bin tt' = nat_of_bin t + nat_of_bin t' ;

  bin_minus : T -> T -> T * overflow;
  bin_minus_correct : forall t t' tt', bin_minus t t' = (tt', false) ->
    nat_of_bin tt' = nat_of_bin t - nat_of_bin t' ;

  bin_mult : T -> T -> T * overflow;
  bin_mult_correct : forall t t' tt', bin_mult t t' = (tt', false) ->
    nat_of_bin tt' = nat_of_bin t * nat_of_bin t'
}.

Definition bit := bool.
Definition bits (n : nat) := vector bit n.
Definition byte := bits 8.

Definition zero {n} : bits n := constant_vector n false.
Definition full {n} : bits n := constant_vector n true.

Hint Extern 4 => progress (unfold hide_pattern in *) : Below.

Global Transparent div2 div2_rest pow_of_2 vector_append_one constant_vector. 

Delimit Scope bin_scope with bin.
Bind Scope bin_scope with bits.
Notation "1" := true : bin_scope.
Notation "0" := false : bin_scope.
Open Local Scope bin_scope.

(** Binary equality *)

Equations(nocomp) binary_eq {n} (x y : bits n) : bool :=
binary_eq ?(0) Vnil Vnil := true ;
binary_eq ?(S n) (Vcons a n x) (Vcons b n y) := bool_eq a b && binary_eq x y.

Lemma binary_eq_refl n (b : bits n) : binary_eq b b = true.
Proof. intros. remember b as b'. rewrite Heqb' at 1. funind (binary_eq b b') foo. 
  rewrite bool_eq_refl. rewrite IHbinary_eq_ind. reflexivity.
  simp binary_eq in foo. rewrite bool_eq_refl in foo. assumption.
Qed.

Instance const_eq : EqDec (bits n) eq.
Proof. 
intros n. red. intros. case_eq (binary_eq x y) ; [ left | right ].

  funind (binary_eq x y) foo. reflexivity.
  red. rewrite andb_true_iff in x. destruct x.
  specialize (IHbinary_eq_ind H1).
  apply bool_eq_ok in H. subst.
  simp binary_eq in foo. rewrite bool_eq_refl in foo. 
  specialize (IHbinary_eq_ind foo). congruence.

  funind (binary_eq x y) foo. red ; intros.
  red in H. noconf H. simp binary_eq in foo.
  rewrite bool_eq_refl, binary_eq_refl in foo.
  simpl in foo. discriminate.
Qed.

Equations(nocomp) binary_shiftl {n} (t : bits n) : bits n * overflow :=
binary_shiftl O Vnil := (Vnil, false) ;
binary_shiftl (S n) (Vcons a n v) := 
  let '(v', overflow) := binary_shiftl v in
    (Vcons overflow v', a).

Equations(nocomp) binary_shiftl_full {n} (t : bits n) : bits (S n) :=
binary_shiftl_full O Vnil := zero ;
binary_shiftl_full (S n) (Vcons a n v) := 
  let v' := binary_shiftl_full v in (a |:| v').

Equations(nocomp) binary_shiftl_n {n} (t : bits n) (m : nat) : bits n * overflow :=
binary_shiftl_n n t O := (t, false) ;
binary_shiftl_n n t (S m) <= binary_shiftl t => {
  binary_shiftl_n n t (S m) (pair t' true) := (t', true) ;
  binary_shiftl_n n t (S m) (pair t' false) := binary_shiftl_n t' m }.

Equations(nocomp) binary_shiftl_n_full {n} (t : bits n) (m : nat) : bits (m + n) :=
binary_shiftl_n_full n t O := t ;
binary_shiftl_n_full n t (S m) := binary_shiftl_full (binary_shiftl_n_full t m).
    
Global Transparent binary_shiftl binary_shiftl_n.
Global Transparent binary_shiftl_full binary_shiftl_n_full.

(** * Routine to add three bits and compute a new bit and a carry. *)

Definition add_bits_spec (x y c : bool) :=
  (xorb (xorb x y) c, (x && y) || (y && c) || (x && c)).

Definition add_bits (x y c : bool) :=
  if x then 
    if y then (c, true)
    else 
      if c then (false, c)
      else (x, c)
  else
    if y then 
      if c then (false, c)
      else (y, c)
    else (c, false).

Lemma add_bits_correct x y c : add_bits x y c = add_bits_spec x y c.
Proof.
  destruct x ; destruct y ; destruct c ; compute ; try reflexivity.
Qed.

Lemma binary_eq_eq {n} {x y : bits n} : binary_eq x y = true -> x = y.
Proof.
  intros. funind (binary_eq x y) eqxy. destruct recres.
  simp binary_eq in eqxy. rewrite andb_b_true in x. rewrite x in *.
  simpl in *. rewrite eqxy in IHbinary_eq_ind. apply bool_eq_ok in x. subst.
  rewrite IHbinary_eq_ind by auto. reflexivity.

  rewrite andb_b_false in x. discriminate.
Qed.

Require Import BoolEq.

Lemma binary_eq_neq {n} {x y : bits n} : binary_eq x y = false -> x <> y.
Proof.
  intros. funind (binary_eq x y) eqxy. destruct recres.
  simp binary_eq in eqxy. rewrite andb_b_true in x. rewrite x in *.
  simpl in *. red ; intros. noconf H. rewrite bool_eq_refl in x. discriminate.

  red ; intros H ; noconf H. simp binary_eq in eqxy. 
  rewrite bool_eq_refl in *.
  simpl in *. elim (IHbinary_eq_ind eqxy). reflexivity.
Qed.

Transparent binary_eq.

Definition coerce_bits {n m} (c : bits n) (H : n = m) : bits m.
Proof. intros ; subst. exact c. Defined.

(** Orders *)

Class BoolReflexive {A} (R : A -> A -> bool) := 
  reflexivityb : forall x, R x x = true.

Class BoolIrreflexive {A} (R : A -> A -> bool) := 
  irreflexivityb : forall x, R x x = false.

Class BoolSymmetric {A} (R : A -> A -> bool) := 
  symmetryb : forall x y, R x y = true -> R y x = true.

Class BoolAntiSymmetric {A} (R : A -> A -> bool) := 
  antisymmetryb : forall x y, R x y = true -> R y x = false.

Class BoolTransitive {A} (R : A -> A -> bool) := 
  transitivityb : forall x y z, R x y = true -> R y z = true -> R x z = true.

(** * From and to [positive] *)

Require Import BinPos.

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

(** For [binary_of_pos] preconditions. *)

Hint Extern 3 (Have (Psize _ = _)) => reflexivity : typeclass_instances.
Hint Extern 3 (Have (Psize ?x <= ?y)%nat) => apply (@leb_complete (Psize x) y eq_refl) : typeclass_instances.

Eval compute in (binary_of_pos_be 3 (5%positive)).
Eval compute in (binary_of_pos_be 3 (6%positive)).
Eval compute in (binary_of_pos_be 32 (6%positive)).
Eval compute in (binary_of_pos_be 32 (255%positive)).

Eval compute in (binary_of_pos_be 32 (pow_of_2_positive 32 - 1)).

Program Definition max_int n : bits n := 
  match n with O => (@zero 0) | S n => (@binary_of_pos_be (S n) (pow_of_2_positive (S n) - 1) _) end.

  Next Obligation. red. induction n0. simpl. auto. 
    simpl. case_eq_rew (pow_of_2_positive n0); simpl in *; omega.
  Qed.

Eval compute in (max_int 32).


Definition binary_inverse {n} (b : bits n) := Bneg _ b.

Lemma binary_inverse_involutive {n} (b : bits n) : binary_inverse (binary_inverse b) = b.
Proof. intros. unfold binary_inverse. unfold Bneg.
  induction b ; simpl ; auto. rewrite negb_involutive.
  now rewrite IHb.
Qed.

Lemma binary_inverse_is_constant {n} (b : bits n) c : binary_inverse b = constant_vector n c -> 
  b = constant_vector n (negb c).
Proof. 
  induction b ; simpl ; intros ; auto.
  noconf H. rewrite negb_involutive. 
  rewrite (IHb (negb a)) at 1. 
  rewrite negb_involutive. reflexivity. assumption.
Qed.

Lemma binary_inverse_constant {n} c : 
  binary_inverse (constant_vector n c) = constant_vector n (negb c).
Proof. 
  induction n ; simpl ; intros ; auto. rewrite IHn. reflexivity.
Qed.

Lemma binary_inverse_vector_append {n m} (v : bits n) (w : bits m) :
  binary_inverse (vector_append v w) = vector_append (binary_inverse v) (binary_inverse w).
Proof. intros. Opaque vector_append.
  funind (vector_append v w) vw.
  rewrite IHvector_append_ind. reflexivity.
Qed.

Hint Rewrite @binary_inverse_constant 
  @binary_inverse_involutive 
  @binary_inverse_vector_append : binary.
