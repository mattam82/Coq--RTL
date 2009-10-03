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

Lemma binary_eq_eq {n} {x y : bits n} : binary_eq x y = true -> x = y.
Proof.
  intros. funind (binary_eq x y) eqxy. destruct recres.
  simp binary_eq in eqxy. rewrite andb_b_true in x. rewrite x in *.
  simpl in *. rewrite eqxy in IHbinary_eq_ind. apply bool_eq_ok in x. subst.
  rewrite IHbinary_eq_ind by auto. reflexivity.

  rewrite andb_b_false in x. discriminate.
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
