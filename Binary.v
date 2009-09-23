Require Export CSDL.Basics Bvector List Arith Euclid.

Inductive endianness := BigEndian | LittleEndian.

Definition overflow := bool.

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
    nat_of_bin tt' = nat_of_bin t + nat_of_bin t'

}.

Definition bit := bool.
Definition bits (n : nat) := vector bit n.

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
             | _ => Some (constant_vector t false)
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

Definition one_binary_le {n : nat} : bits n :=
  fst (bits_succ _ (constant_vector n false)).
    
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

Lemma nat_of_binary_inverse n (t : nat) (b : bits t) : binary_of_nat_be t n = Some b ->
  nat_of_binary_be b = n.
Proof with auto with *. intros n t b Htb. generalize dependent t. induction n ; intros...
  Opaque binary_of_nat_be.

  induction t... rewrite binary_of_nat_be_n_O in Htb. simpdep.
  simpl. clear. induction t...

  simpl in *. Transparent binary_of_nat_be. simpl in *. destruct n.
  destruct t... simpdep. clear. induction t...

  case_eq (binary_of_nat_be t (S n)); [intros b' Hb'Sn | intros Hb'Sn ].
  rewrite Hb'Sn in Htb.
  specialize (IHn _ _ Hb'Sn).

  case_eq (bits_succ_be t b'); intros sb bo Hsb.
  rewrite Hsb in *. destruct bo... program_simpl.
  now apply nat_of_binary_bits_succ_be in Hsb.

  now rewrite Hb'Sn in *.
Qed.

Lemma nat_of_binary_representation `{R : Representable t n} : 
  nat_of_binary_be (representation t n) = n.
Proof with auto with *.
  intros. destruct R. now apply nat_of_binary_inverse.
Qed.

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
  
Definition coerce_bits {n m} (c : bits n) (H : n = m) : bits m.
Proof. intros ; subst. exact c. Defined.

Equations(nocomp) vector_firstn {A} {l : nat} (s : nat) (c : vector A l) (Hsl : s < l) : vector A s :=
vector_firstn A ?(O) s Vnil Hsl :=! Hsl ;
vector_firstn A ?(S n) O (Vcons a n v) Hsl := Vnil ;
vector_firstn A ?(S n) (S m) (Vcons a n v) Hsl := Vcons a (vector_firstn m v _).

  Next Obligation. omega. Defined.

  Next Obligation. revert s Hsl ; induction c ; intros ;
    simp vector_firstn ; auto with * ; destruct s ; simp vector_firstn.
  Defined.
  
Equations(nocomp) vfold_right {A : nat -> Type} {B} (f : Π n, B -> A n -> A (S n)) (e : A 0) {n} (v : vector B n) : A n := 
vfold_right A B f e ?(O) Vnil := e ;
vfold_right A B f e ?(S n) (Vcons hdv n tlv) := 
  f n hdv (vfold_right f e tlv).

Equations(nocomp) vfold_right2 {A : nat -> Type} {B C} 
  (f : Π n, B -> C -> A n -> A (S n)) (e : A 0) {n} (v : vector B n) (v' : vector C n) : A n := 
vfold_right2 A B C f e ?(O) Vnil Vnil := e ;
vfold_right2 A B C f e ?(S n) (Vcons hdv n tlv) (Vcons hdv' n tlv') := 
  f n hdv hdv' (vfold_right2 f e tlv tlv').

Definition bits_plus_be {n} (x y : bits n) : bits n * overflow :=
  vfold_right2 (A:=fun n => (bits n * overflow)%type) (fun n b b' r => 
    let '(rest, carry) := r in
    let '(b, carry) := 
      match b, b' with
        | true, true => (carry, true) 
        | false, false => (carry, false)
        | true, false | false, true => (negb carry, carry)
      end
    in (Vcons b rest, carry))
  (Vnil, false) x y.

Instance: Have (pow_of_2 (S n) > 0).
Proof. reduce_goal. simp pow_of_2. induction n ; simpl ; omega. Qed.

Lemma bits_plus_be_correct_full n : forall (t t' : bits n) tt' o, bits_plus_be t t' = (tt', o) ->
  let add' := nat_of_binary_be t + nat_of_binary_be t' in
    if o then add' >= pow_of_2 n /\ nat_of_binary_be tt' = add' - pow_of_2 n
    else nat_of_binary_be tt' = add'.
Proof.
  intros. revert o H. induction t ; intros ; depelim t' ; try depelim tt'. simpl in *. reflexivity.

  destruct o.
  unfold bits_plus_be in H.
  simp vfold_right2 in H.
  case_eq (bits_plus_be t t'). intros. specialize (IHt _ _ _ H0).
  unfold bits_plus_be in H0. unfold bit in * ; rewrite H0 in H.
  clear H0.
  
  destruct a. destruct a0 ; noconf H ; program_simpl.
  assert (add' >= pow_of_2 (S n)) by (subst add'; simpl; omega).
  split. simpl in H ; omega. destruct a1. program_simpl. rewrite H1.
  subst add'. omega. subst add'. rewrite IHt. omega.

  assert (add' >= pow_of_2 (S n)) by (subst add'; simpl; omega).
  split. simpl in H1 ; omega. rewrite H0.
  subst add'. omega.

  destruct a0 ; noconf H ; program_simpl.
  assert (add' >= pow_of_2 (S n)) by (subst add'; simpl; omega).
  split. simpl in H1 ; omega. rewrite H0.
  subst add'. omega.

  subst add'.
  unfold bits_plus_be in H. simp vfold_right2 in H.
  case_eq (bits_plus_be t t'). intros. specialize (IHt _ _ _ H0).
  unfold bits_plus_be in H0. unfold bit in * ; rewrite H0 in H.
  clear H0.
  destruct a ; destruct a0 ; simpl in * ; noconf H ; simpl ; try rewrite IHt ; try omega.
  destruct a1. program_simpl. rewrite H0. omega.
  assumption.
Qed.

Lemma bits_plus_be_correct n : forall (t t' : bits n) tt', bits_plus_be t t' = (tt', false) ->
  nat_of_binary_be tt' = nat_of_binary_be t + nat_of_binary_be t'.
Proof.
  intros. apply (bits_plus_be_correct_full _ _ _ _ _ H).
Qed.

Program Instance bvec_binary_be n : Binary BigEndian (bits (S n)) := {
  bin_size t := S n ;
  
  bin_of_nat := binary_of_nat_be (S n);
  nat_of_bin := nat_of_binary_be;

  bin_succ := bits_succ_be (S n) ;

  bin_plus := bits_plus_be
}.

  Next Obligation. now apply nat_of_binary_inverse. Qed.

  Next Obligation. Admitted.

  Next Obligation. now erewrite nat_of_binary_bits_succ_be. Qed.
  Next Obligation. now apply bits_plus_be_correct. Qed.
