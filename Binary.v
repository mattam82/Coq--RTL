Require Export CSDL.Basics Bvector List Arith Euclid.

Inductive endianness := BigEndian | LittleEndian.

Definition overflow := bool.

Equations(nocomp) pow_of_2 (n : nat) : nat :=
pow_of_2 O := 1 ;
pow_of_2 (S n) := 2 * pow_of_2 n.

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

Equations(nocomp) div2_rest (n : nat) : nat * bit :=
div2_rest O := (0, false) ;
div2_rest (S O) := (0, true) ;
div2_rest (S (S n)) := let (n', rest) := (div2_rest n) in (S n', rest).

Equations(nocomp) div2 (n : nat) : nat :=
div2 O := 0 ;
div2 (S O) := 0 ;
div2 (S (S n)) := S (div2 n).

Equations(nocomp) constant_vector {A} (n : nat) (x : A) : vector A n :=
constant_vector A O x := Vnil ;
constant_vector A (S n) x := Vcons x (constant_vector n x).

Equations(nocomp) vector_append {A} {n m : nat} (v : vector A n) (w : vector A m) : vector A (n + m) :=
vector_append A ?(O) m Vnil w := w ;
vector_append A ?(S n) m (Vcons a n x) w := Vcons a (vector_append x w).

Equations vector_append_one {A} {n : nat} (v : vector A n) (a : A) : vector A (S n) :=
vector_append_one A ?(O) Vnil w := Vcons w Vnil ;
vector_append_one A ?(S n) (Vcons a n x) w := Vcons a (vector_append_one x w).

Definition zero {n} : bits n := constant_vector n false.
Definition one {n} : bits (S n) := vector_append_one (constant_vector n false) true.
Definition full {n} : bits n := constant_vector n true.

Equations(nocomp) bits_succ {t} (c : bits t) : bits t * overflow :=
bits_succ O v := (v, true) ;
bits_succ (S n) (Vcons true n v) := let (v', rest) := bits_succ v in
  (Vcons false v', rest) ;
bits_succ (S n) (Vcons false n v) := (Vcons true v, false).

Equations(nocomp) bits_succ_be {t} (c : bits t) : bits t * overflow :=
bits_succ_be O v := (v, true) ;
bits_succ_be (S n) (Vcons true n v) := let (v', rest) := bits_succ_be v in
  (Vcons true v', rest) ;
bits_succ_be (S n) (Vcons false n v) := let (v', rest) := bits_succ_be v in
  if rest then (Vcons true zero, false) 
  else (Vcons false v', false).

Hint Extern 4 => progress (unfold hide_pattern in *) : Below.

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
          let (m', overflow) := bits_succ m' in
            if overflow then None
            else Some m'
      end
  end.

Fixpoint binary_of_nat_be (t : nat) (c : nat) : option (bits t) :=
  match c with
    | 0 => Some zero
    | 1 => match t with 
             | 0 => None
             | S n => Some (vector_append_one zero true)
           end
    | S m => 
      match binary_of_nat_be t m with
        | None => None
        | Some m' => 
          let (m', overflow) := bits_succ_be m' in
            if overflow then None
            else Some m'
      end
  end.

Definition one_binary_le {n : nat} : bits n := 
  fst (bits_succ zero).
    
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

(* Lemma binary_of_nat_le_O n : binary_of_nat_le 0 n = None. *)
(* Proof. *)
(*   induction n ; simpl ; auto. destruct n ; auto. *)
(*   rewrite IHn. reflexivity. *)
(* Qed. *)

(* Lemma binary_of_nat_be_O n : binary_of_nat_be 0 n = None. *)
(* Proof. *)
(*   induction n ; simpl ; auto. destruct n ; auto. *)
(*   rewrite IHn. reflexivity. *)
(* Qed. *)

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

Lemma bits_succ_be_overflow (t : nat) (b : bits t) (c : bits t) : bits_succ_be b = (c, true) ->
  b = c /\ b = full.
Proof with auto with *.
  intros. Opaque bits_succ_be. funind (bits_succ_be b) indbits.

    now depelim c.

    destruct recres. destruct o... simpdep.
    simp bits_succ_be in indbits. 
    destruct_call @bits_succ_be. destruct o ; simpdep... intuition (repeat subst ; auto).

    destruct recres. destruct o...
Qed.

Lemma nat_of_binary_bits_succ_be (t : nat) (b : bits t) (c : bits t) : bits_succ_be b = (c, false) -> 
  nat_of_binary_be c = S (nat_of_binary_be b).
Proof with auto with *.
  intros.
  Opaque bits_succ_be binary_of_nat_be nat_of_binary_be.
  funind (bits_succ_be b) indbits.
     
  destruct recres. program_simpl.
  simp bits_succ_be in indbits. case_eq (bits_succ_be v); intros.
  rewrite H in *. simpdep.
  Transparent nat_of_binary_be. simpl.
  rewrite IHbits_succ_be_ind. ring.

  destruct recres. simp bits_succ_be in indbits.
  case_eq (bits_succ_be v) ; intros. rewrite H in *. 
  case_eq o0; case_eq o; simpdep.
  apply bits_succ_be_overflow in H. program_simpl. 
  clear. induction n... simpl. rewrite plus_assoc, plus_0_r, <- plus_assoc. 
  unfold zero in IHn. rewrite IHn. unfold full. ring.

  simpl. assumption.
Qed.

Lemma binary_of_nat_be_n_O n : binary_of_nat_be (S n) 0 = Some zero.
Proof with auto with *.
  induction n ; intros...
Qed.
Transparent binary_of_nat_be. 
Lemma nat_of_binary_inverse n (t : nat) (b : bits t) : binary_of_nat_be t n = Some b ->
  nat_of_binary_be b = n.
Proof with auto with *. intros n t b Htb. generalize dependent t. induction n ; intros...

  induction t... simpl in Htb. noconf Htb. 
  noconf Htb.

  simpl in *. destruct n.
  destruct t... simpdep. clear. induction t...

  case_eq (binary_of_nat_be t (S n)); [intros b' Hb'Sn | intros Hb'Sn ].
  rewrite Hb'Sn in Htb.
  specialize (IHn _ _ Hb'Sn).

  case_eq (bits_succ_be b'); intros sb bo Hsb.
  rewrite Hsb in *. destruct bo... program_simpl.
  now apply nat_of_binary_bits_succ_be in Hsb.

  now rewrite Hb'Sn in *.
Qed.

Lemma nat_of_binary_representation `{R : Representable t n} : 
  nat_of_binary_be (representation t n) = n.
Proof with auto with *.
  intros. destruct R. now apply nat_of_binary_inverse.
Qed.

Lemma pow_of_2_pos n : pow_of_2 n > 0.
Proof. induction n. auto. simpl. omega. Qed.

Equations(nocomp) vfold_right {A : nat -> Type} {B} (f : Π n, B -> A n -> A (S n)) (e : A 0) {n} (v : vector B n) : A n := 
vfold_right A B f e ?(O) Vnil := e ;
vfold_right A B f e ?(S n) (Vcons hdv n tlv) := 
  f n hdv (vfold_right f e tlv).

Equations(nocomp) vfold_right2 {A : nat -> Type} {B C} 
  (f : Π n, B -> C -> A n -> A (S n)) (e : A 0) {n} (v : vector B n) (v' : vector C n) : A n := 
vfold_right2 A B C f e ?(O) Vnil Vnil := e ;
vfold_right2 A B C f e ?(S n) (Vcons hdv n tlv) (Vcons hdv' n tlv') := 
  f n hdv hdv' (vfold_right2 f e tlv tlv').

Definition binary_plus_be {n} (x y : bits n) : bits n * overflow :=
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

Lemma binary_plus_be_correct_full n : forall (t t' : bits n) tt' o, binary_plus_be t t' = (tt', o) ->
  let add' := nat_of_binary_be t + nat_of_binary_be t' in
    if o then add' >= pow_of_2 n /\ nat_of_binary_be tt' = add' - pow_of_2 n
    else nat_of_binary_be tt' = add'.
Proof.
  intros. revert o H. induction t ; intros ; depelim t' ; try depelim tt'. simpl in *. reflexivity.

  destruct o.
  unfold binary_plus_be in H.
  simp vfold_right2 in H.
  case_eq (binary_plus_be t t'). intros. specialize (IHt _ _ _ H0).
  unfold binary_plus_be in H0. unfold bit in * ; rewrite H0 in H.
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
  unfold binary_plus_be in H. simp vfold_right2 in H.
  case_eq (binary_plus_be t t'). intros. specialize (IHt _ _ _ H0).
  unfold binary_plus_be in H0. unfold bit in * ; rewrite H0 in H.
  clear H0.
  destruct a ; destruct a0 ; simpl in * ; noconf H ; simpl ; try rewrite IHt ; try omega.
  destruct a1. program_simpl. rewrite H0. omega.
  assumption.
Qed.

Lemma binary_plus_be_correct n : forall (t t' : bits n) tt', binary_plus_be t t' = (tt', false) ->
  nat_of_binary_be tt' = nat_of_binary_be t + nat_of_binary_be t'.
Proof.
  intros. apply (binary_plus_be_correct_full _ _ _ _ _ H).
Qed.

Inductive bits_nat_view {n} : bits n -> Prop :=
| b0 : bits_nat_view (constant_vector n false)
| bS : forall b, bits_nat_view b -> forall b', bits_succ_be b = (b', false) -> bits_nat_view b'.

Print vector_ind.

Lemma Vcons_append_one {A n} (a : A) (v : vector A n) : exists a' v', (a |:| v)%bin = vector_append_one v' a'.
Proof. intros. revert a.
  induction v.
  intros. exists a. exists (@Vnil A). reflexivity.

  intros.
  destruct (IHv a) as [a' [ v' Hv' ] ].
  exists a'. exists (a0 |:| v')%bin. 
  simp vector_append_one. congruence.
Qed.

Lemma vector_rev_ind : Π (A : Type) (P : Π n : nat, vector A n -> Prop),
       P 0 [[]]%bin ->
       (Π (a : A) (n : nat) (v : vector A n), P n v -> P (S n) (vector_append_one v a)%bin) ->
       Π (n : nat) (v : vector A n), P n v.
Proof.
  intros.
  destruct v.
  assumption.
  revert a v. induction n. intros.
  depelim v. apply (H0 a 0 Vnil H).

  intros.
  depelim v.
  destruct (Vcons_append_one a0 v) as [a' [ v' Ha'v' ] ].
  pose (IHn a0 v).
  rewrite Ha'v' in p.
  rewrite Ha'v'.
  replace (a |:| vector_append_one v' a')%bin with (vector_append_one (a |:| v') a')%bin.
  apply H0. apply IHn.
  simp vector_append_one.
Qed.

Lemma bits_succ_vector_append_0 : Π (n : nat) (v : vector bit n),
  bits_succ_be (vector_append_one v 0%bin) =
  (vector_append_one v 1%bin, 0%bin).
Proof. intros.
  Opaque vector_append_one.
  funind (vector_append_one v false) appv.
  destruct a.
  simp bits_succ_be. rewrite IHvector_append_one_ind. reflexivity.
  simp bits_succ_be. rewrite IHvector_append_one_ind. reflexivity.
Qed.
  
(* Lemma bits_succ_ind' n : Π (P : bits n -> Prop), *)
(*        P (constant_vector n false) -> *)
(*        (Π (v : bits n), P v -> forall v', bits_succ_be n v = (v', false) -> P v') -> *)
(*        Π (v : bits n), P v. *)
(* Proof. *)
(*   intros. induction v using vector_rev_ind. apply H. *)
(*   cut (P (vector_append_one v false)). intros. *)
(*   destruct a. apply H0 with (vector_append_one v false). assumption. *)
(*   apply bits_succ_vector_append_0. assumption. *)
(*   eapply H0. pose @vector_append. *)


(*   intros. *)
(*   destruct v. *)
(*   assumption. *)
(*   revert a v. induction n. intros. *)
(*   depelim v. apply (H0 a 0 Vnil H). *)


(* Lemma bits_nat_view_full n (b : bits n) : bits_nat_view b. *)
(* Proof. *)
(*   induction b using vector_rev_ind. *)
(*   constructor. *)

(*   destruct a.  *)
(*   eapply bS with (vector_append_one b 0)%bin. *)
(*   eapply bS. *)
Open Local Scope bin_scope.
Definition fourty_five := (representation 32 45).
Definition ninety := (representation 32 90).

Equations(nocomp) binary_minus_be {n} (x y : bits n) : bits n * overflow :=
binary_minus_be O Vnil Vnil := (Vnil, false) ;
binary_minus_be (S n) (Vcons hdx n tlx) (Vcons hdy n tly) := 
  match hdx, hdy with
    | 1, 1 | 0, 0 => 
      let '(min', carry) := binary_minus_be tlx tly in
        (Vcons 0 min', carry)
    | 0, 1 =>
      (* diff (b(n-1) * 2^n-1 + ... + b0) (2^n + b'(n-1) 2^n-1 + ... + b'0) =
         ((2^n - 1) - (b(n-1) * 2^n-1 + ... + b0)) + 1 + b'(n-1) 2^n-1 + ... + b'0) *)
      let min' := Bneg _ tlx in
      let '(plus, overflow) := bits_succ_be min' in
        if overflow then (* tlx must have been 0 *)
          (1 |:| tly, 1)
        else
          let '(plus', overflow') := binary_plus_be plus tly in
            ((overflow' |:| plus'), 1)
    | 1, 0 => 
     (* (2^n + b(n-1) * 2^n-1 + ... + b0) - (b'(n-1) 2^n-1 + ... + b'0) =
        (2^n - 1) - (b'(n-1) 2^(n-1) + ... + b'0) + 1 + (bn * 2^(n-1) + ... + b0) *)
      let rest := Bneg _ tly in
      let '(plus, overflow) := bits_succ_be rest in
        if overflow then (* tly was all zeros *)
          (1 |:| tlx, 0)
        else
          let '(plus', overflow') := binary_plus_be plus tlx in
            (overflow' |:| plus', 0)
  end.

Notation " 'convertible' x y " := ((@eq_refl _ x) : x = y) (at level 0, x at next level, y at next level).

Global Transparent binary_minus_be binary_plus_be bits_succ_be constant_vector vfold_right2 vector_append_one.

Check (convertible (fst (binary_minus_be ninety fourty_five)) fourty_five).
Check (convertible (nat_of_binary_be (fst (binary_minus_be fourty_five ninety))) 45).

Eval compute in (binary_minus_be (one (n:=4)) zero). 
Eval compute in (nat_of_binary_be (fst (binary_minus_be (one (n:=4)) (representation _ 5)))).
Eval compute in (nat_of_binary_be (fst (binary_minus_be (representation 5 5) (representation _ 5)))).
Eval compute in (binary_minus_be (representation 5 5) (representation _ 5)).

Lemma bits_succ_be_ne n y b' : bits_succ_be (Bneg n y) = (b', 1) -> y = zero.
Proof.
  induction n; intros. depelim y. reflexivity.
  
  Opaque bits_succ_be.
  depelim y.
  case_eq (bits_succ_be (Bneg n y)). intros. destruct o. specialize (IHn _ _ H).
  destruct a; simp bits_succ_be in x; rewrite H in x ; noconf x. 
  subst y. reflexivity.
  
  destruct a; simp bits_succ_be in x; rewrite H in x; noconf x. 
Qed.

Lemma nat_of_binary_zero n : nat_of_binary_be (zero (n:=n)) = 0%nat.
Proof. induction n ; simpl ; auto. Qed.

Lemma nat_of_binary_one n : nat_of_binary_be (one (n:=n)) = 1%nat.
Proof. induction n ; simpl ; auto. Qed.


Lemma nat_of_binary_bound {n} (x : bits n) : nat_of_binary_be x < pow_of_2 n.
Proof.
  induction n ; intros. depelim x. simpl. auto.
  depelim x. destruct a ; simpl ; auto with arith.
Qed.

Lemma nat_of_binary_bound_eq {n} (x : bits n) : nat_of_binary_be x - pow_of_2 n = 0%nat.
Proof. intros. generalize (nat_of_binary_bound x). omega. Qed.

Lemma nat_of_binary_bneg n x : nat_of_binary_be (Bneg n x) = 
  pow_of_2 n - (S (nat_of_binary_be x)).
Proof.
  induction n ; intros.
  
    now depelim x. 
    
    Opaque pow_of_2.
    simpl in *.
    case_eq (pow_of_2 (S n)). 
    generalize (pow_of_2_pos (S n)). 
    intros ; elimtype False ; omega.
    
    intros.
    depelim x.
    simpl. 
    rewrite IHn. case_eq (pow_of_2 n).
    generalize (pow_of_2_pos n). 
    intros ; elimtype False ; omega.
    intros.
    Transparent pow_of_2. simpl in H.
    rewrite H0 in H. simpl in H.
    rewrite plus_comm in H. noconf H.
    
    destruct a ; simpl. 
    omega.
    
    case_eq (nat_of_binary_be x); intros. omega.
    pose (nat_of_binary_bound x). 
    rewrite H0 in l. omega.
Qed.

Lemma minus_plus_lt x y z : x > y -> (x - y + z) = (x + z) - y.
Proof. intros. omega. Qed.
  
Lemma minus_plus_lt2 x y z : x > y -> ((x + z) - y) - x = z - y.
Proof. intros. omega. Qed.

(* Lemma minus_plus_lt3 x y z : x > y -> x + y - z = x + (y - z). *)
(* Proof. intros. omega. Qed. *)

    
Lemma binary_minus_correct {n} (x y t : bits n) : binary_minus_be x y = (t, false) -> 
  nat_of_binary_be x - nat_of_binary_be y = nat_of_binary_be t.
Proof.
  intros.
  Opaque binary_minus_be.
  induction n ; depelim x; depelim y. reflexivity.
  destruct a ; destruct a0; simp binary_minus_be in H.
  case_eq (binary_minus_be x y). intros. rewrite H0 in *.
  noconf H. specialize (IHn _ _ _ H0).
  simpl. rewrite <- IHn. omega.
  
  clear IHn.
  case_eq (bits_succ_be (Bneg n y)); intros ; rewrite H0 in *.
  destruct o.
  noconf H. simpl. apply bits_succ_be_ne in H0. subst y. rewrite nat_of_binary_zero.
  omega.

  case_eq (binary_plus_be b x); intros ; rewrite H1 in *.
  noconf H. apply binary_plus_be_correct_full in H1. 
  apply nat_of_binary_bits_succ_be in H0.
  simpl. rewrite H0 in H1. rewrite nat_of_binary_bneg in *.
  pose (nat_of_binary_bound x). 
  pose (nat_of_binary_bound y).
  destruct o. simpl. destruct H1. rewrite H1.
  replace (S (pow_of_2 n - S (nat_of_binary_be y))) with (pow_of_2 n - nat_of_binary_be y) by omega.
  rewrite minus_plus_lt by omega.
  rewrite minus_plus_lt2 by omega.
  omega.

  rewrite H1.
  replace (S (pow_of_2 n - S (nat_of_binary_be y))) with (pow_of_2 n - nat_of_binary_be y) by omega.
  omega.

  destruct_call @bits_succ_be. destruct o ; simpl in H. discriminate.
  destruct_call @binary_plus_be. discriminate.

  case_eq (binary_minus_be x y) ; intros. rewrite H0 in *.
  noconf H.
  simpl. rewrite (IHn _ _ _ H0). reflexivity.
Qed.

Lemma binary_minus_be_one_overflow n (t : bits (S n)) b : binary_minus_be t one = (b, 1) -> t = zero.
Proof.
  induction n ; simpl ; auto.
  intros. do 2 depelim t. do 2 depelim b. unfold one in H. simpl in H. simp binary_minus_be in H.
  destruct a. fold bit in H. rewrite binary_minus_be_equation_1 in H. noconf H.
  simp bits_succ_be in H.
  
  intros.
  depelim t ; depelim b.
  fold bit in H. unfold one in H. simp binary_minus_be in H.
  destruct a. destruct_call @bits_succ_be. destruct o. discriminate.
  destruct_call @binary_plus_be. discriminate.
  case_eq (binary_minus_be t (vector_append_one (constant_vector n 0) 1)).
  intros.
  rewrite H0 in H.
  noconf H.
  apply IHn in H0. subst. reflexivity.
Qed.

Lemma nat_of_binary_one_is_one n (t : bits (S n)) : nat_of_binary_be t = 1%nat -> t = one.
Proof. induction n ; simpl ; intros ; auto. do 2 depelim t. destruct a ; simpl in * ; auto with *.
  depelim t. destruct a.
  generalize (pow_of_2_pos n) ; intros ; elimtype False ; omega.
  simpl in x. apply IHn in x. rewrite x. reflexivity.
Qed.

Lemma nat_of_binary_full n : nat_of_binary_be (full (n:=n)) = pow_of_2 n - 1.
Proof.  Transparent nat_of_binary_be.
  induction n ; simpl ; auto with *. unfold full in *. rewrite IHn. omega.
Qed.
Ltac absurd_arith := intros ; elimtype False ; omega.

Lemma nat_of_binary_be_inj n (t t' : bits n) : nat_of_binary_be t = nat_of_binary_be t' -> t = t'.
Proof.
  induction n. depelim t ; depelim t' ; auto with *.

  intros.
  revert IHn.
  depelim t. depelim t' ; intros; auto with *.
  simpl in x. destruct a; destruct a0 ; auto;
  try rewrite (IHn t t') by omega ; try reflexivity.
  generalize (nat_of_binary_bound t'). generalize (pow_of_2_pos n). absurd_arith.
  generalize (nat_of_binary_bound t). generalize (pow_of_2_pos n). absurd_arith.
Qed.
  
Open Local Scope bin_scope.
Lemma binary_of_nat_inverse {n} (t : bits n) : binary_of_nat_be n (nat_of_binary_be t) = Some t.
Proof.
  intros n t. remember (nat_of_binary_be t) as tmp. revert n t Heqtmp. induction tmp ; intros. simpl.
  destruct n. now depelim t.

  unfold zero in *. 
  funind (nat_of_binary_be t) foo. subst rest.
  destruct a. generalize (pow_of_2_pos n). intros. elimtype False. omega. 
  depind v. reflexivity. simpl. f_equal. f_equal. 
  specialize (IHnat_of_binary_be_ind foo). congruence.

  Opaque nat_of_binary_be.
  depelim t.
  case_eq (binary_minus_be (a |:| t) one).
  intros.
  destruct o.
  apply binary_minus_be_one_overflow in H. rewrite H. rewrite H in Heqtmp.
  rewrite nat_of_binary_zero in Heqtmp. discriminate.

  apply binary_minus_correct in H. rewrite nat_of_binary_one in H.
  rewrite <- Heqtmp in H.
  simpl in H. rewrite <- minus_n_O in H. subst.
  simplify_IH_hyps.
  simpl.
  case_eq (nat_of_binary_be b) ; intros. rewrite H in *.

  pose (nat_of_binary_one_is_one _ _ (symmetry Heqtmp)). rewrite e. reflexivity.

  rewrite H in IHtmp.
  rewrite IHtmp.
  case_eq (bits_succ_be b).
  intros.
  destruct o.
  destruct (bits_succ_be_overflow _ _ _ H0). 
  subst.
  rewrite H2 in Heqtmp.
  rewrite nat_of_binary_full in Heqtmp.
  replace (S (pow_of_2 (S n) - 1)) with (pow_of_2 (S n)) in Heqtmp. 
  pose (nat_of_binary_bound (a |:| t)). rewrite <- Heqtmp in l.
  elimtype False ; omega.
  
  generalize (pow_of_2_pos (S n)) ; intros ; omega.

  apply nat_of_binary_bits_succ_be in H0.
  rewrite Heqtmp in H0. apply nat_of_binary_be_inj in H0. congruence.
Qed.

(* Inductive Split {X : Type}{m n : nat} : vector X (m + n) -> Type := *)
(*   append : Π (xs : vector X m)(ys : vector X n), Split (vector_append xs ys). *)

(* Implicit Arguments Split [ [X] ]. *)

(* Equations(nocomp) split {X : Type} {m n} (xs : vector X (m + n)) : Split m n xs := *)
(* split X O    n xs := append Vnil xs ; *)
(* split X (S m) n (Vcons x ?(S m + n) xs) := *)
(*   let res := split xs in *)
(*   let 'append xs' ys' in Split _ _ vec := res return Split (S m) n (Vcons x vec) in *)
(*     append (Vcons x xs') ys'. *)

(* Equations(nocomp) split {X : Type} {m} (xs : vector X m) n : vector  *)
(* split X O    n xs := append Vnil xs ; *)
(* split X (S m) n (Vcons x ?(S m + n) xs) := *)
(*   let res := split xs in *)
(*   let 'append xs' ys' in Split _ _ vec := res return Split (S m) n (Vcons x vec) in *)
(*     append (Vcons x xs') ys'. *)

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

Equations(nocomp) binary_shiftl_n {n} (t : bits n) (m : nat) : bits n * overflow :=
binary_shiftl_n n t O := (t, false) ;
binary_shiftl_n n t (S m) <= binary_shiftl t => {
  binary_shiftl_n n t (S m) (pair t' true) := (t', true) ;
  binary_shiftl_n n t (S m) (pair t' false) := binary_shiftl_n t' m }.
    
Equations(nocomp) binary_mult_be {n m} (x : bits m) (y : bits n) : bits n * overflow :=
binary_mult_be n O Vnil y := (zero, false) ;
binary_mult_be n (S m) (Vcons hdx m tlx) y :=
  if hdx then 
    let '(y', overflow) := binary_shiftl_n y m in
      if overflow then (y, true)
      else 
        let '(y'', overflow) := binary_mult_be tlx y in
          if overflow then (y, true)
          else binary_plus_be y' y''
  else binary_mult_be tlx y.

(* Lemma binary_mult_be_0 {n} (y : bits n) z is_zero :  *)
(*   binary_mult_be zero y true = (zero, false). *)
(*   nat_of_binary_be x * nat_of_binary_be y = nat_of_binary_be z. *)
(* Proof. *)
(*   intros n m x y z is_zero. *)
(*   funind (binary_mult_be x y is_zero) multxy. *)
(*   simpdep. simpl. destruct is_zero. simpl. *)
(*   intros.  *)

Global Transparent binary_shiftl binary_shiftl_n binary_mult_be nat_of_binary_be.

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

Transparent nat_of_binary_be.

Ltac case_eq_rew :=
  fun x => generalize (@eq_refl _ x); pattern x at - 1 in |- *; case x ; intros ; 
    on_last_hyp ltac:(fun H => rewrite H in *).


Tactic Notation "funind" constr(c) ident(Hcall) :=
  match c with
    appcontext C [ ?f ] => 
      let x := constr:(fun_ind_prf (f:=f)) in
        (let prf := eval simpl in x in
         let p := context C [ prf ] in
         let prf := fresh in
         let call := fresh in
           assert(prf:=p) ;
           (* Abstract the call *)
           set(call:=c) in *; generalize (refl_equal : call = c); clearbody call ; intro Hcall ;
           (* Now do dependent elimination and simplifications *)
           dependent induction prf ; simplify_IH_hyps ;
           (* Use the simplifiers for the constant to get a nicer goal. *)
           try simpc f ; try on_last_hyp ltac:(fun id => simpc f in id ; noconf id))
        || fail 1 "Internal error in funind"
  end || fail "Maybe you didn't declare the functional induction principle for" c.

Tactic Notation "funind" constr(c) ident(Hcall) "generalizing" ne_hyp_list(l) := 
  match c with
    appcontext C [ ?f ] => 
      let x := constr:(fun_ind_prf (f:=f)) in
        (let prf := eval simpl in x in
         let p := context C [ prf ] in
         let prf := fresh in
         let call := fresh in
           assert(prf:=p) ;
           (* Abstract the call *)
             set(call:=c) in *; generalize (refl_equal : call = c); intro Hcall ; revert Hcall ; clearbody call ; (* ; *)
           (* (* Now do dependent elimination and simplifications *) *)
           revert l ; do_depelim' ltac:(fun hyp => do_ind hyp) prf ; simplify_dep_elim ; 
           intros ; simplify_IH_hyps ;
           (* Use the simplifiers for the constant to get a nicer goal. *)
           try simpc f ; try simpc f in Hcall)
  end.

Opaque binary_shiftl.
Print Ltac funind.
Lemma binary_shiftl_correct {n} (t : bits n) t' o : binary_shiftl t = (t', o) ->
  if o then pow_of_2 n + nat_of_binary_be t' = 2 * nat_of_binary_be t
  else nat_of_binary_be t' = 2 * nat_of_binary_be t.
Proof. intros. 
  info funind (binary_shiftl t) shiftt generalizing t' o H. 
  destruct recres. noconf H. 
  case_eq_rew (binary_shiftl v). noconf shiftt. 
  destruct o. simpl. destruct o1. omega. omega. 
  destruct o1; simpl. omega. omega.
Qed.

Transparent binary_shiftl.

Lemma binary_shiftl_n_correct {n} (t : bits n) m t' : binary_shiftl_n t m = (t', false) ->
  nat_of_binary_be t' = pow_of_2 m * nat_of_binary_be t.
Proof. intros n t m ; revert n t ; induction m ; intros.

    simp binary_shiftl_n in H. noconf H.

    simp binary_shiftl_n in H. 
    case_eq_rew (binary_shiftl t). destruct o. noconf H. 
    specialize (IHm _ _ _ H). rewrite IHm.
    rewrite (binary_shiftl_correct _ _ _ H0).
    rewrite mult_assoc at 1. setoid_rewrite mult_comm at 2. simpl.
    reflexivity.
Qed.

Lemma binary_eq_eq {n} {x y : bits n} : binary_eq x y = true -> x = y.
Proof.
  intros. funind (binary_eq x y) eqxy. destruct recres.
  simp binary_eq in eqxy. rewrite andb_b_true in x. rewrite x in *.
  simpl in *. rewrite eqxy in IHbinary_eq_ind. apply bool_eq_ok in x. subst.
  rewrite IHbinary_eq_ind by auto. reflexivity.

  rewrite andb_b_false in x. discriminate.
Qed.

Transparent binary_eq.
Opaque binary_mult_be.
Lemma binary_mult_correct {n m} (x : bits m) (y : bits n) z : 
  binary_mult_be x y = (z, false) -> nat_of_binary_be x * nat_of_binary_be y = nat_of_binary_be z.
Proof.
  intros n m x. induction x ; intros.
  simp binary_mult_be in H. noconf H.
  rewrite nat_of_binary_zero. reflexivity. 

  simp binary_mult_be in H.
  destruct a. 
  case_eq (binary_shiftl_n y n0) ; intros. rewrite H0 in *.
  case_eq_rew (binary_mult_be x y). 
  destruct o ; try noconf H.
  destruct o0. noconf H.
  specialize (IHx _ _ H1).
  apply binary_shiftl_n_correct in H0.
  apply binary_plus_be_correct in H.
  rewrite H.
  rewrite <- IHx. rewrite H0. ring.

  specialize (IHx _ _ H).
  assumption.
Qed.
Transparent binary_mult_be.

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
  

Program Instance bvec_binary_be n : Binary BigEndian (bits (S n)) := {
  bin_size t := S n ;
  
  bin_of_nat := binary_of_nat_be (S n);
  nat_of_bin := nat_of_binary_be;

  bin_succ := bits_succ_be ;

  bin_plus := binary_plus_be ;
  bin_minus := binary_minus_be ;
  bin_mult := binary_mult_be
}.

  Next Obligation. now apply nat_of_binary_inverse. Qed.
  Next Obligation. apply binary_of_nat_inverse. Qed.
  Next Obligation. now erewrite nat_of_binary_bits_succ_be. Qed.
  Next Obligation. now apply binary_plus_be_correct. Qed.
  Next Obligation. symmetry. now apply binary_minus_correct. Qed.
  Next Obligation. symmetry. now apply binary_mult_correct. Qed.

Global Transparent vfold_right2 binary_minus_be bits_succ_be nat_of_binary_be.

Eval compute in (nat_of_bin (fst (bin_plus (representation 32 16) (representation 32 4)))).
Eval compute in (nat_of_bin (fst (bin_plus (representation 32 90) (representation 32 45)))).
Eval compute in (nat_of_bin (fst (bin_plus fourty_five ninety))).

Eval compute in (nat_of_bin (fst (bin_minus fourty_five ninety))).
Eval compute in (nat_of_bin (fst (bin_minus ninety fourty_five))).


(** Orders *)

Equations(nocomp) binary_be_le {n} (x y : bits n) : bool :=
binary_be_le O Vnil Vnil := true ;
binary_be_le (S n) (Vcons a n x) (Vcons a' n y) :=
  if xorb a a' then a'
  else binary_be_le x y.

Class BoolReflexive {A} (R : A -> A -> bool) := 
  reflexivityb : forall x, R x x = true.

Class BoolSymmetric {A} (R : A -> A -> bool) := 
  symmetryb : forall x y, R x y = true -> R y x = true.

Class BoolTransitive {A} (R : A -> A -> bool) := 
  transitivityb : forall x y z, R x y = true -> R y z = true -> R x z = true.

Instance: BoolReflexive (@binary_be_le n).
Proof. reduce_goal. induction x ; simp binary_be_le.
  rewrite IHx. destruct a ; simpl ; auto.
Qed.

Instance: BoolTransitive (@binary_be_le n).
Proof. reduce_goal. induction x ; simp binary_be_le; depelim y ; depelim z.
  simp binary_be_le.

  simp binary_be_le in H.
  simp binary_be_le in H0. 
  destruct a ; destruct a1 ; destruct a0 ; simpl in * ; try discriminate ; simp binary_be_le.
Qed.

Definition binary_le_lt {n} (x y : bits n) := 
  let '(x', overflow) := bits_succ_be x in
    if overflow then false
    else binary_be_le x' y.