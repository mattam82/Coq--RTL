Require Import CSDL.Binary CSDL.BinaryBe.
Require Import ZArith.

Open Local Scope vect_scope.
Open Local Scope Z_scope.

Definition sign_of_signed {n} (b : bits (S n)) : bit := Vhead b.
Definition Z_of_sign (b : bool) := if b then -1 else 1.
Definition Z_of_bool (b : bool) := if b then 1 else 0.
Definition min_signed {n} : bits (S n) := (true |:| zero).
Definition max_signed {n} : bits (S n) := (false |:| full).

Fixpoint Z_of_signed_be {n} : bits n -> Z :=
  match n return bits n -> Z with
    | O => const 0%Z
    | S n => λ x,
      match x with
        | Vcons neg n v =>
          if neg then (- Zsucc (Z_of_nat (nat_of_binary_be (binary_inverse v))))%Z
          else Z_of_nat (nat_of_binary_be v)
      end
  end.

Notation " [Z:  x ] " := (Z_of_signed_be x).

Bind Scope vect_scope with bits.

Lemma Z_of_nat_binary_be {n} (t : bits n) : Z_of_nat [: t] = [Z: (false |:| t)].
Proof. intros. induction t. simpl. reflexivity. simpl. reflexivity. Qed.

Lemma Z_of_signed_be_zero n : [Z: @zero n] = 0.
Proof. induction n. simpl. reflexivity.
  simpl. rewrite nat_of_binary_zero. simpl. reflexivity.
Qed.

Lemma Z_of_signed_be_one n : [Z: @one (S n)] = 1.
Proof. induction n. simpl. reflexivity.
  simpl. rewrite nat_of_binary_one. simpl. reflexivity.
Qed.

Lemma Z_of_nat_of_binary_be_bound {n} (t : bits n) : Z_of_nat [: t ] < pow_of_2_Z n.
Proof. intros.
  rewrite <- pow_of_2_nat_Z. apply inj_lt. apply nat_of_binary_bound.
Qed.

Lemma Z_of_signed_be_bound_pos {n} (t : bits n) : [Z: false |:| t] < pow_of_2_Z n.
Proof. intros. simpl. rewrite <- pow_of_2_nat_Z. apply inj_lt. apply nat_of_binary_bound. Qed.

Lemma Z_of_signed_be_bound_neg {n} (t : bits n) : [Z: true |:| t] >= - pow_of_2_Z n.
Proof. intros. simpl. rewrite <- pow_of_2_nat_Z. 
  rewrite Zopp_succ. unfold Zpred ; ring_simplify.
  rewrite nat_of_binary_inverse. rewrite inj_minus, inj_S, pow_of_2_nat_Z. 
  ring_simplify. rewrite Zmax_right. ring_simplify. omega. rewrite Z_of_nat_binary_be.
  generalize (Z_of_signed_be_bound_pos t). omega.
Qed.


Lemma Z_of_nat_of_binary_full n : Z_of_nat [: (@full n) ] = pow_of_2_Z n - 1.
Proof. intros. rewrite nat_of_binary_full. rewrite inj_minus, pow_of_2_nat_Z. 
  rewrite Zmax_right. simpl ; ring. generalize (pow_of_2_Z_pos n). intros ; simpl ; omega. 
Qed.

Lemma Z_of_nat_pos n : Z_of_nat n >= 0.
Proof. auto with zarith. Qed.

Lemma Zge_opp_Zle x y : x <= y -> - x >= - y. 
Proof. intros. omega. Qed.

Eval compute in (Z_of_signed_be (@full 3)).

(** * Inverse. *)

Lemma Z_of_nat_binary_be_inverse n (b : bits n) :
  Z_of_nat [: binary_inverse b] = pow_of_2_Z n - Zsucc (Z_of_nat [: b ]).
Proof.
  intros. rewrite ! nat_of_binary_inverse. 
  generalize (nat_of_binary_bound b). intros. rewrite inj_minus, inj_S.
  rewrite Zmax_right. rewrite pow_of_2_nat_Z. reflexivity.
  omega.
Qed.

Lemma Z_of_signed_be_full {n} : Z_of_signed_be (@full (S n)) = - 1.
Proof.
  intros. unfold full. simpl.
  rewrite Zopp_succ, Z_of_nat_binary_be_inverse.
  unfold Zpred ; ring_simplify.
  rewrite nat_of_binary_full. rewrite inj_minus.
  rewrite pow_of_2_nat_Z, Zmax_right.
  simpl. omega.
  simpl. generalize (pow_of_2_Z_pos n). omega.
Qed.

(** * Two's complement of a signed binary number. *)

Definition two_s_complement {n} (b : bits (S n)) :=
  let '(compl, _) := bits_succ_be (binary_inverse b) in
    (compl, Vhead b && Vhead compl).

(** A reformulation of [bits_succ_be_correct] for integers. *)

Lemma bits_succ_be_correct_Z (t : nat) (b c : bits (S t)) o : bits_succ_be b = (c, o) -> 
  if negb (Vhead b) && (Vhead c) then 
    b = (false |:| full) /\ c = binary_inverse b    
  else [Z: c ] = Zsucc [Z: b].
Proof.
  intros. destruct o. 
  apply bits_succ_be_overflow in H. destruct H ; subst.
  simpl. auto.
  rewrite binary_inverse_constant. rewrite ! nat_of_binary_zero. reflexivity.

  apply bits_succ_be_correct in H.
  depelim c ; depelim b. simpl.
  destruct a; simpl; simpl in x.
  simpl in *. destruct a0 ; simpl.
  assert ([: c] = S [: b]) by omega.
  rewrite ! Z_of_nat_binary_be_inverse. 
  rewrite H. rewrite inj_S. simpl.
  ring.
  
  generalize (nat_of_binary_bound b). intros.
  assert ([: c] = 0)%nat by omega.
  rewrite H0 in x.
  rewrite <- plus_n_O in x.
  assert([: b ] = pow_of_2 t - 1)%nat by omega.
  rewrite <- (nat_of_binary_full t) in H1.
  apply nat_of_binary_be_inj in H1. subst.
  rewrite <- (nat_of_binary_zero t) in H0.
  apply nat_of_binary_be_inj in H0. subst.
  unfold full. rewrite binary_inverse_constant. intuition auto.

  destruct a0 ; simpl.
  generalize (nat_of_binary_bound c) ; absurd_arith.
  
  rewrite x. rewrite inj_S. ring.
Qed.

(** Correctness proof for two's complement. Only overflowing case is if we're taking
   the opposite of [-2^n]. *)

Lemma two_s_complement_correct {n} (x : bits (S n)) compl o : two_s_complement x = (compl, o) ->
  if o then x = min_signed /\ compl = x
  else [Z: compl ] = - [Z: x ].
Proof. unfold two_s_complement.
  intros.
  Opaque bits_succ_be.
  destruct_call_eq @bits_succ_be.
  
  apply bits_succ_be_correct_Z in H0.
  noconf H.
  rewrite binary_inverse_involutive in H0.
  depelim x ; depelim compl ; simpl in *.
  rewrite binary_inverse_involutive in H0.  
  destruct a ; destruct a0 ; simpl in *; try rewrite H0 ; try ring.
  destruct H0. noconf H ; noconf H0.
  apply binary_inverse_is_constant in x. subst. now auto.
Qed.

Require Import ROmega.

Opaque vfold_right2.

(** Arithmetic operations in terms of unsigned arithmetic operations. 
   Overflow detection actually needs the last two carries for addition, 
   so we specialize it. *) 

Equations(nocomp) signed_plus_be {n} (t t' : bits (S n)) : bits (S n) * overflow :=
signed_plus_be n (Vcons s n t) (Vcons s' _ t') :=
  let '(add, carry) := binary_plus_be t t' in
  let '(last, carry') := add_bits s s' carry in
    (Vcons last add, xorb carry carry').

(** Reformulation of binary addition correctness in terms of integers. *)

Lemma binary_plus_be_correct_Z n : forall (t t' : bits n) tt' o, binary_plus_be t t' = (tt', o) ->
  let add' := Z_of_nat [: t ] + Z_of_nat [: t'] in
    if o then add' >= pow_of_2_Z n /\
      Z_of_nat [: tt' ] = add' - pow_of_2_Z n
    else Z_of_nat [: tt' ] = add'.
Proof.
  intros. 
  apply binary_plus_be_correct_full in H. subst add'.
  destruct o ; program_simpl.
  rewrite H0.
  assert(Z_of_nat [: t] + Z_of_nat [: t'] >= pow_of_2_Z n).
  rewrite <- inj_plus. rewrite <- pow_of_2_nat_Z. apply inj_ge ; auto.
  split ; auto.
  rewrite inj_minus, Zmax_right ; try omega.
  rewrite inj_plus. rewrite pow_of_2_nat_Z. reflexivity.
  rewrite inj_plus. omega.

  rewrite <- inj_plus. auto.
Qed.

(** Signed multiplication correctness. *)
  
Lemma signed_plus_be_correct n : forall (t t' : bits (S n)) tt', signed_plus_be t t' = (tt', false) ->
  Z_of_signed_be tt' = Z_of_signed_be t + Z_of_signed_be t'.
Proof.
  intros.
  funind (signed_plus_be t t') stt'. depelim tt'.
  destruct_call_eq @binary_plus_be.
  rewrite add_bits_correct in x.
  destruct_call_eq @add_bits_spec.
  noconf x.
  apply binary_plus_be_correct_Z in H.
  destruct o.
  destruct H. simpl in H.
  destruct a ; destruct a0 ; noconf x ; simpl in * ;
  rewrite ! Z_of_nat_binary_be_inverse ;
  rewrite H0; try ring. 

  destruct a ; destruct a0 ; noconf x ; simpl in * ;
  rewrite ! Z_of_nat_binary_be_inverse ;
    try rewrite H; try ring.
Qed. 

(** If there is an overflow, the sign depends on the sign of the result. *)
  
Lemma signed_plus_be_overflow n : forall (t t' : bits (S n)) tt', signed_plus_be t t' = (tt', true) ->
  Z_of_signed_be tt' + Z_of_sign (negb (Vhead tt')) * pow_of_2_Z (S n) = Z_of_signed_be t + Z_of_signed_be t'.
Proof.
  intros. 
  funind (signed_plus_be t t') plustt'.
  depelim tt'.
  destruct_call_eq @binary_plus_be.
  rewrite add_bits_correct in x.
  apply binary_plus_be_correct_Z in H.
  destruct_call_eq @add_bits_spec.
  noconf x.
  destruct o. destruct H. Opaque Z_of_sign.
  destruct a ; destruct a0 ; noconf x ; simpl in * ;
  rewrite ! Z_of_nat_binary_be_inverse ;
  rewrite H0. 
  Transparent Z_of_sign.
  ring_simplify. rewrite Zdouble_mult. simpl Z_of_sign. ring.

  Opaque Z_of_sign.
  destruct a ; destruct a0 ; noconf x ; simpl in * ;
  rewrite ! Z_of_nat_binary_be_inverse ;
  rewrite H. 
  ring_simplify. Transparent Z_of_sign. rewrite Zdouble_mult. simpl Z_of_sign. ring.
Qed.

(** Signed substraction [signed_plus_be] is just addition of the opposite. *)

Definition signed_minus_be {n} (x y : bits (S n)) : bits (S n) * borrow :=
  let '(compl, o) := two_s_complement y in
    if o then (y, o)
    else signed_plus_be x compl.
  
Transparent Zmult Zdouble.
Lemma signed_minus_be_correct {n} (x y t : bits (S n)) b : signed_minus_be x y = (t, b) -> 
  if b then 
    (y = min_signed /\ t = y) \/
    (Z_of_signed_be t + Z_of_sign (negb (Vhead y)) * pow_of_2_Z (S n) = Z_of_signed_be x - Z_of_signed_be y)
  else Z_of_signed_be t = (Z_of_signed_be x - Z_of_signed_be y).
Proof.
  intros. unfold signed_minus_be in H.
  destruct_call_eq @two_s_complement.
  apply two_s_complement_correct in H0.
  depelim b0. depelim t.
  destruct b. destruct b1.
  noconf H. 

  destruct H0. unfold min_signed. noconf H. 
  
  apply signed_plus_be_overflow in H.
  depelim x. depelim y.
  Opaque Zmult.

  generalize (pow_of_2_Z_pos n).
  generalize (Z_of_nat_pos [:t]).
  generalize (Z_of_nat_pos [:y]).
  generalize (Z_of_nat_pos [:b0]).
  generalize (Z_of_nat_pos [:x0]).
  generalize (Z_of_nat_of_binary_be_bound x0).
  generalize (Z_of_nat_of_binary_be_bound t).
  generalize (Z_of_nat_of_binary_be_bound b0).
  generalize (Z_of_nat_of_binary_be_bound y). intros.
  rewrite ! Z_of_nat_binary_be_inverse in x1.
  ring_simplify in x1.
  rewrite ! Z_of_nat_binary_be_inverse in x.
  ring_simplify in x.
  rewrite Zdouble_mult in x1. ring_simplify in x1.
  destruct a ; destruct a0; destruct a1; destruct a2;
    simpl in *; ring_simplify in x1; ring_simplify in x;
   try absurd_arith.

  assert(Z_of_nat [:t] = Z_of_nat [:x0] + Z_of_nat [:b0]) by omega.
  unfold min_signed. rewrite H8. rewrite Z_of_nat_binary_be_inverse.
  right.
  ring_simplify.
  assert (Z_of_nat [: b0] = - Z_of_nat [:y] + pow_of_2_Z n) by omega.
  rewrite H9. rewrite Zdouble_mult. ring.

  right. rewrite ! Z_of_nat_binary_be_inverse. ring_simplify.
  rewrite Zdouble_mult. ring_simplify. rewrite x in x1.
  assert(Z_of_nat [:t] = Z_of_nat [:x0] - Z_of_nat [:y]) by omega.
  rewrite H8. ring.

  destruct b1. noconf H.
  apply signed_plus_be_correct in H. rewrite H. rewrite H0. omega.
Qed.


Lemma nat_of_binary_be_vector_append_one {n} (b : bits n) c :
  [: vector_append_one b c ] = (2 * [: b ] + nat_of_bool c)%nat.
Proof.
  intros.
  Opaque vector_append_one.
  funind (vector_append_one b c) bc.
  destruct a. rewrite IHvector_append_one_ind. ring.
  rewrite IHvector_append_one_ind. reflexivity.
Qed.

Lemma nat_of_binary_of_pos_be n p `{Have (Psize p <= n)%nat} : [: binary_of_pos_be n p] = nat_of_P p.
Proof. intros n p. revert n.
  induction p ; simpl ; intros ; auto.
  destruct n; simpl. bang.
  rewrite nat_of_binary_be_vector_append_one.
  rewrite IHp. simpl nat_of_bool. rewrite nat_of_P_xI. omega.

  destruct n; simpl. bang.
  rewrite nat_of_binary_be_vector_append_one.
  rewrite IHp. simpl nat_of_bool. rewrite nat_of_P_xO. omega.

  destruct n; simpl. bang.
  rewrite nat_of_binary_be_vector_append_one.
  rewrite nat_of_binary_zero. simpl. unfold nat_of_P. simpl. reflexivity.
Qed.

Tactic Notation "apply" "*" constr(c) := apply c || symmetry ; apply c.


(** Representing integers by signed binary numbers. *)

Definition signed_of_Z_be {n} (z : Z) : option (bits (S n)) :=
  match z with
    | Z0 => Some zero
    | Zpos p => 
      match dec (leb (Psize p) n) with
        | left H => Some (Vcons false (binary_of_pos_be n p (Hs:=leb_complete _ _ H)))
        | right _ => None
      end
        (* (binary_of_nat_be n (nat_of_P p)) *)
    | Zneg 1 => Some full
    | Zneg p => let p' := Ppred p in
      match dec (leb (Psize p') n) with
        | left H => Some (Vcons true (binary_inverse (binary_of_pos_be n p' (Hs:=leb_complete _ _ H))))
        | _ => None
      end
  end.

Eval compute in (@signed_of_Z_be 7 (-5)).
Eval compute in (@signed_of_Z_be 7 5).
Eval compute in (@signed_of_Z_be 7 (-1)).
Eval compute in (@signed_of_Z_be 7 (- Z_of_nat (pow_of_2 7))).
Eval compute in (@signed_of_Z_be 7 (- Z_of_nat (pow_of_2 7 + 1))).
Eval compute in (@signed_of_Z_be 7 (pow_of_2_Z 7)).
Eval compute in (@signed_of_Z_be 7 (pow_of_2_Z 7 - 1)).
Eval compute in (@signed_of_Z_be 7 0).
Eval compute in (@signed_of_Z_be 7 1).

Eval compute in (option_map Z_of_signed_be (@signed_of_Z_be 7 (-5))).
Eval compute in (option_map Z_of_signed_be (@signed_of_Z_be 7 (-128))).
Eval compute in (option_map Z_of_signed_be (@signed_of_Z_be 7 0)).
Eval compute in (option_map Z_of_signed_be (@signed_of_Z_be 7 127)).

Lemma Z_of_signed_of_Z_inverse n z b :
  @signed_of_Z_be n z = Some b -> [Z: b] = z.
Proof.
  intros. induction z; try noconf H. apply Z_of_signed_be_zero.
  simpl in H.
  case_eq_rew (dec (leb (Psize p) n)). noconf H.
  simpl. rewrite nat_of_binary_of_pos_be. 
  apply* Zpos_eq_Z_of_nat_o_nat_of_P.
  discriminate.

  simpl in H.
  case_eq_rew (dec (leb (Psize (Ppred p)) n)). 
  destruct p; noconf H.
  simpl. rewrite binary_inverse_involutive.
  unfold Zsucc. rewrite nat_of_binary_of_pos_be.
  rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P. simpl. reflexivity.

  simpl.
  rewrite binary_inverse_involutive.
  unfold Zsucc. rewrite nat_of_binary_of_pos_be.
  rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P. simpl.
  rewrite <- Pplus_one_succ_r.
  rewrite Psucc_o_double_minus_one_eq_xO. reflexivity.

  rewrite Z_of_signed_be_full. reflexivity.

  destruct p ; noconf H.
  rewrite Z_of_signed_be_full. reflexivity.
Qed.

Lemma signed_of_Z_be_neg {n} (b : bits n) : [Z: true |:| b] = Zneg (P_of_succ_nat [: binary_inverse b]).
Proof.
  intros. simpl.
  case_eq_rew ([: binary_inverse b]).
  simpl. reflexivity.

  simpl.
  rewrite <- Pplus_one_succ_r. reflexivity.
Qed.

Derive NoConfusion for positive.

(** * Sign extension *)

Equations(nocomp) sx_be {n} (b : bits (S n)) (m : nat) : bits (S m + n) :=
sx_be n (Vcons x n b) m := if x then vector_append full b 
  else Vcons false (vector_append zero b).

Lemma sx_correct {n} (b : bits (S n)) m : [Z: sx_be b m] = [Z: b].
Proof.
  intros. Opaque Z_of_signed_be. funind (sx_be b m) bm. 
  destruct a.
  unfold full. simpl. simp vector_append.
  Transparent Z_of_signed_be. simpl. 
  rewrite binary_inverse_vector_append.
  rewrite binary_inverse_constant.
  rewrite nat_of_binary_be_vector_append.
  rewrite nat_of_binary_zero. rewrite mult_comm ; reflexivity.

  simpl.
  rewrite nat_of_binary_be_vector_append.
  rewrite nat_of_binary_zero. rewrite mult_comm ; reflexivity.
Qed.

Instance psize_psucc `(Have (Psize (Psucc p) <= n)%nat) : Have (Psize p <= n)%nat. 
Proof. unfold Have ; induction p ; simpl ; intros. destruct n ; [inversion H|].
  apply le_S_n in H. pose (IHp _ H). omega. auto. omega.
Qed.

Instance psize_S `(Have (Psize p <= n)%nat) : Have (Psize (p~0) <= S n)%nat. 
Proof. unfold Have. intros. simpl. omega. Qed.


Lemma binary_of_pos_be_Psucc (p : positive) n (Hs : Have (Psize (Psucc p) <= n)%nat) :
  [: binary_of_pos_be n (Psucc p) ] = S [: binary_of_pos_be n p ].
Proof.
  induction p; intros. simpl. destruct n ; simpl. bang.
  rewrite ! nat_of_binary_be_vector_append_one. simpl. ring_simplify.
  rewrite IHp. ring_simplify. pi.

  simpl. destruct n ; [inversion Hs|]. simpl.
  rewrite ! nat_of_binary_be_vector_append_one. simpl. ring_simplify. pi.

  simpl. unfold Have in Hs. depelim Hs. simpl. 
  rewrite ! nat_of_binary_be_vector_append_one. simpl. ring_simplify. 
  rewrite ! nat_of_binary_be_vector_append_one. simpl. reflexivity.

  simpl.
  destruct m. inversion Hs. simpl.
  rewrite ! nat_of_binary_be_vector_append_one. simpl. 
  rewrite ! nat_of_binary_be_vector_append_one. simpl. 
  rewrite ! nat_of_binary_zero. simpl. reflexivity.
Qed.

Lemma binary_of_pos_be_binary_of_nat n (p : positive) (Hs : Have (Psize p <= n)%nat) : exists b,
  binary_of_nat_be n (nat_of_P p) = Some b /\ binary_of_pos_be n p = b.
Proof.
  intros n p. pattern p. apply Prect ; intros.
  simpl. destruct n. inversion Hs. simpl. exists (vector_append_one (@zero n) 1%bin). split ; reflexivity.
  
  rewrite nat_of_P_succ_morphism.
  simpl. destruct_call_eq nat_of_P. 
  generalize (lt_O_nat_of_P p0). absurd_arith.
  destruct (H (psize_psucc Hs)). 
  destruct H1. subst. exists (binary_of_pos_be n (Psucc p0)). rewrite H1. 
  destruct_call_eq @bits_succ_be.
  
  destruct o. 
  apply bits_succ_be_overflow in H2.
  destruct H2. subst. 
  remember (binary_of_pos_be n (Psucc p0)).
  apply (f_equal nat_of_binary_be) in Heqb. rewrite binary_of_pos_be_Psucc in Heqb.
  rewrite H3 in Heqb. rewrite nat_of_binary_full in Heqb. generalize (nat_of_binary_bound b).
  absurd_arith.

  apply bits_succ_be_correct in H2.
  split. f_equal. 
  apply nat_of_binary_be_inj. rewrite H2. 
  rewrite binary_of_pos_be_Psucc. reflexivity.
  reflexivity.
Qed.

Lemma pow_of_2_Z_positive n : pow_of_2_Z n = Zpos (pow_of_2_positive n).
Proof. induction n ; simpl ; auto. rewrite IHn. 
  rewrite Zdouble_mult ; reflexivity.
Qed.

Lemma pow_of_2_Z_S n : pow_of_2_Z (S n) = Zpos (pow_of_2_positive n)~0.
Proof. intros. rewrite pow_of_2_Z_positive. simpl. reflexivity. Qed.
  
Lemma pow_of_2_positive_Psize n : Psize (pow_of_2_positive n) = S n.
Proof. intros. induction n ; simpl ; auto. Qed.
  
Lemma Psize_Ppred_pow_of_2_positive n : Psize (Ppred (pow_of_2_positive (S n))) = S n.
Proof. intros. induction n ; simpl ; auto. Qed.
  
Derive NoConfusion for Datatypes.comparison Z.

Lemma pow_of_2_size n p : pow_of_2_Z n > Zpos p -> (n >= Psize p)%nat.
Proof. induction n ; intros. simpl in H. 
  revert H. pattern p ; apply Prect. intros. inversion H.
  intros.
  inversion H0. destruct p0 ; compute in H2; discriminate.
  
  destruct p.
  
  simpl.
  simpl in H. rewrite Zdouble_mult in H. Transparent Zmult. rewrite pow_of_2_Z_positive in H.
  simpl in H. 
  exploit (IHn p). rewrite Zpos_xI, Zpos_xO in H.
  rewrite pow_of_2_Z_positive. omega. intros.
  omega.
  
  simpl.
  simpl in H. rewrite Zdouble_mult in H. Transparent Zmult. rewrite pow_of_2_Z_positive in H.
  simpl in H. 
  exploit (IHn p). rewrite Zpos_xO in H. rewrite (Zpos_xO p) in H. 
  rewrite pow_of_2_Z_positive. omega. intros. omega.
  
  simpl. omega.
Qed.

Lemma Zpos_p_nat_of_P p : Zpos p = Z_of_nat (nat_of_P p).
Proof. intro p ; pattern p ; apply Prect. 
  simpl. reflexivity.
  intros.
  rewrite nat_of_P_succ_morphism, inj_S. rewrite <- H. 
  destruct p0; simpl ; reflexivity.
Qed.

Lemma Psize_succ p : (Psize p <= Psize (Psucc p))%nat.
Proof. induction p ; simpl ; auto with arith. Qed.
  
Lemma Psize_pred p : (Psize (Ppred p) <= Psize p)%nat.
Proof. apply Prect. simpl. reflexivity.
  intros. rewrite Ppred_succ. apply Psize_succ. Qed.
  
Lemma signed_of_Z_be_Z_of_signed_inverse n (b : bits (S n)) :
  signed_of_Z_be [Z: b ] = Some b.
Proof. intros. depelim b.
  destruct a.

  simpl. rewrite Z_of_nat_binary_be_inverse.
  unfold Zopp, Zsucc. 
  replace (pow_of_2_Z n - (Z_of_nat [: b] + 1) + 1) with (pow_of_2_Z n - Z_of_nat [:b]) by omega.
  generalize (Z_of_nat_of_binary_be_bound b) ; intros.
  case_eq_rew (pow_of_2_Z n - Z_of_nat [: b]). 
  absurd_arith.

  simpl. destruct p. destruct_call dec. simpl. repeat f_equal.
  apply nat_of_binary_be_inj.
  rewrite nat_of_binary_inverse.
  simpl in e. destruct n. discriminate.
  pose (leb_complete _ _ e).
  pose (binary_of_pos_be_binary_of_nat (S n) (p~0) (psize_S l)).
  destruct e0. destruct H1. case_eq_rew (binary_of_nat_be (S n) (nat_of_P p~0)).
  rewrite H1 in H3. 
  replace ((@binary_of_pos_be (S n) (xO p) (leb_complete (S (Psize p)) (S n) e))) with
    (@binary_of_pos_be (S n) (xO p) (@psize_S p n l)) by pi.
  rewrite H2. clear H2. noconf H1.
  apply inj_eq_rev. assert(Z_of_nat [:b] = - Zpos p~1 + pow_of_2_Z (S n)). rewrite <- H0. ring. 
  rewrite H1. rewrite inj_minus, pow_of_2_nat_Z. 
  rewrite Zmax_right. ring_simplify. 
  f_equal. simpl. 
  rewrite (nat_of_binary_binary_of_nat_inverse _ _ _ H3).
  rewrite P_of_succ_nat_o_nat_of_P_eq_succ. simpl. reflexivity.

  generalize (Z_of_nat_of_binary_be_bound x).
  rewrite inj_S. intros. omega.
  discriminate.

  apply leb_complete_conv in e. simpl in e.
  assert (pow_of_2_Z n >= Zpos p~1) by omega.
  assert (pow_of_2_Z n > Zpos p~0). apply Zlt_succ_gt.
  simpl. omega.
  pose (pow_of_2_size _ _ H2). simpl in g. absurd_arith.

  destruct_call dec. repeat f_equal.
  rewrite Zpos_xO in H0. 
  destruct n. simpl pow_of_2_Z in H0.
  assert(1 - Z_of_nat [:b] <= 0) by omega. 
  rewrite H0 in H1. simpl in H1. generalize (Zgt_pos_0 (p~0)). absurd_arith.

  apply nat_of_binary_be_inj. rewrite nat_of_binary_inverse.
  rewrite nat_of_binary_of_pos_be.
  rewrite <- nat_of_P_succ_morphism.
  destruct (Psucc_pred (p~0)). discriminate. rewrite H1 in *. 
  rewrite (Zpos_p_nat_of_P p) in *.
  rewrite nat_of_P_xO. apply inj_eq_rev. 
  assert(Z_of_nat [:b] = - 2 * Z_of_nat (nat_of_P p) + pow_of_2_Z (S n)). omega.
  rewrite H2.
  rewrite inj_minus.
  rewrite pow_of_2_nat_Z.
  rewrite inj_mult. simpl Z_of_nat.
  rewrite Zmax_right. ring.
  omega.
  
  apply leb_complete_conv in e.
  
  case_eq_rew [: b]. 
  simpl Z_of_nat in H0. ring_simplify in H0. Opaque pow_of_2_positive.
  rewrite pow_of_2_Z_positive in *.
  assert(pow_of_2_positive n = p~0%positive). noconf H0. 
  rewrite <- H2 in e. 
  destruct n ; simpl in *. Transparent pow_of_2_positive. simpl in H2. discriminate.

  rewrite (Psize_Ppred_pow_of_2_positive n) in e. 
  absurd_arith.

  rewrite inj_S in H0.
  assert(pow_of_2_Z n > Zpos p~0) by omega.
  pose (pow_of_2_size _ _ H2). 
  rewrite (Psize_pred (p~0)%positive) in e. absurd_arith.

  assert(Z_of_nat [:b] = pow_of_2_Z n - 1) by omega.
  rewrite <- Z_of_nat_of_binary_full in H1. apply inj_eq_rev in H1.
  apply nat_of_binary_be_inj in H1. subst. reflexivity.

  assert(Z_of_nat [:b] - pow_of_2_Z n < 0) by omega. 
  generalize (pow_of_2_Z_pos n). intros.
  generalize (Z_of_nat_pos [:b]). intros.
  assert(pow_of_2_Z n - Z_of_nat [:b] < 0). rewrite H0.
  apply Zlt_neg_0.
  absurd_arith.

  simpl.
  case_eq_rew [: b]. simpl. 
  rewrite <- (nat_of_binary_zero n) in H.
  apply nat_of_binary_be_inj in H. subst.
  simpl. reflexivity.
  
  simpl. destruct_call_eq dec. clear H0.
  repeat f_equal.
  destruct (binary_of_pos_be_binary_of_nat n _ (leb_complete _ _ e)).
  destruct H0.
  rewrite H1. rewrite nat_of_P_o_P_of_succ_nat_eq_succ in H0. rewrite <- H in H0.
  pose (nat_of_binary_binary_of_nat_inverse _ _ _ H0). 
  apply nat_of_binary_be_inj in e0. assumption.

  clear H0.
  apply leb_complete_conv in e.
  generalize (nat_of_binary_bound b). intros.
  rewrite H in H0.
  assert(pow_of_2_Z n > Zpos (P_of_succ_nat n0)).
  rewrite <- pow_of_2_nat_Z.
  change (Zpos (P_of_succ_nat n0)) with (Z_of_nat (S n0)).
  apply inj_gt. omega.
  pose (pow_of_2_size _ _ H1). absurd_arith.
Qed.
  