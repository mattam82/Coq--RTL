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
      match leb (Psize p') n as lepn return leb (Psize p') n = lepn -> option (bits (S n)) with
        | true => λ le, Some (Vcons true (binary_inverse (binary_of_pos_be n p' (Hs:=leb_complete _ _ le))))
        | false => λ le, None
      end eq_refl
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

Lemma signed_of_Z_be_Z_of_signed_inverse n z b :
  @signed_of_Z_be n z = Some b -> [Z: b] = z.
Proof.
  intros. induction z; try noconf H. apply Z_of_signed_be_zero.
  simpl in H.
  case_eq_rew (dec (leb (Psize p) n)). noconf H.
  simpl. rewrite nat_of_binary_of_pos_be. 
Admitted.
(*   revert H. *)
(*   set(foo:=leb_complete (Psize p) n). *)
(*   Set Printing All. intros. *)
(*   reverse. intros n p b. destruct (Psize p). *)

  
  

(* case_eq_rew (Psize p). *)
(*   destruct (leb (Psize p) n). *)

(*   [apply leb_complete in H0 | apply leb_complete_conv in H0]. *)
  
(*   try noconf H.  *)
