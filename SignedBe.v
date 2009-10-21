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

Hint Rewrite Z_of_signed_be_zero Z_of_signed_be_one : binary.

Lemma Z_of_nat_of_binary_be_bound {n} (t : bits n) : Z_of_nat [: t ] < pow_of_2_Z n.
Proof. intros.
  rewrite <- pow_of_2_nat_Z. apply inj_lt. apply nat_of_binary_bound.
Qed.

Lemma Z_of_nat_of_binary_be_bound' {n} (t : bits n) : Z_of_nat [: t ] < Zpos (pow_of_2_positive n).
Proof. intros. apply Z_of_nat_of_binary_be_bound. Qed.

Lemma Z_of_signed_be_upper_bound_pos {n} (t : bits n) : [Z: false |:| t] < pow_of_2_Z n.
Proof. intros. simpl. rewrite <- pow_of_2_nat_Z. apply inj_lt. apply nat_of_binary_bound. Qed.

Lemma Z_of_signed_be_lower_bound_pos {n} (t : bits n) : [Z: false |:| t] >= 0.
Proof. intros. simpl. auto with zarith. Qed.

Lemma Z_of_signed_be_upper_bound_neg {n} (t : bits n) : [Z: true |:| t] < 0.
Proof. intros. simpl. auto with zarith. Qed.

Lemma Z_of_signed_be_lower_bound_neg {n} (t : bits n) : [Z: true |:| t] >= - pow_of_2_Z n.
Proof. intros. simpl. 
  rewrite Zopp_succ. unfold Zpred ; ring_simplify.
  rewrite nat_of_binary_inverse. rewrite inj_minus, inj_S. unfold pow_of_2.
  ring_simplify. 
  autorewrite with Z_of_nat zarith. 
  rewrite Zmax_right. ring_simplify.
  autorewrite with Z_of_nat zarith. omega.
  generalize (Z_of_nat_of_binary_be_bound' t). intros ; omega.
Qed.

Ltac exists_hypothesis p :=
  match type of p with
    ?X =>
    match goal with
      | [ H : X |- _ ] => idtac
      | _ => fail 1
    end
  end.

Ltac add_bounds_of H T :=
  match T with
    | context [ Z_of_nat [: H ] ] => 
      let Hb := fresh "upper_bound" H in
      let Hb' := fresh "lower_bound" H in
        add_hypothesis Hb (Z_of_nat_of_binary_be_bound H) ;
        add_hypothesis Hb' (Z_of_nat_pos [:H])
        
    | context [ [: H ] ] => 
      let Hb := fresh "bound" H in
        exists_hypothesis (Z_of_nat_of_binary_be_bound H)
        || add_hypothesis Hb (nat_of_binary_bound H)
        
    (* [Z: ] *) 
    | context [ [Z: false |:| H ] ] => 
      let Hb := fresh "upperbound" H in
      let Hb' := fresh "lowerbound" H in
        add_hypothesis Hb (Z_of_signed_be_upper_bound_pos H) ;
        add_hypothesis Hb' (Z_of_signed_be_lower_bound_pos H)

    | context [ [Z: true |:| H ] ] => 
      let Hb := fresh "upperbound" H in
      let Hb' := fresh "lowerbound" H in
        add_hypothesis Hb (Z_of_signed_be_upper_bound_neg H) ;
        add_hypothesis Hb' (Z_of_signed_be_lower_bound_neg H)
        
  end.

Ltac add_hyps_bounds_of H := repeat
  match goal with
    [ _ : ?T |- _ ] => add_bounds_of H T
  end.

Ltac add_bounds := add_pow_bounds ;
  repeat
    match goal with
      | [ H : bits ?n |- ?T ] => progress ((try add_bounds_of H T) ; add_hyps_bounds_of H)
      | [ H : (vector bit ?n) |- ?T ] => progress ((try add_bounds_of H T) ; add_hyps_bounds_of H)
    end. 

Lemma Z_of_nat_of_binary_full n : Z_of_nat [: (@full n) ] = pow_of_2_Z n - 1.
Proof. intros. rewrite nat_of_binary_full. rewrite inj_minus, pow_of_2_nat_Z. 
  rewrite Zmax_right. simpl ; ring. add_bounds. simpl Z_of_nat. omega. 
Qed.

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
  autorewrite with zarith Z_of_nat pow_of_2.
  rewrite Zmax_right. omega. add_bounds ; omega.
Qed.

Hint Rewrite @Z_of_nat_binary_be_inverse @Z_of_signed_be_full : binary.


(** * Two's complement of a signed binary number. *)

Definition two_s_complement {n} (b : bits (S n)) :=
  let '(compl, _) := bits_succ_be (binary_inverse b) in
    (compl, Vhead b && Vhead compl).

(** A reformulation of [bits_succ_be_correct] for integers. *)

Ltac zauto := auto with zarith || omega.

Ltac zarith :=
  autorewrite with binary zarith pow_of_2 Z_of_nat in * ; 
    try ring_simplify ; try zauto ; add_bounds ; try zauto.
  
Lemma bits_succ_be_correct_Z (t : nat) (b c : bits (S t)) o : bits_succ_be b = (c, o) -> 
  if negb (Vhead b) && (Vhead c) then 
    b = (false |:| full) /\ c = binary_inverse b    
  else [Z: c ] = Zsucc [Z: b].
Proof.
  intros. destruct o. 
  apply bits_succ_be_overflow in H. destruct H ; subst.
  simpl. autorewrite with binary pow_of_2 Z_of_nat. ring.

  apply bits_succ_be_correct in H.
  depelim c ; depelim b. simpl.
  destruct a; simpl; simpl in x.
  simpl in *. destruct a0 ; simpl.
  assert ([: c] = S [: b]) by omega. zarith.

  add_bounds.
  assert ([: c] = 0)%nat by omega.
  rewrite H in x. autorewrite with arith in x.
  assert([: b ] = pow_of_2 t - 1)%nat by omega.
  rewrite <- (nat_of_binary_full t) in H0.
  inject H0. 
  rewrite <- (nat_of_binary_zero t) in H. inject H.
  unfold full ; autorewrite with binary. intuition auto.

  destruct a0; simpl; zarith.
Qed.

(** Correctness proof for two's complement. Only overflowing case is if we're taking
   the opposite of [-2^n]. *)

Lemma two_s_complement_correct {n} (x : bits (S n)) compl o : two_s_complement x = (compl, o) ->
  if o then x = min_signed /\ compl = x
  else [Z: compl ] = - [Z: x ].
Proof. unfold two_s_complement.
  intros.
  Opaque bits_succ_be.
  destruct_call_eq @bits_succ_be sinvx.
  apply bits_succ_be_correct_Z in sinvx.
  noconf H. zarith.
  depelim x ; depelim compl ; simpl in *.
  destruct a ; destruct a0 ; simpl in * ; try rewrite H0 ; zarith.
  destruct sinvx as [H H0]. noconf H ; noconf H0.
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

Ltac Z_of_nat := simp Z_of_nat_inv Z_of_nat.

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
  assert(Z_of_nat [: t] + Z_of_nat [: t'] >= pow_of_2_Z n) by Z_of_nat.
  split ; Z_of_nat. Z_of_nat.
Qed.

(** Signed multiplication correctness. *)
  
Lemma signed_plus_be_correct n : forall (t t' : bits (S n)) tt', signed_plus_be t t' = (tt', false) ->
  Z_of_signed_be tt' = Z_of_signed_be t + Z_of_signed_be t'.
Proof.
  intros. funind' (signed_plus_be t t'). depelim tt'.
  destruct_call_eq @binary_plus_be plusvv0.
  rewrite add_bits_correct in H.
  destruct_call_eq @add_bits_spec addaa0o.
  noconf H.
  apply binary_plus_be_correct_Z in plusvv0.
  destruct o; [destruct plusvv0|] ; destruct a ; destruct a0 ; noconf x ; simpl in * ; zarith.
Qed.

(** If there is an overflow, the sign depends on the sign of the result. *)
Transparent Z_of_sign.
Lemma Z_of_sign_0 : Z_of_sign 0%bin = 1.
Proof. reflexivity. Qed.
Lemma Z_of_sign_1 : Z_of_sign 1%bin = -1.
Proof. reflexivity. Qed.
Opaque Z_of_sign.

Hint Rewrite Z_of_sign_0 Z_of_sign_1 : zarith.
  
Lemma signed_plus_be_overflow n : forall (t t' : bits (S n)) tt', signed_plus_be t t' = (tt', true) ->
  Z_of_signed_be tt' + Z_of_sign (negb (Vhead tt')) * pow_of_2_Z (S n) = Z_of_signed_be t + Z_of_signed_be t'.
Proof.
  intros. funind' (signed_plus_be t t').
  depelim tt'.
  destruct_call_eq @binary_plus_be plusvv0.
  rewrite add_bits_correct in H.
  apply binary_plus_be_correct_Z in plusvv0.
  destruct_call_eq @add_bits_spec aa0o.
  noconf H.
  destruct o. destruct plusvv0. zarith. simpl. rewrite H0. 
  Opaque pow_of_2_Z Zminus Zmult.
  destruct a ; destruct a0 ; noconf x ; simpl ; zarith. 
  Transparent Zminus Zmult.
  omega.

  destruct a ; destruct a0 ; noconf x ; simpl in * ; rewrite plusvv0 ; zarith.
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
  destruct_call_eq @two_s_complement comply.
  apply two_s_complement_correct in comply.
  depelim b0. depelim t.
  destruct b. destruct b1.
  noconf H. 

  destruct comply. unfold min_signed. noconf H. 
  
  apply signed_plus_be_overflow in H.
  depelim x. depelim y.
  Opaque Zmult.

  Transparent Zminus.
  zarith. simpl in *. zarith.
  destruct a ; destruct a0; destruct a1; destruct a2; simpl in *;
    autorewrite with zarith in * ; try absurd_arith.

  ring_simplify in x1; ring_simplify in x.

  assert(Z_of_nat [:t] = Z_of_nat [:x0] + Z_of_nat [:b0]) by omega.
  unfold min_signed. rewrite H. right. zarith.

  right. ring_simplify in x1. 
  assert(Z_of_nat [:t] = Z_of_nat [:x0] - Z_of_nat [:y]) by omega.
  rewrite H. ring.

  destruct b1. noconf H.
  apply signed_plus_be_correct in H. rewrite H, comply. omega.
Qed.

Lemma nat_of_binary_be_vector_append_one {n} (b : bits n) c :
  [: vector_append_one b c ] = (2 * [: b ] + nat_of_bool c)%nat.
Proof.
  intros.
  Opaque vector_append_one.
  funind (vector_append_one b c) bc.
  destruct a. rewrite IHvector_append_one_ind. zarith.
  rewrite IHvector_append_one_ind. reflexivity.
Qed.

Hint Rewrite @nat_of_binary_be_vector_append_one : binary.

Lemma nat_of_binary_of_pos_be n p `{Have (Psize p <= n)%nat} : [: binary_of_pos_be n p] = nat_of_P p.
Proof. intros n p. revert n.
  induction p ; simpl ; intros ; auto.
  destruct n; simpl. bang.
  zarith; rewrite IHp; simpl nat_of_bool; autorewrite with nat_of_P; omega.

  destruct n; simpl. bang.
  zarith; rewrite IHp; simpl nat_of_bool; autorewrite with nat_of_P; omega.

  destruct n; simpl. bang.
  zarith; simpl nat_of_bool; autorewrite with nat_of_P; omega.
Qed.

Hint Rewrite @nat_of_binary_of_pos_be : binary.

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

Transparent pow_of_2_Z vector_append_one.

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

Hint Rewrite <- Pplus_one_succ_r : positive.
Hint Rewrite Psucc_o_double_minus_one_eq_xO : positive.

Theorem Z_of_signed_of_Z_inverse n z b :
  @signed_of_Z_be n z = Some b -> [Z: b] = z.
Proof.
  intros. induction z; try noconf H; zarith.
  simpl in H.
  case_eq_rew (dec (leb (Psize p) n)) lepn. noconf H.
  simpl. rewrite nat_of_binary_of_pos_be. 
  apply* Zpos_eq_Z_of_nat_o_nat_of_P.
  discriminate.

  simpl in H.
  case_eq_rew (dec (leb (Psize (Ppred p)) n)) lepn. 
  destruct p; noconf H; zarith.
  simpl. zarith. 

  simpl. repeat progress zarith. simpl. autorewrite with positive. 
  reflexivity. 

  destruct p ; noconf H; zarith.
Qed.

Lemma signed_of_Z_be_neg {n} (b : bits n) : [Z: true |:| b] = Zneg (P_of_succ_nat [: binary_inverse b]).
Proof.
  intros. simpl.
  case_eq_rew ([: binary_inverse b]) ninvb. 
  zarith.

  simpl. zarith.
  rewrite Pplus_one_succ_r. zarith.
Qed.

Derive NoConfusion for positive.

(** * Sign extension *)

Equations(nocomp) sx_be {n} (b : bits (S n)) (m : nat) : bits (S m + n) :=
sx_be n (Vcons x n b) m := if x then vector_append full b 
  else Vcons false (vector_append zero b).

Theorem sx_correct {n} (b : bits (S n)) m : [Z: sx_be b m] = [Z: b].
Proof.
  intros. Opaque Z_of_signed_be. funind (sx_be b m) bm. 
  destruct a. zarith.
  Transparent Z_of_signed_be.
  simpl in *. zarith. 
  
  simpl. zarith.
Qed.

Instance psize_psucc `(Have (Psize (Psucc p) <= n)%nat) : Have (Psize p <= n)%nat. 
Proof. unfold Have ; induction p ; simpl ; intros ; auto ;
  destruct n ; [inversion H|]; auto with *.
Qed.

Instance psize_S `(Have (Psize p <= n)%nat) : Have (Psize (p~0) <= S n)%nat. 
Proof. unfold Have. intros. simpl. omega. Qed.

Lemma binary_of_pos_be_Psucc (p : positive) n (Hs : Have (Psize (Psucc p) <= n)%nat) :
  [: binary_of_pos_be n (Psucc p) ] = S [: binary_of_pos_be n p ].
Proof.
  induction p; intros. simpl. destruct n ; simpl. bang.
  zarith. simpl. zarith. autorewrite with nat_of_P positive. omega.

  simpl. destruct n ; [inversion Hs|]. simpl. zarith.

  simpl. unfold Have in Hs. depelim Hs. simpl. zarith.

  simpl. destruct m. inversion Hs. simpl. zarith.
Qed.

Lemma binary_of_pos_be_binary_of_nat n (p : positive) (Hs : Have (Psize p <= n)%nat) : exists b,
  binary_of_nat_be n (nat_of_P p) = Some b /\ binary_of_pos_be n p = b.
Proof.
  intros n p. pattern p. apply Prect ; intros.
  simpl. destruct n. inversion Hs. simpl. exists (vector_append_one (@zero n) 1%bin). split ; reflexivity.
  
  rewrite nat_of_P_succ_morphism.
  simpl. destruct_call_eq nat_of_P np0. 
  generalize (lt_O_nat_of_P p0). absurd_arith.
  destruct (H (psize_psucc Hs)) as [b [H0 H1] ].
  subst. exists (binary_of_pos_be n (Psucc p0)). 
  rewrite H0. destruct_call_eq @bits_succ_be sucp0.
  
  destruct o. 
  apply bits_succ_be_overflow in sucp0.
  destruct sucp0 as [bz pf]. subst. 
  remember (binary_of_pos_be n (Psucc p0)).
  apply (f_equal nat_of_binary_be) in Heqb. rewrite binary_of_pos_be_Psucc in Heqb.
  rewrite pf in Heqb. rewrite nat_of_binary_full in Heqb. 
  zarith.

  apply bits_succ_be_correct in sucp0.
  split. f_equal. 
  apply nat_of_binary_be_inj. rewrite sucp0. 
  rewrite binary_of_pos_be_Psucc. reflexivity.
  reflexivity.
Qed.

Lemma pow_of_2_Z_S n : pow_of_2_Z (S n) = Zpos (pow_of_2_positive n)~0.
Proof. intros. zarith. Qed.
  
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
  
  simpl. zarith. unfold pow_of_2_Z in H.
  exploit (IHn p). Transparent Zmult. simpl in H. rewrite Zpos_xI, Zpos_xO in H.
  unfold pow_of_2_Z. omega. intros.
  omega.
  
  simpl. unfold pow_of_2_Z in H.
  simpl in H. 
  exploit (IHn p). rewrite Zpos_xO in H. rewrite (Zpos_xO p) in H. 
  unfold pow_of_2_Z. omega. intros. omega.
  
  simpl. omega.
Qed.

Lemma Zpos_p_nat_of_P p : Zpos p = Z_of_nat (nat_of_P p).
Proof. intro p ; pattern p ; apply Prect. 
  simpl. reflexivity.
  intros. autorewrite with nat_of_P Z_of_nat in *. 
  destruct p0; simpl ; reflexivity.
Qed.

Lemma Psize_succ p : (Psize p <= Psize (Psucc p))%nat.
Proof. induction p ; simpl ; auto with arith. Qed.
  
Lemma Psize_pred p : (Psize (Ppred p) <= Psize p)%nat.
Proof. apply Prect. simpl. reflexivity.
  intros. rewrite Ppred_succ. apply Psize_succ. Qed.

Definition Zsize (z : Z) :=
  match z with
    | Z0 => 1%nat
    | Zpos p => Psize p
    | Zneg p => Psize p
  end.


Lemma Psize_monotone : forall p q, (p <= q)%positive -> (Psize p <= Psize q)%nat.
Proof.
  assert (le0 : forall n, (0<=n)%nat) by (induction n; auto).
  assert (leS : forall n m, (n<=m -> S n <= S m)%nat) by (induction 1; auto).
  induction p; destruct q; simpl; auto; intros; try discriminate.
  apply leS. apply IHp. 
  intro.
  unfold Ple in H. simpl in H.
  apply H. rewrite Pcompare_Gt_eq_Gt. left ; auto.

  unfold Ple in H. simpl in H.
  apply leS. apply IHp. intro. apply H.
  rewrite <- Pcompare_eq_Gt. auto.
Qed.

Hint Resolve Zgt_pos_0 : zarith.

Lemma Zsize_monotone_pos : forall p q, p >= 0 -> p <= q -> (Zsize p <= Zsize q)%nat.
Proof. intros. destruct p ; destruct q ; simpl ; auto with arith.
  destruct p ; simpl ; auto with arith.
  apply Psize_monotone. apply H0.
Qed.

Lemma Zsize_monotone_neg : forall p q, q <= 0 -> p <= q -> (Zsize q <= Zsize p)%nat.
Proof. intros. destruct p ; destruct q ; simpl ; auto with arith.
  destruct p ; simpl ; auto with arith.
  apply Psize_monotone. unfold Zle in H0. simpl in H0. red. 
  intro. apply ZC1 in H1. rewrite H1 in H0. simpl in H0. elim H0 ; reflexivity.
Qed.

Lemma Psucc_minus_1 p : (Psucc p - 1 = p)%positive.
Proof. intros. rewrite <- Ppred_minus. rewrite Ppred_succ. reflexivity. Qed.

Hint Rewrite pow_of_2_nat_positive : nat_of_P_inv'.

Hint Rewrite <- nat_of_P_succ_morphism nat_of_P_plus_carry_morphism 
  Pmult_nat_l_plus_morphism nat_of_P_plus_morphism Pmult_nat_r_plus_morphism
  nat_of_P_mult_morphism Pmult_nat_mult_permute Pmult_nat_2_mult_2_permute 
  nat_of_P_xH nat_of_P_xO nat_of_P_xI
  Pmult_nat_4_mult_2_permute : nat_of_P_inv'.

Hint Rewrite
  pred_o_P_of_succ_nat_o_nat_of_P_eq_id : nat_of_P_inv'.

Lemma pos_Zpos_eq p q : Zpos p = Zpos q -> p = q.
Proof. intros. noconf H. Qed.

(* Lemma equal_fun {A B} (f : A -> B) (x y : A) : f x = f y -> f x = f y. *)
(* Proof. Print f_equ *)

(* Lemma Psucc_minus p q : (p - q = Psucc p - Psucc q)%positive. *)
(* Proof. *)
(*   intros p. pattern p. apply Prect. intros. *)
(*   simpl. destruct q ; simpl. unfold Pminus. simpl.  *)
(*   destruct q; simpl ; auto. *)
(*   destruct q; simpl ; auto. *)
(*   reflexivity. *)

(*   intros. *)
(*   rewrite Pplus_one_succ_l.  *)
(*   generalize (p0 + 1)%positive. intros. *)
(*   rewrite <- 2 Pplus_one_succ_r. *)

(*   destruct p1 ; destruct q ; simpl ; auto. compute. *)
(*   replace ( *)

(*   rewrite 2 nat_of_P_minus_morphism. *)
(*   autorewrite with nat_of_P. zarith. *)
  
  

  
(*   rewrite <- H. *)
  
(*   rewrite <- H. *)
  
(*   rewrite H0. *)

(*   apply pos_Zpos_eq. *)
(*   rewrite Zpos_minus_distr. *)
(*   rewrite Zpos_plus_distr. *)
  
  
  
  
(*   About ring_theory. *)
(*   autorewrite with nat_of_P_inv'. *)
  
(*   simpl. *)


(*   destruct q ; simpl. unfold Pminus. simpl. *)


(*   Lemma nat_of_P_minus p q : (p > q)%nat -> P_of_succ_nat (p - S q) = (P_of_succ_nat p - P_of_succ_nat q)%positive. *)
(*   Proof. *)
(*     induction p ; simpl ; intros ; auto with arith. *)
(*     inversion H. *)
    
(*     destruct p. simpl. destruct q. reflexivity. *)
(*     depelim H. inversion H.  *)

(*     simpl. destruct q ; simpl ; auto. *)
(*     simpl in IHp. rewrite Psucc_minus_1. *)
(*     reflexivity. *)

(*     simpl in IHp. rewrite IHp by omega. *)
    
(*     f_equal. *)
    
(*     simpl. *)

(*     simpl. *)
    


(*     intros p. pattern p. apply Prect. intros. simpl. *)
(*     case_eq_rew (nat_of_P q). *)
(*     generalize (lt_O_nat_of_P q). absurd_arith. *)
(*     Transparent Pminus. *)
(*     destruct q ; simpl; auto with arith.  *)

(*   Lemma nat_of_P_minus p q : (q < p)%positive -> nat_of_P (p - q) = (nat_of_P p - nat_of_P q)%nat. *)
(*   Proof. *)
(*     intros p. pattern p. apply Prect. intros. simpl. *)
(*     case_eq_rew (nat_of_P q). *)
(*     generalize (lt_O_nat_of_P q). absurd_arith. *)
(*     Transparent Pminus. *)
(*     destruct q ; simpl; auto with arith.  *)

(*     intros. autorewrite with nat_of_P. *)
(*     destruct q ; simpl; auto with arith.  *)
(*     unfold Psucc. simpl. *)
    
(*     simpl. *)
(*     rewrite nat_of_P_xI in H. noconf H.  *)
(*     simpl in H. *)
(*     compute in H. *)
    
(*     autorewrite with nat_of_P.  *)
(*     zarith. *)
    
(* inversion H0. *)
(*     rewrite <- H2. destruct q ; simpl ; auto. simpl. *)
  

(* apply Psize_monotone. *)
(*   simpl. assert(pow_of_2 n >= S [: b])%nat by omega. *)

(*   case_eq_rew [: b]. *)
(*   clear. *)
(*   assert(pow_of_2_positive n = P_of_succ_nat (pow_of_2 n - 1)). *)
(*   induction n. simpl ; auto. rewrite pow_of_2_positive_Sn. rewrite IHn.  *)
(*   simp pow_of_2. zarith.  *)
  
  
  
(*   replace (pow_of_2 (S n)) with 2 *  *)
(*   rewrite pow_of_2_Sn.  *)
(*   simp pow_of_2.  *)
  

(*   autorewrite with nat_of_P. *)
  

(*   simpl. destruct a. *)
(*   autorewrite with Z_of_nat_inv. *)
(*   apply inj_le. *)

Lemma Ple_1 : forall p, (p <= 1 -> p = 1)%positive.
Proof. intros. destruct p ; simpl ; auto. Qed.

(* Lemma Ple_Plt : forall x y, (Psucc x <= y -> x < y)%positive. *)
(* Proof. intros.  *)
(*   red. *)
(*   red in H. *)
(*   case_eq_rew ((Psucc x ?= y)%positive Eq).  *)
(*   apply Pcompare_Eq_eq in H0. subst. *)
(*   apply Pcompare_p_Sp. *)

(*   rewrite  *)

(*    discriminates. *)

(*   simpl. *)

(*   destruct (Pcompare_p_Sq y x) as (H',_).  *)
  

(* Instance: Transitive Ple. *)
(* Proof. red ; intros x y z. *)
(*   pattern y. apply Pind. intros. *)
(*   assert (H1:=Ple_1 _ H). subst x. assumption. *)

(*   intros. *)
  


(*   set (p':= Psucc p) in *. *)
  


(*   induction z using Pind; intros H H0. *)
  
(*   red in H0. *)
(*   destruct (Pcompare_p_Sq y z) as (H',_).  *)
(*   destruct (H' H1); subst; auto. *)
(*   intro. red in H. apply IHz. apply H. intro.  *)
(*   rewrite H4 in H2. discriminate. *)

(*   apply  *)
  
  
(*   apply H2. *)


(* Qed. *)

(*   red in H, H0. intro. *)
(*   apply H0. *)
  

(* Lemma P_of_succ_nat_minus x y : (P_of_succ_nat (x - y)%nat <= P_of_succ_nat x)%positive. *)
(* Proof. *)
(*   induction x. simpl. intros. auto.  *)

(*   intros. *)
(*   simpl. *)
(*   destruct y ; simpl. *)
(*   red. rewrite Pcompare_refl. auto. *)

  

(*   transitivity (P_of_succ_nat x). *)

(*   induction x  *)
(*   intros.  *)

  
(* Theorem Z_of_signed_size n (b : bits (S n)) : (Zsize [Z: b ] <= S n)%nat. *)
(* Proof. *)
(*   depelim b. *)
(*   destruct a. rewrite signed_of_Z_be_neg. simpl. *)
(*   transitivity (Zsize (pow_of_2_Z n)). *)
(*   2:simp pow_of_2; rewrite pow_of_2_positive_Psize; reflexivity. *)
(*   zarith. simp pow_of_2.   *)
(*   apply Psize_monotone.  *)
(*   clear. induction n  *)
(*   autorewrite with Z_of_nat_inv. *)
(*   zarith. simpl. *)
(*   case_eq_rew (pow_of_2 n - [:b])%nat. simpl. destruct n ; simpl ; auto with arith. *)
(*   simpl. apply Psize_monotone. *)
(*   assert(n0 = pow_of_2 n - [: b] - 1)%nat by omega. *)
(*   subst n0. *)
(*   autorewrite with nat_of_P. *)
(*   admit. *)

(*   simpl. *)
  
  
  



Theorem signed_of_Z_be_Z_of_signed_inverse n (b : bits (S n)) :
  signed_of_Z_be [Z: b ] = Some b.
Proof. intros. depelim b.
  destruct a.

  simpl. zarith. 
  autorewrite with Z_of_nat_inv. 
  case_eq_rew (Z_of_nat (S (pow_of_2 n) - S [: b])) zb; try absurd_arith.
  simpl in zb. rewrite inj_minus1 in zb by auto. absurd_arith. simpl in zb.
  rewrite inj_minus1 in zb by auto.
  simpl. destruct p. destruct_call dec. zarith.
  pose (binary_of_pos_be_binary_of_nat n _ (leb_complete _ _ e)).
  destruct e0 as [b' [H0 H1] ]. rewrite H1.
  repeat f_equal.
  simpl in H0. 
  autorewrite with nat_of_P in H0. 
  assert(Z_of_nat [:b] = pow_of_2_Z n - (2 * Zpos p + 1)) by omega.
  apply nat_of_binary_be_inj. apply inj_eq_rev. rewrite H.
  zarith. 
  rewrite (nat_of_binary_binary_of_nat_inverse _ _ _ H0).
  zarith.

  apply leb_complete_conv in e. simpl in e.
  assert (pow_of_2_Z n >= Zpos p~1) by zarith.
  assert (pow_of_2_Z n > Zpos p~0). apply Zlt_succ_gt.
  simpl. omega.
  pose (pow_of_2_size _ _ H0). simpl in g. absurd_arith.

  destruct_call dec. repeat f_equal.
  rewrite Zpos_xO in zb. 
  destruct (binary_of_pos_be_binary_of_nat n _ (leb_complete _ _ e)).
  destruct H as [H H'].
  apply nat_of_binary_binary_of_nat_inverse in H. 
  zarith. 
  apply nat_of_binary_be_inj. zarith. 
  rewrite <- H. rewrite <- H'.
  zarith. apply inj_eq_rev. 
  assert(Zb:Z_of_nat [:b] = - 2 * Zpos p + pow_of_2_Z n) by omega.
  rewrite Zb.
  rewrite inj_minus.
  rewrite pow_of_2_nat_Z. zarith.
  zarith.
  rewrite (Zplus_comm 1)%Z.
  fold (Zsucc (Zpos (Ppred p~0))).
  rewrite <- Zpos_succ_morphism. simpl Ppred.
  rewrite Psucc_o_double_minus_one_eq_xO.
  rewrite Zmax_right. zarith.
  rewrite Zpos_xO. zarith.
  
  apply leb_complete_conv in e.
    
  case_eq_rew [: b] nb.
  Transparent Z_of_nat. simpl in nb. zarith.
  unfold pow_of_2_Z in zb. noconf zb.
  rewrite <-x in e.
  destruct n. simpl in *. noconf x.
  rewrite (Psize_Ppred_pow_of_2_positive n) in e. 
  absurd_arith.
  
  autorewrite with pow_of_2 Z_of_nat in zb.
  assert(npos:pow_of_2_Z n > Zpos p~0) by omega.
  pose (pow_of_2_size _ _ npos).
  rewrite (Psize_pred (p~0)%positive) in e. absurd_arith.

  autorewrite with pow_of_2 Z_of_nat in zb.
  assert(Z_of_nat [:b] = pow_of_2_Z n - 1) by omega.
  rewrite <- Z_of_nat_of_binary_full in H. apply inj_eq_rev in H. inject H.
  reflexivity.

  assert(Z_of_nat [:b] - pow_of_2_Z n < 0) by omega. 
  generalize (pow_of_2_Z_pos n). intros.
  generalize (Z_of_nat_pos [:b]). intros.
  assert(pow_of_2_Z n - Z_of_nat [:b] < 0).
  rewrite inj_minus1 in zb by auto.
  autorewrite with Z_of_nat pow_of_2 in zb.
  pose (Zlt_neg_0 p). absurd_arith.

  simpl in zb. rewrite inj_minus1 in zb by auto.
  simpl. case_eq_rew [: b] nb. simpl.
  simpl in H. zarith. absurd_arith.

  zarith. simpl.
  case_eq_rew ([: b]) nb.
  simpl. rewrite <- (nat_of_binary_zero n) in nb. inject nb.
  reflexivity.

  simpl Z_of_nat.
  simpl.
  destruct_call dec.
  repeat f_equal. zarith.
  destruct (binary_of_pos_be_binary_of_nat n _ (leb_complete _ _ e)) as [ b' [H0 H1] ].
  rewrite H1. rewrite nat_of_P_o_P_of_succ_nat_eq_succ in H0. rewrite <- nb in H0.
  pose (nat_of_binary_binary_of_nat_inverse _ _ _ H0). 
  apply nat_of_binary_be_inj in e0. assumption.

  apply leb_complete_conv in e.
  generalize (nat_of_binary_bound b). intros.
  rewrite nb in H.
  assert(pow_of_2_Z n > Zpos (P_of_succ_nat n0)).
  rewrite <- pow_of_2_nat_Z.
  change (Zpos (P_of_succ_nat n0)) with (Z_of_nat (S n0)).
  apply inj_gt. omega.
  pose (pow_of_2_size _ _ H0). absurd_arith.
Qed.
