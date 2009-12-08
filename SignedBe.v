Require Import CSDL.Binary CSDL.BinaryBe.
Require Import ZArith.

Open Local Scope vect_scope.
Open Local Scope Z_scope.

Definition sign_of_signed {n} (b : bits (S n)) : bit := Vhead b.
Definition Z_of_sign (b : bool) := if b then -1 else 1.
Definition Z_of_bool (b : bool) := if b then 1 else 0.
Definition min_signed {n} : bits (S n) := (true |:| zero).
Definition max_signed {n} : bits (S n) := (false |:| full).

Equations(nocomp) Z_of_signed_be {n} (b : bits n) : Z :=
Z_of_signed_be ?(O) Vnil := 0%Z ;
Z_of_signed_be ?(S n) (Vcons true n v) := - Zsucc (Z_of_nat ([: binary_inverse v ]))%Z ;
Z_of_signed_be ?(S n) (Vcons false n v) := Z_of_nat [: v ].

Equations(nocomp) signed_of_Z_be {n} (z : Z) : option (bits (S n)) :=
signed_of_Z_be n Z0 := Some zero ;
signed_of_Z_be n (Zpos p) <= dec (leb (Psize p) n) => {
  | left H := Some (Vcons false (binary_of_pos_be n p (Hp:=leb_complete _ _ H))) ;
  | right _ := None } ;

signed_of_Z_be n (Zneg xH) := Some full ;

signed_of_Z_be n (Zneg p) <= dec (leb (Psize (Ppred p)) n) => {
  | left H := Some (Vcons true (binary_inverse (binary_of_pos_be n (Ppred p) (Hp:=leb_complete _ _ H)))) ;
  | right _ := None }.

Notation " [Z:  x ] " := (Z_of_signed_be x).
Transparent pow_of_2_Z pow_of_2 vector_append_one.
Transparent signed_of_Z_be Zminus.

Eval compute in (@signed_of_Z_be 1 (-2)).
Eval compute in (@signed_of_Z_be 1 1).
Eval compute in (@signed_of_Z_be 1 2).
Eval compute in (@signed_of_Z_be 2 2).
Eval compute in (@signed_of_Z_be 2 3).
Eval compute in (@signed_of_Z_be 2 (-4)).
Eval compute in (@signed_of_Z_be 2 3).

Bind Scope vect_scope with bits.

Lemma Z_of_nat_binary_be {n} (t : bits n) : Z_of_nat [: t] = [Z: (false |:| t)].
Proof. intros. induction t. simpl. reflexivity. simpl. reflexivity. Qed.

Lemma Z_of_signed_be_zero n : [Z: @zero n] = 0.
Proof. induction n. simpl. reflexivity.
  unfold zero. simpl; simp Z_of_signed_be binary. 
Qed.

Lemma Z_of_signed_be_one n : [Z: @one (S n)] = 1.
Proof. induction n; simp Z_of_signed_be. Qed.

Hint Rewrite Z_of_signed_be_zero Z_of_signed_be_one : binary.

Lemma Z_of_nat_of_binary_be_bound {n} (t : bits n) : Z_of_nat [: t ] < pow_of_2_Z n.
Proof. rewrite <- pow_of_2_nat_Z. apply inj_lt. apply nat_of_binary_bound. Qed.

Hint Resolve inj_lt @nat_of_binary_bound : zarith.

Lemma Z_of_signed_be_upper_bound_pos {n} (t : bits n) : [Z: false |:| t] < pow_of_2_Z n.
Proof. intros. simpl. rewrite <- pow_of_2_nat_Z. simp Z_of_signed_be binary zarith. Qed.

Lemma Z_of_signed_be_lower_bound_pos {n} (t : bits n) : [Z: false |:| t] >= 0.
Proof. simp Z_of_signed_be binary zarith. Qed.

Lemma Z_of_signed_be_upper_bound_neg {n} (t : bits n) : [Z: true |:| t] < 0.
Proof. simp Z_of_signed_be binary zarith. Qed.

Lemma Z_of_signed_be_lower_bound_neg {n} (t : bits n) : [Z: true |:| t] >= - pow_of_2_Z n.
Proof. simp Z_of_signed_be binary pow_of_2.
  rewrite Zopp_succ. unfold Zpred ; ring_simplify.
  rewrite inj_minus, inj_S. simp pow_of_2. 
  ring_simplify. 
  rewrite Zmax_right. ring_simplify. omega.
  generalize (Z_of_nat_of_binary_be_bound t). intros ; omega.
Qed.

Lemma Z_of_signed_be_upper_bound {n} (t : bits n) : [Z: t] < pow_of_2_Z (pred n).
Proof.  generalize (pow_of_2_Z_pos (pred n)).  depelim t.
  intros. setoid_rewrite Z_of_signed_be_equation_1. simp pow_of_2. auto with zarith.
  destruct a. 
  
    generalize (Z_of_signed_be_upper_bound_neg t). intros. 
    transitivity 0; auto with zarith.

    generalize (Z_of_signed_be_upper_bound_pos t). auto.
Qed.

Instance: Transitive Zge.
Proof. reduce. 
  rewrite Zge_iff_le in H, H0. assert(z <= x). transitivity y; auto.
  rewrite <- Zge_iff_le in H2.
  red in H2. contradiction.
Qed.

Lemma Z_of_signed_be_lower_bound {n} (t : bits n) : 
  match n with 
    | 0%nat => [Z: t] >= 0 
    | S n => [Z: t] >= - pow_of_2_Z n
  end.
Proof.  generalize (pow_of_2_Z_pos n).  depelim t.
  intros. setoid_rewrite Z_of_signed_be_equation_1. simp pow_of_2. auto with zarith.

  destruct a. 
  
    generalize (Z_of_signed_be_lower_bound_neg t). auto. 

    generalize (Z_of_signed_be_lower_bound_pos t). auto.
    intros. transitivity 0; auto with zarith. simpl.
    compute. intros. discriminate.
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
Proof. rewrite nat_of_binary_full. rewrite inj_minus, pow_of_2_nat_Z. 
  rewrite Zmax_right. simpl ; ring. add_bounds. simpl Z_of_nat. omega. 
Qed.

(* Transparent Z_of_signed_be. *)
(* Eval compute in (Z_of_signed_be (@full 3)). *)

(** * Inverse. *)

Lemma Z_of_nat_binary_be_inverse n (b : bits n) :
  Z_of_nat [: binary_inverse b] = pow_of_2_Z n - Zsucc (Z_of_nat [: b ]).
Proof. simp binary.
  generalize (nat_of_binary_bound b). intros. rewrite inj_minus, inj_S.
  rewrite Zmax_right. rewrite pow_of_2_nat_Z. reflexivity.
  omega.
Qed.

Lemma Z_of_signed_be_full {n} : Z_of_signed_be (@full (S n)) = - 1.
Proof.
  intros. unfold full; simpl. simp Z_of_signed_be binary.
  unfold Zpred ; ring_simplify.
  rewrite inj_minus.
  autorewrite with zarith Z_of_nat pow_of_2.
  rewrite Zmax_right. omega. add_bounds ; omega.
Qed.

Hint Rewrite @Z_of_nat_binary_be_inverse @Z_of_signed_be_full : binary.
Hint Rewrite Z_of_nat_of_binary_full : Z_of_nat.

(** * Two's complement of a signed binary number. *)

Equations(nocomp) two_s_complement {n} (b : bits (S n)) : bits (S n) * overflow :=
two_s_complement n b <= bits_succ_be (binary_inverse b) => {
  | pair compl _ := (compl, Vhead b && Vhead compl) }.

(** A reformulation of [bits_succ_be_correct] for integers. *)

Ltac zauto := auto with zarith || omega.

Ltac zarith :=
  autorewrite with Z_of_signed_be binary zarith pow_of_2 Z_of_nat in * ; 
    try ring_simplify ; try zauto ; add_bounds ; try zauto.

Hint Unfold full zero : binary.

Instance bits_succ_be_correct_Z (t : nat) (b c : bits (S t)) o : 
  provided bits_succ_be b = (c, o) 
  have
    if negb (Vhead b) && (Vhead c) then 
      b = (false |:| full) /\ c = binary_inverse b    
    else [Z: c ] = Zsucc [Z: b].
Proof. intro. Opaque bits_succ_be. 
  funelim (bits_succ_be b); correct Heq; subst.

  simp binary.
  
  Opaque Zminus. 
  simp Z_of_signed_be binary zarith. rewrite Heq. 
  ring_simplify. unfold Zpred. zarith.
  
  unfold full. intuition; simp binary.
 
  simp binary Z_of_signed_be. rewrite Heq. zarith.
Qed.

(** Correctness proof for two's complement. Only overflowing case is if we're taking
   the opposite of [-2^n]. *)
Transparent two_s_complement.
Instance two_s_complement_correct {n} (x : bits (S n)) compl o : 
  provided two_s_complement x = (compl, o)
  have
    if o then x = min_signed /\ compl = x
    else [Z: compl ] = - [Z: x ].
Proof. intro. 
  funelim (two_s_complement x); correct Heq; subst.

  clear b0. autorewrite with binary in *.
  depelim b; depelim compl.
  simpl in *.
  destruct a; destruct a0; simpl in *; destruct_conjs;
    rew* ; simp Z_of_signed_be in *; zarith. 
  noconf H; noconf H0.
  apply binary_inverse_is_constant in H. subst. now trivial.
Qed.

Require Import ROmega.

Opaque vfold_right2.

(** Arithmetic operations in terms of unsigned arithmetic operations. 
   Overflow detection actually needs the last two carries for addition, 
   so we specialize it. *) 

Equations(nocomp) signed_plus_be {n} (t t' : bits (S n)) : bits (S n) * overflow :=
signed_plus_be n (Vcons s n t) (Vcons s' _ t') <= binary_plus_be t t' => {
  | pair add carry <= add_bits s s' carry => {
    | pair last carry' := (Vcons last add, xorb carry carry') } }.

(** Reformulation of binary addition correctness in terms of integers. *)

Ltac Z_of_nat := simp Z_of_nat_inv Z_of_nat.

Instance binary_plus_be_correct_Z n (t t' : bits n) tt' o :
  provided binary_plus_be t t' = (tt', o)
  have
  let add' := Z_of_nat [: t ] + Z_of_nat [: t'] in
    if o then add' >= pow_of_2_Z n /\
      Z_of_nat [: tt' ] = add' - pow_of_2_Z n
    else Z_of_nat [: tt' ] = add'.
Proof. intro. correct H.
  destruct o ; program_simpl; zarith.
  rewrite H0; Z_of_nat. zarith.
Qed.

(** Signed multiplication correctness. *)
  
Instance signed_plus_be_correct n (t t' : bits (S n)) tt' : 
  provided signed_plus_be t t' = (tt', false)
  have [Z: tt' ] = [Z: t ] + [Z: t' ].
Proof. intro. 
  funelim (signed_plus_be t t'); simp binary Z_of_signed_be. 
  correct Heq0.
  destruct b0; funelim (add_bits a a0 b); try noconf Heq; try noconf H2;
    simp binary Z_of_signed_be; 
    destruct_conjs; autorewrite_local;
    zarith.
Qed.

(** If there is an overflow, the sign depends on the sign of the result. *)
Transparent Z_of_sign.
Lemma Z_of_sign_0 : Z_of_sign 0%bin = 1.
Proof. reflexivity. Qed.
Lemma Z_of_sign_1 : Z_of_sign 1%bin = -1.
Proof. reflexivity. Qed.
Opaque Z_of_sign.

Hint Rewrite Z_of_sign_0 Z_of_sign_1 : zarith.
  
Hint Rewrite andb_true_l andb_true_r orb_true_l orb_true_r xorb_true_l xorb_true_r 
  andb_false_l andb_false_r orb_false_l orb_false_r xorb_false_l xorb_false_r 
  negb_involutive : bool.
Transparent Zminus.
Hint Opaque Zminus Zplus Zmult Zdiv : zarith.

Ltac simpl_ctx :=
  simpl in * |-; destruct_conjs; autorewrite_local.

Hint Extern 0 => progress simpl_ctx : solve.
Hint Extern 0 => progress (simp binary pow_of_2 Z_of_signed_be Z_of_nat) : solve.

Instance signed_plus_be_overflow n (t t' : bits (S n)) tt' : 
  provided signed_plus_be t t' = (tt', true)
  have [Z: tt'] + Z_of_sign (negb (Vhead tt')) * pow_of_2_Z (S n) = 
   [Z: t ] + [Z: t'].
Proof. intro.
  funelim (signed_plus_be t t').
  correct Heq0. 
  destruct b; destruct b1; noconf H2. rewrite add_bits_correct in Heq. noconf Heq.
  destruct a; destruct a0; noconf H. simpl. zarith.
  destruct a; destruct a0; noconf Heq. simpl. zarith.
Qed.

(** Signed substraction [signed_plus_be] is just addition of the opposite. *)

Equations(nocomp) signed_minus_be {n} (x y : bits (S n)) : bits (S n) * borrow :=
signed_minus_be n x y <= two_s_complement y => {
  | pair compl true := (y, true) ;
  | pair compl false := signed_plus_be x compl }.
  
Transparent Zmult Zdouble.
Lemma signed_minus_be_correct {n} (x y t : bits (S n)) b : 
  impl (signed_minus_be x y = (t, b))
  (if b then 
    (y = min_signed /\ t = y) \/
    (Z_of_signed_be t + Z_of_sign (negb (Vhead t)) * pow_of_2_Z (S n) = Z_of_signed_be x - Z_of_signed_be y)
  else Z_of_signed_be t = (Z_of_signed_be x - Z_of_signed_be y)).
Proof. intro.
  funelim (signed_minus_be x y); correct Heq; simpl in Heq. 
    left. intuition.

    destruct b; correct H; rew*; auto. 
Qed.

Hint Rewrite @signed_minus_be_correct : signed_minus_be.

Ltac bang :=
  match goal with
    | |- context [ False_rect _ ?p ] => elim p
    | |- context [ False_rec _ ?p ] => elim p
  end.

Hint Extern 4 => bang : exfalso.

Tactic Notation "apply" "*" constr(c) := apply c || symmetry ; apply c.

(** Representing integers by signed binary numbers. *)

Transparent pow_of_2_Z pow_of_2 vector_append_one.
Transparent signed_of_Z_be Zminus.
(*
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
*)
Hint Rewrite <- Pplus_one_succ_r : positive.
Hint Rewrite Psucc_o_double_minus_one_eq_xO : positive.

Instance Z_of_signed_of_Z_inverse n z b :
  provided @signed_of_Z_be n z = Some b
  have [Z: b] = z.
Proof. intro.
  funelim (signed_of_Z_be (n:=n) z); simp Z_of_signed_be Z_of_nat binary.

  clear H. destruct n; try noconf e. apply leb_complete in e. 
  zarith.

  clear H. apply leb_complete in e. repeat zarith.
  simpl. autorewrite with positive. reflexivity.
Qed.

Derive NoConfusion for positive.

(** * Sign extension *)

Equations(nocomp) sx_be {n} (b : bits (S n)) (m : nat) : bits (S m + n) :=
sx_be n (Vcons true n b) m := vector_append full b ;
sx_be n (Vcons false n b) m := Vcons false (vector_append zero b).

Theorem sx_correct {n} (b : bits (S n)) m : [Z: sx_be b m] = [Z: b].
Proof. Opaque Zminus. funelim (sx_be b m); simp binary Z_of_signed_be; zarith. Qed.

Lemma psize_psucc `(Have (Psize (Psucc p) <= n)%nat) : Have (Psize p <= n)%nat. 
Proof. unhave. revert n H ; induction p ; simpl ; intros ; auto;
  destruct n; auto with *.
Qed.

Hint Extern 0 (Have (Psize ?p <= ?n)%nat) => 
  class_apply @psize_psucc; assumption : typeclass_instances.

Instance psize_S `(Have (Psize p <= n)%nat) : Have (Psize (p~0) <= S n)%nat. 
Proof. unhave. intros. simpl. omega. Qed.

Lemma Psize_pos p : (Psize p > 0)%nat.
Proof. destruct p ; simpl ; auto with arith. Qed.

Lemma binary_of_pos_be_Psucc (p : positive) n (Hs : Have (Psize (Psucc p) <= n)%nat) :
  [: binary_of_pos_be n (Psucc p) ] = S [: binary_of_pos_be n p ].
Proof. autorewrite with binary nat_of_P. reflexivity. Qed.

Lemma binary_of_pos_be_binary_of_nat n (p : positive) (Hs : Have (Psize p <= n)%nat) : 
  binary_of_nat_be n (nat_of_P p) = Some (binary_of_pos_be n p).
Proof. Opaque binary_of_nat_be binary_of_pos_be.
  rewrite <- (nat_of_binary_of_pos_be n p).
  rewrite binary_of_nat_inverse. reflexivity.
Qed.

Lemma pow_of_2_Z_S n : pow_of_2_Z (S n) = Zpos (pow_of_2_positive n)~0.
Proof. intros. zarith. Qed.
  
Lemma pow_of_2_positive_Psize n : Psize (pow_of_2_positive n) = S n.
Proof. intros. induction n ; simpl ; auto. Qed.
  
Lemma Psize_Ppred_pow_of_2_positive n : Psize (Ppred (pow_of_2_positive (S n))) = S n.
Proof. intros. induction n ; simpl ; auto. Qed.
  
Derive NoConfusion for Datatypes.comparison Z.

Lemma pow_of_2_size n : forall p, pow_of_2_Z n > Zpos p -> (n >= Psize p)%nat.
Proof. 
  induction n ; intros. simp pow_of_2 in H.
  unfold Zgt in H. destruct p; noconf H.

  destruct p; simpl in H; simpl; auto with arith;
  exploit (IHn p); simp pow_of_2 in H; zarith;
  auto with arith.
Qed.

Lemma Zpos_p_nat_of_P p : Zpos p = Z_of_nat (nat_of_P p).
Proof. zarith. Qed.

Lemma Psize_succ p : (Psize p <= Psize (Psucc p))%nat.
Proof. induction p ; simpl ; auto with arith. Qed.
  
Lemma Psize_pred p : (Psize (Ppred p) <= Psize p)%nat.
Proof. revert p; apply Prect. simpl. reflexivity.
  intros. rewrite Ppred_succ. apply Psize_succ. Qed.

Definition Zbits (z : Z) :=
  match z with
    | Z0 => 0%nat
    | Zpos p => S (Psize p)
    | Zneg xH => 1%nat
    | Zneg p => S (Psize (Ppred p))
  end.

Definition Zsize (z : Z) :=
  match z with
    | Z0 => 1%nat
    | Zpos p => Psize p
    | Zneg p => Psize p
  end.

(*
Eval compute in (Zbits 0).
Eval compute in (Zbits 1).
Eval compute in (Zbits 2).
Eval compute in (Zbits (-1)).
Eval compute in (Zbits (-2)).
Eval compute in (Zbits (-3)).
Eval compute in (Zbits (-pow_of_2_Z 4)).
*)
Transparent pow_of_2_Z Zminus.

Instance Psize_monotone : Proper (Ple ==> le) Psize.
Proof. intros p.
  assert (le0 : forall n, (0<=n)%nat) by (induction n; auto).
  assert (leS : forall n m, (n<=m -> S n <= S m)%nat) by (induction 1; auto).
  induction p; intros q; destruct q; simpl; auto with exfalso; intros; try discriminate.
  apply leS. apply IHp. 
  intro.
  unfold Ple in H. simpl in H.
  apply H. rewrite Pcompare_Gt_eq_Gt. left ; auto.

  unfold Ple in H. simpl in H.
  apply leS. apply IHp. intro. apply H.
  rewrite <- Pcompare_eq_Gt. auto.
Qed.

Hint Resolve Zgt_pos_0 : zarith.

Lemma Zbits_monotone_pos : forall p q, p >= 0 -> p <= q -> (Zbits p <= Zbits q)%nat.
Proof. intros. destruct p ; destruct q ; simpl ; auto with arith exfalso.
  apply le_n_S.
  apply Psize_monotone. apply H0.
Qed.

Lemma Psize_Pdoubleminus_one p : (Psize (Pdouble_minus_one p) <= S (Psize p))%nat.
Proof.
  induction p ; simpl ; auto with arith.
Qed.

Lemma S_Psize_0 p : S (Psize p) = Psize (p~0).
Proof. simpl. reflexivity. Qed.

Lemma S_Psize_1 p : S (Psize p) = Psize (p~1).
Proof. simpl. reflexivity. Qed.

Instance Plt_Ple : subrelation Plt Ple.
Proof. reduce. red in H. rewrite H in H0. discriminate. Qed.

Instance Ple_trans : Transitive Ple.
Proof. reduce. red in H. red in H0.
  destruct_call_eq (Pcompare x y) xy; try discriminates.
  apply Pcompare_Eq_eq in xy. subst.
  rewrite H1 in H0; discriminates.

  destruct_call_eq (Pcompare y z) yz; try discriminates.
  apply Pcompare_Eq_eq in yz. subst. rewrite H1 in xy; discriminates.
  assert (tr:=Plt_trans _ _ _ xy yz). red in tr. rewrite tr in H1; discriminates.
Qed.

Instance Plt_trans : Transitive Plt.
Proof. exact Plt_trans. Qed.

Instance: Injective Psucc.
Proof. intro. induction x; destruct y; simpl in *; intros; try congruence. noconf H. 
  specialize (IHx _ H); congruence.
  noconf H. destruct x; simpl in *; try congruence.
  destruct y; simpl in *; try congruence.
Qed.

Lemma Pcompare_Psucc_Psucc p q : (Psucc p ?= Psucc q)%positive Eq = Lt <-> (p ?= q)%positive Eq = Lt.
Proof.
  split ; intros.
  apply nat_of_P_lt_Lt_compare_complement_morphism.
  apply nat_of_P_lt_Lt_compare_morphism in H.
  autorewrite with nat_of_P in *.  omega.
  apply nat_of_P_lt_Lt_compare_complement_morphism.
  apply nat_of_P_lt_Lt_compare_morphism in H.
  autorewrite with nat_of_P in *. omega.
Qed.

Lemma nat_of_P_le : forall p q:positive, (p <= q)%positive <-> (nat_of_P p <= nat_of_P q)%nat.
Proof.
  intros. split; intros. 

    red in H. destruct_call_eq Pcompare pq. apply Pcompare_Eq_eq in pq. subst. reflexivity.
    apply nat_of_P_lt_Lt_compare_morphism in pq.
    auto with arith.
    discriminates.

    intro.
    apply nat_of_P_gt_Gt_compare_morphism in H0.
    omega.
Qed.

Lemma Ppred_le p q : (p <= q)%positive -> (Ppred p <= Ppred q)%positive.
Proof. 
  revert q. pattern p. apply Prect; intros. 
  simpl. destruct q; simpl; auto. destruct q; simpl; auto. compute. intros. discriminate.

  revert H0. pattern q; apply Pcase.
  intros. simpl. rewrite Ppred_succ. rewrite <- H0. intro.
  rewrite Pcompare_p_Sp in H1. discriminate.

  intros.
  rewrite ! Ppred_succ.
  rewrite ! nat_of_P_le in *. 
  simp nat_of_P in *; try omega.
Qed.

Lemma nat_of_P_double_minus_one p : nat_of_P (Pdouble_minus_one p) = (2 * nat_of_P p - 1)%nat.
Proof.
  induction p ; simpl ; simp nat_of_P. ring_simplify. 
  simp nat_of_P. unfold nat_of_P. omega.
  rewrite IHp. generalize (lt_O_nat_of_P p). intros. omega.
Qed.

Hint Rewrite nat_of_P_double_minus_one : nat_of_P.
    
Lemma Pcompare_Pdouble_Pdouble p q : (Pdouble_minus_one p ?= Pdouble_minus_one q)%positive Eq = Gt ->
  (p ?= q)%positive Eq = Gt.
Proof. intros.
  apply nat_of_P_gt_Gt_compare_morphism in H.
  apply nat_of_P_gt_Gt_compare_complement_morphism.
  simp nat_of_P in H. omega.
Qed.

Instance Pdouble_minus_one_le : Proper (Ple ==> Ple) Pdouble_minus_one.
Proof. reduce.
  red in H. reverse. intros x. pattern x. apply Pcase.
  simpl. intros. 
  case_eq_rew ((1 ?= y)%positive Eq) np; try apply Pcompare_Eq_eq in np;
  destruct y; simpl in *; try congruence. 

  intros P y. pattern y. apply Pcase. intros.
  destruct P; simpl in *; try congruence.

  intros.
  apply Pcompare_Pdouble_Pdouble in H0. congruence.
Qed.

Lemma Zbits_neg p : Zbits (Zneg p) = Zbits
  (match p with 
     | xH => -1
     | _ => (Zpos (Ppred p))
  end).
Proof. induction p; simpl; auto. Qed.

Hint Resolve Psize_monotone Ppred_le : positive.
Hint Unfold Zbits : zarith.

Lemma Zbits_monotone_neg : forall p q, q < 0 -> p <= q -> (Zbits q <= Zbits p)%nat.
Proof. intros.
  destruct p ; destruct q ; auto with arith exfalso.

  red in H0. simpl in H0. rewrite Pcompare_antisym in H0. simpl in H0.
  change (p0 <= p)%positive in H0.
  rewrite ! Zbits_neg.
  destruct p0; destruct p; 
    try (red in H0 ; simpl in H0) ;
    try solve [ try discriminates; unfold Zbits; auto with arith positive ].
Qed.

Lemma Zsize_monotone_pos : forall p q, p >= 0 -> p <= q -> (Zsize p <= Zsize q)%nat.
Proof. intros. destruct p ; destruct q ; simpl ; auto with arith exfalso.
  generalize (Psize_pos p); omega.
  apply Psize_monotone. apply H0.
Qed.

Lemma Zsize_monotone_neg : forall p q, q <= 0 -> p <= q -> (Zsize q <= Zsize p)%nat.
Proof. intros. destruct p ; destruct q ; simpl ; auto with arith exfalso.
  generalize (Psize_pos p); omega.
  apply Psize_monotone. 
  intro. apply ZC1 in H1. red in H0. simpl in H0. apply H0. unfold CompOpp. 
  rewrite H1. reflexivity.
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

Lemma Ple_1 : forall p, (p <= 1 -> p = 1)%positive.
Proof. intros. destruct p ; simpl ; zarith. Qed.

Instance: Injective Zopp := Zopp_inj.
Instance: Injective Zsucc := Zsucc_inj.
Instance: Injective Z_of_nat := inj_eq_rev.
Instance negb_inj : Injective negb. 
Proof. reduce. destruct x; destruct y; noconf H. Qed.

Instance Vunary_inj {A} `(I : Injective A A f) : Injective (Vunary _ f n).
Proof. reduce. induction x; depelim y. noconf H. 
  simpl in H. noconf_ref H; simplify_dep_elim. inject H. now rewrite (IHx _ H0).
Qed.

Instance inj_inverse n : Injective (@binary_inverse n) := Vunary_inj negb_inj.

Instance: Injective (@Z_of_signed_be n).
Proof. reduce. funelim [Z: x]; funelim [Z: y];
  try solve [now repeat inject H]. 

  pose (Z_of_nat_pos). absurd_arith.
  pose (Z_of_nat_pos). absurd_arith.
Qed.

Lemma Z_neg_P_of_succ : forall n, - Zsucc (Z_of_nat n) = Zneg (P_of_succ_nat n).
Proof. induction n. simpl. reflexivity.
  simpl. autorewrite with positive. reflexivity.
Qed.

Hint Rewrite Z_neg_P_of_succ : zarith.
  
Lemma Z_of_nat_S n : Z_of_nat (S n) = Zpos (P_of_succ_nat n).
Proof. reflexivity. Qed.

Lemma signed_of_Z_be_correct p t : (Zsize (Zpos p) <= t)%nat -> exists x, signed_of_Z_be (n:=t) (Zpos p) = Some x.
Proof.
  intros. simpl in H. funelim (signed_of_Z_be (n:=t) (Zpos p)); try solve [ econstructor; eauto ].

  clear Heq; exfalso. apply leb_complete_conv in e. omega.
Qed.

Lemma signed_of_Z_be_correct' z t : (Zbits z <= (S t))%nat -> 
  exists x, signed_of_Z_be (n:=t) z = Some x.
Proof.
  intros. simpl in H. funelim (signed_of_Z_be (n:=t) z); try solve [ econstructor; eauto ].

  clear Heq; exfalso. apply leb_complete_conv in e. omega.
  clear H; exfalso. destruct n. absurd_arith. apply leb_complete_conv in e. omega.
  clear H; exfalso. apply leb_complete_conv in e.
  omega.
Qed.

Lemma Zsize_pow_of_2 n : Zsize (pow_of_2_Z n) = S n.
Proof.
  induction n; simp pow_of_2; simpl in *; zarith.
Qed.

Lemma Zbits_pow_of_2 n : Zbits (pow_of_2_Z n) = S (S n).
Proof.
  induction n; simp pow_of_2; simpl in *; zarith. 
Qed.

Instance: Proper (le ==> le) S.
Proof. reduce. omega. Qed.

Transparent binary_of_pos_be.

Lemma Zbits_opp_pow_of_2 n : (Zbits (- pow_of_2_Z n) = S n)%nat.
Proof.
  induction n; simp pow_of_2; simpl in *; zarith.
  destruct_call pow_of_2_positive; simpl in *; noconf IHn. omega.
Qed.

Lemma Zsize_opp z : (Zsize (- z) <= S (Zsize z))%nat.
Proof. destruct z ; simpl ; auto. Qed.

Hint Resolve Psize_monotone : zarith.
Hint Resolve le_n_S : zarith.

Instance: Proper (Ple ==> le) (fun x => Zsize (Zpos x)).
Proof. reduce. simpl. auto with zarith. Qed.

Lemma Zsucc_minus_1 n : Zsucc n - 1 = n.
Proof. zarith. Qed.

Hint Rewrite Zsucc_minus_1 : zarith.

Lemma Zpos_lt_n_Zsize p n : Zpos p < pow_of_2_Z n -> (Psize p < (S n))%nat.
Proof. revert p. induction n; intros. simp pow_of_2 in H. 
  destruct p; try destruct p; try discriminate.
  Transparent pow_of_2_Z. unfold pow_of_2_Z in H.
  destruct p; simpl in *.
  red in H. simpl in H. apply le_n_S. apply IHn.
  unfold pow_of_2_Z. red. simpl. apply Pcompare_Gt_Lt in H. assumption.
  red in H. simpl in H. apply le_n_S. apply IHn. red. auto.

  auto with arith.
Qed.

Lemma Zbits_Z_of_signed {n} (v : bits n) : (Zbits [Z: v] <= n)%nat.
Proof.
  destruct n. depelim v.
  setoid_rewrite Z_of_signed_be_equation_1. auto.

  generalize (Z_of_signed_be_lower_bound v).
  generalize (Z_of_signed_be_upper_bound v).
  generalize ([Z: v]). intros.
  generalize (Zbits_pow_of_2 n).
  intros; simpl in *.
  destruct z. simpl; auto with arith zarith. simpl.
  apply Zpos_lt_n_Zsize in H. 
  simpl; auto with arith zarith.

  rewrite <- Zbits_opp_pow_of_2.
  unfold pow_of_2_Z.
  simpl Zopp. apply Zbits_monotone_neg. compute. auto.
  omega.
Qed.
 
Theorem signed_of_Z_be_Z_of_signed_inverse n (b : bits (S n)) :
  signed_of_Z_be [Z: b ] = Some b.
Proof.
  assert (H:=Zbits_Z_of_signed b).
  destruct (signed_of_Z_be_correct' [Z: b] n H). 
  rewrite H0. apply Z_of_signed_of_Z_inverse in H0. inject H0. reflexivity.
Qed.
