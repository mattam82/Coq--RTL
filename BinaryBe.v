Require Import CSDL.Binary.

Equations(nocomp) bits_succ_be {t} (c : bits t) : bits t * overflow :=
bits_succ_be O v := (v, true) ;
bits_succ_be (S n) (Vcons true n v) := let (v', rest) := bits_succ_be v in
  (Vcons true v', rest) ;
bits_succ_be (S n) (Vcons false n v) := let (v', rest) := bits_succ_be v in
  if rest then (Vcons true zero, false) 
  else (Vcons false v', false).

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

Global Transparent bits_succ_be.

Definition one {n} : bits (S n) := vector_append_one (constant_vector n false) true.

Eval compute in (binary_of_nat_be 8 1).
Eval compute in (binary_of_nat_be 8 255).


Equations(nocomp) nat_of_binary_be {t : nat} (c : bits t) : nat :=
nat_of_binary_be ?(O) Vnil := O ;
nat_of_binary_be ?(S n) (Vcons b n v) := let rest := nat_of_binary_be v in
  if b then pow_of_2 n + rest else rest.

Global Transparent nat_of_binary_be.

(* Eval compute in (nat_of_binary_be (representation 3 7)). *)

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

Lemma bits_succ_be_correct (t : nat) (b : bits t) (c : bits t) : bits_succ_be b = (c, false) -> 
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
  now apply bits_succ_be_correct in Hsb.

  now rewrite Hb'Sn in *.
Qed.


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

Opaque vfold_right2.

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

Open Local Scope vect_scope.  
Open Local Scope bin_scope.  

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

Global Transparent binary_minus_be binary_plus_be bits_succ_be constant_vector vfold_right2 vector_append_one.

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
  apply bits_succ_be_correct in H0.
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

  apply bits_succ_be_correct in H0.
  rewrite Heqtmp in H0. apply nat_of_binary_be_inj in H0. congruence.
Qed.

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

Opaque binary_shiftl.
Transparent nat_of_binary_be. 

Lemma binary_shiftl_be_correct {n} (t : bits n) t' o : binary_shiftl t = (t', o) ->
  if o then pow_of_2 n + nat_of_binary_be t' = 2 * nat_of_binary_be t
  else nat_of_binary_be t' = 2 * nat_of_binary_be t.
Proof. intros. 
  info funind (binary_shiftl t) shiftt generalizing t' o H. 
  destruct recres. noconf H. 
  case_eq_rew (binary_shiftl v). noconf shiftt. 
  destruct o; destruct o1 ; simpl ; omega.
Qed.

Transparent binary_shiftl.

Lemma binary_shiftl_n_be_correct {n} (t : bits n) m t' : binary_shiftl_n t m = (t', false) ->
  nat_of_binary_be t' = pow_of_2 m * nat_of_binary_be t.
Proof. intros n t m ; revert n t ; induction m ; intros.

    simp binary_shiftl_n in H. noconf H.

    simp binary_shiftl_n in H. 
    case_eq_rew (binary_shiftl t). destruct o. noconf H. 
    specialize (IHm _ _ _ H). rewrite IHm.
    rewrite (binary_shiftl_be_correct _ _ _ H0).
    rewrite mult_assoc at 1. setoid_rewrite mult_comm at 2. simpl.
    reflexivity.
Qed.

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
  apply binary_shiftl_n_be_correct in H0.
  apply binary_plus_be_correct in H.
  rewrite H.
  rewrite <- IHx. rewrite H0. ring.

  specialize (IHx _ _ H).
  assumption.
Qed.
Transparent binary_mult_be.


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
  Next Obligation. now erewrite bits_succ_be_correct. Qed.
  Next Obligation. now apply binary_plus_be_correct. Qed.
  Next Obligation. symmetry. now apply binary_minus_correct. Qed.
  Next Obligation. symmetry. now apply binary_mult_correct. Qed.

Global Transparent vfold_right2 binary_minus_be bits_succ_be nat_of_binary_be.

(** * Orders *)

Equations(nocomp) binary_be_le {n} (x y : bits n) : bool :=
binary_be_le O Vnil Vnil := true ;
binary_be_le (S n) (Vcons a n x) (Vcons a' n y) :=
  if xorb a a' then a'
  else binary_be_le x y.

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

Lemma binary_be_le_correct {n} (x y : bits n) : if binary_be_le x y then nat_of_binary_be x <= nat_of_binary_be y
  else nat_of_binary_be y < nat_of_binary_be x.
Proof. intros. induction n; depelim x ; depelim y ; simpl ; simp binary_be_le.

  auto.

  specialize (IHn x y).
  case_eq (xorb a a0). intros.
  destruct a0; destruct a ; try simpl in H ; noconf H.
  case_eq_rew (binary_be_le x y).
  omega.
  pose (nat_of_binary_bound x) ; omega.

  case_eq_rew (binary_be_le x y).
  pose (nat_of_binary_bound y) ; omega.
  omega.

  case_eq_rew (binary_be_le x y).
  destruct a0; destruct a ; try simpl in H0 ; noconf H0.
  omega.
  destruct a0; destruct a ; try simpl in H0 ; noconf H0.
  omega.
Qed.

Lemma binary_be_le_view {n} (x y : bits n) : binary_be_le x y = true <-> nat_of_binary_be x <= nat_of_binary_be y. 
Proof. intros. induction n; depelim x ; depelim y ; simpl ; simp binary_be_le.

  split ; auto.

  specialize (IHn x y).
  case_eq (xorb a a0) ; intros H ;
  destruct a0; destruct a ; try simpl in H ; noconf H ; auto.

  destruct IHn. split ; auto. intros.
  pose (nat_of_binary_bound x) ; omega.

  split ; auto.
  intros.
  generalize (nat_of_binary_bound y). intros. elimtype False. clear IHn. omega.
  destruct IHn.
  split ; intros ; auto.
  specialize (H H1). omega.

  apply H0.
  omega.
Qed.

Lemma binary_be_le_view' {n} (x y : bits n) : binary_be_le x y = false <-> nat_of_binary_be y < nat_of_binary_be x. 
Proof. intros. induction n; depelim x ; depelim y ; simpl ; simp binary_be_le.

  split ; intros ; auto with *.

  specialize (IHn x y).
  case_eq (xorb a a0) ; intros H ;
  destruct a0; destruct a ; try simpl in H ; noconf H ; auto.

  destruct IHn. split ; auto. intros.
  pose (nat_of_binary_bound x) ; absurd_arith.

  split ; intros ; auto.
  generalize (nat_of_binary_bound y). intros. clear IHn. omega.

  destruct IHn.
  split ; intros ; auto.
  specialize (H H1). omega.

  apply H0.
  omega.
Qed.

Definition binary_be_lt {n} (x y : bits n) := 
  let '(x', overflow) := bits_succ_be x in
    if overflow then false
    else binary_be_le x' y.

Instance: BoolIrreflexive (@binary_be_lt n).
Proof. reduce_goal. induction x ; simp binary_be_le.
  unfold binary_be_lt.
  unfold binary_be_lt in IHx.
  case_eq (bits_succ_be (a |:| x)).
  intros. destruct o. reflexivity.

  rewrite binary_be_le_view'.
  apply bits_succ_be_correct in H.
  rewrite H. omega.
Qed.
