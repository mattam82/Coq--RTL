Require Import CSDL.Binary.

Class Correctness (cond : Prop) (concl : Prop) :=
  correctness_prf : impl cond concl.

Notation "'provided' c 'have' t" := (Correctness c t)
  (only parsing, at level 100, c at next level, t at next level).

Ltac simplify_hyp H :=
  match type of H with
    | ?P /\ ?Q => 
      let freshH := fresh H in
        destruct H as [H freshH];
          simplify_hyp H; simplify_hyp freshH
    | _ => idtac
  end.

Ltac correct H := 
  let ty := type of H in
  let prf := constr:(correctness_prf (cond:=ty)) in
    rewrite prf in H; simplify_hyp H.

Definition nat_of_bool (b : bool) := if b then 1%nat else 0%nat.

(** * Semantics of an unsigned big-endian vector. *)

Equations(nocomp) nat_of_binary_be {t : nat} (c : bits t) : nat :=
nat_of_binary_be ?(O) Vnil := O ;
nat_of_binary_be ?(S n) (Vcons b n v) := let rest := nat_of_binary_be v in
  if b then pow_of_2 n + rest else rest.

Global Transparent nat_of_binary_be.

Notation " [:  x ] " := (nat_of_binary_be x).

Lemma nat_of_binary_zero n : [: zero (n:=n) ] = 0%nat.
Proof. induction n ; simpl ; auto. Qed.

Definition one {n} : bits (S n) := vector_append_one (constant_vector n false) true.

Lemma nat_of_binary_one n : [: @one n ] = 1%nat.
Proof. induction n ; simpl ; auto. Qed.

Ltac autorew := autorewrite with pow_of_2 nat_of_P in * ; simpl.

Lemma nat_of_binary_full n : [: @full n ] = pow_of_2 n - 1.
Proof. 
  induction n ; simpl ; auto with *. unfold full in *. rewrite IHn.
  autorewrite with pow_of_2 in *. omega.
Qed.

Lemma nat_of_binary_bound {n} (x : bits n) : nat_of_binary_be x < pow_of_2 n.
Proof.
  induction n ; intros. depelim x. simpl. auto.
  depelim x. destruct a ; simpl ; autorewrite with pow_of_2; auto with arith. 
Qed.

Hint Rewrite nat_of_binary_zero nat_of_binary_one nat_of_binary_full : binary.

Lemma nat_of_binary_be_inj n (t t' : bits n) : [: t ] = [: t' ] -> t = t'.
Proof.
  induction n. depelim t ; depelim t' ; auto with *.

  intros.
  revert IHn.
  depelim t. depelim t' ; intros; auto with *.
  simpl in H. destruct a; destruct a0 ; auto;
  try rewrite (IHn t t') by omega ; try reflexivity.
  generalize (nat_of_binary_bound t'). generalize (pow_of_2_pos n). absurd_arith.
  generalize (nat_of_binary_bound t). generalize (pow_of_2_pos n). absurd_arith.
Qed.

Hint Resolve nat_of_binary_be_inj : binary.

Hint Extern 4 => progress (autorewrite with binary) : binary.

Instance: Injective (@nat_of_binary_be n) := nat_of_binary_be_inj.

Lemma nat_of_binary_be_eq_rect m n v (H : m = n) : [: eq_rect m (λ h, bits h) v n H ] = [: v ].
Proof. subst. simpl. reflexivity. Qed.
Opaque vector_append.
Lemma nat_of_binary_be_vector_append {n m} (v : bits n) (w : bits m) :
  ([: vector_append v w ] = pow_of_2 m * [: v ] + [: w ])%nat.
Proof. funelim (vector_append v w).

  now rewrite mult_comm.

  destruct a; simpl; rewrite H.
    rewrite pow_of_2_plus. ring.
    
    reflexivity.
Qed.

Hint Rewrite @nat_of_binary_be_vector_append nat_of_binary_be_eq_rect : binary.

(** * Inverse *)

Lemma nat_of_binary_inverse {n} (x : bits n) : 
  [: binary_inverse x ] = pow_of_2 n - S [: x ].
Proof.
  induction n ; intros.
  
    now depelim x. 
    
    simpl in *.
    case_eq (pow_of_2 (S n)). 
    generalize (Basics.pow_of_2_pos (S n)). absurd_arith.
    
    intros.
    depelim x.
    simpl. 
    rewrite IHn. case_eq (pow_of_2 n).
    generalize (pow_of_2_pos n). 
    intros ; elimtype False ; omega.
    intros. autorewrite with pow_of_2 in H.
    rewrite H0 in H. simpl in H.
    rewrite plus_comm in H. noconf H.
    
    destruct a ; simpl. 
    omega.
    
    case_eq (nat_of_binary_be x); intros. omega.
    pose (nat_of_binary_bound x). 
    rewrite H0 in l. omega.
Qed.

Hint Rewrite @nat_of_binary_inverse : binary.

Require Import BinPos.

Lemma nat_of_binary_be_vector_append_one {n} (b : bits n) c :
  [: vector_append_one b c ] = (2 * [: b ] + nat_of_bool c)%nat.
Proof.
  Opaque vector_append_one.
  funelim (vector_append_one b c); simpl. 
  destruct a0; simpl. rewrite H. ring_simplify. pose (nat_of_binary_bound v). 
  simpl. simp pow_of_2. omega.
  assumption.
Qed.

Hint Rewrite @nat_of_binary_be_vector_append_one : binary.

Lemma nat_of_binary_of_pos_be n p {Hp: Have (Psize p <= n)} : 
  [: binary_of_pos_be n p ] = nat_of_P p.
Proof.
  funelim (binary_of_pos_be n p);
  autorewrite with binary.
  rewrite H.
  simpl. simp nat_of_P. omega.
  rewrite H.
  simpl. simp nat_of_P. omega.
  simpl. reflexivity.
Qed.

Hint Rewrite @nat_of_binary_of_pos_be : binary.

(** * Successor: adding 1. *)

Equations(nocomp) bits_succ_be {t} (v : bits t) : bits t * overflow :=
bits_succ_be O v := (v, true) ;

bits_succ_be (S n) (Vcons true n v) <= bits_succ_be v => {
  | pair v' true := (Vcons false v', true) ;
  | pair v' false := (Vcons true v', false) } ;

bits_succ_be (S n) (Vcons false n v) <= bits_succ_be v => {
  | pair v' true := (Vcons true zero, false) ;
  | pair v' false := (Vcons false v', false) }.

Instance bits_succ_be_overflow {t : nat} {b : bits t} {c : bits t} : 
  provided bits_succ_be b = (c, true)
  have c = zero /\ b = full.
Proof with auto with *. intro.
  funelim (bits_succ_be b). 

    now depelim c.

    destruct_call @bits_succ_be. 
    destruct o ; simpdep... intuition (repeat subst ; auto).
Qed.

Lemma bits_succ_be_ne n (y : bits n) b' : bits_succ_be (binary_inverse y) = (b', true) -> y = zero.
Proof. intros. correct H. unfold full in H0; subst.
  apply (binary_inverse_is_constant _ _ H0).
Qed.

Instance bits_succ_be_correct {t : nat} {b : bits t} {c : bits t} : 
  provided bits_succ_be b = (c, false)
  have nat_of_binary_be c = S (nat_of_binary_be b).
Proof with auto with *. intro.
  Opaque bits_succ_be nat_of_binary_be.
  funelim (bits_succ_be b).
     
  destruct_call @bits_succ_be.
  destruct o; noconf Heq. 
  Transparent nat_of_binary_be. simpl.
  rewrite Hind. ring.
  reflexivity.

  case_eq_rew (bits_succ_be v) sv.
  destruct o; noconf Heq. correct sv. subst.
  clear. induction n; simpl; auto. 
  simp pow_of_2 zarith. rewrite <- plus_assoc. setoid_rewrite IHn.
  unfold full. simpl. ring. 
  
  simpl. auto.
Qed.

Lemma bits_succ_be_no_overflow_correct n (b : bits n) `{Have ([: b ] < pred (pow_of_2 n))} : 
  [: fst (bits_succ_be b) ] = S [: b ].
Proof.
  intros. 
  funelim (bits_succ_be b); try correct Heq; subst. 
  inversion H.
  rewrite nat_of_binary_full in H. unhave. 
  simp pow_of_2 in H. absurd_arith.
  
  rewrite Heq. omega.

  autorewrite with binary. 
  generalize (pow_of_2_pos n). omega.
  
  rewrite Heq. omega.
Qed.

(* Hint Extern 5 (Have _) => unhave; omega : typeclass_instances. *)

(** * Partial injection from [nat] to unsigned. *)

Equations(nocomp) binary_of_nat_be (t : nat) (c : nat) : option (bits t) :=
binary_of_nat_be t O := Some zero ;
binary_of_nat_be t (S m) <= binary_of_nat_be t m => {
  | None := None;
  | Some b <= bits_succ_be b => {
    | pair sb true := None;
    | pair sb false := Some sb }
}.

Global Transparent bits_succ_be binary_of_nat_be.

Eval compute in (binary_of_nat_be 8 1).
Eval compute in (binary_of_nat_be 8 255).

Ltac simpbin := simpdep; autorewrite with binary in *.
Opaque binary_of_nat_be bits_succ_be.

Instance nat_of_binary_binary_of_nat_inverse n (t : nat) (b : bits t) : 
  provided binary_of_nat_be t n = Some b
  have nat_of_binary_be b = n.
Proof with simpbin; auto. intro.
  funelim (binary_of_nat_be t n).
  
  now simpbin. 

  specialize (Hind _ Heq0).
  rewrite <- Hind. apply bits_succ_be_correct in Heq. rewrite Heq. reflexivity.
Qed.

Hint Rewrite nat_of_binary_binary_of_nat_inverse using solve [ auto ] : binary.
Ltac funelim_call f := on_call f funelim.

(** * Zero extension *)

Program Definition zx_be {t t'} `{Have (t' >= t)} (c : bits t) : bits t' :=
  vector_append (n:=t' - t) (m:=t) zero c.

  Next Obligation.  
    unfold Have in *. omega.
  Qed.

Lemma nat_of_zx_zero {m n} (c : bits m) : [: vector_append (@zero n) c ] = [:c].
Proof. intros. unfold zero. induction n; simp vector_append. Qed.

Lemma zx_be_correct {t t'} `{Have (t' >= t)} (c : bits t) : [: zx_be c ] = [:c].
Proof. intros. unfold zx_be. simpbin. omega. Qed.

Hint Rewrite @nat_of_zx_zero @zx_be_correct : binary.

(** * Addition *)

Equations(nocomp) binary_plus_be_aux {n} (b b' : bit) (r : bits n * overflow) : bits (S n) * overflow :=
binary_plus_be_aux n b b' (pair rest carry) <= add_bits b b' carry => {
  | pair bit carry := (Vcons bit rest, carry) }. 

Definition binary_plus_be {n} (x y : bits n) : bits n * overflow :=
  vfold_right2 (A:=fun n => (bits n * overflow)%type) 
    (@binary_plus_be_aux) (Vnil, false) x y.

Instance: Have (pow_of_2 n > 0).
Proof. reduce_goal. induction n ; simp pow_of_2 ; try omega. Qed.

Opaque vfold_right2.

Instance binary_plus_be_correct_full n (t t' : bits n) : forall tt' o, 
  provided binary_plus_be t t' = (tt', o)
  have
    let add' := nat_of_binary_be t + nat_of_binary_be t' in
      if o then add' >= pow_of_2 n /\
        nat_of_binary_be tt' = add' - pow_of_2 n
      else nat_of_binary_be tt' = add'.
Proof. intros. do 2 red.
  unfold binary_plus_be. funelim_call @vfold_right2.
  destruct_call_eq @vfold_right2 vfoldvv0. simpdep.
  funelim_call @binary_plus_be_aux.
  Opaque binary_plus_be_aux add_bits vfold_right2. clear vfoldvv0.
  destruct o0; funelim_call add_bits; simp add_bits pow_of_2;
    try rewrite H1; try split ; try omega.
Qed.

Lemma binary_plus_be_correct n (t t' : bits n) tt' :
  provided binary_plus_be t t' = (tt', false)
  have [: tt' ] = [: t ] + [: t' ].
Proof.
  intros. intro. apply (binary_plus_be_correct_full _ _ _ _ _ H).
Qed.

Lemma bits_succ_vector_append_0 : Π (n : nat) (v : vector bit n),
  bits_succ_be (vector_append_one v 0%bin) =
  (vector_append_one v 1%bin, 0%bin).
Proof. intros.
  Opaque vector_append_one bits_succ_be. 
  funelim (vector_append_one v false).
    simp bits_succ_be.

    destruct a0; simp bits_succ_be; 
    rewrite H; reflexivity.
Qed.

Hint Rewrite bits_succ_vector_append_0 : binary.

Open Local Scope vect_scope.  
Open Local Scope bin_scope.  

Equations(nocomp) binary_minus_be_carry {n : nat} (x y : bits n) (carry : bit) : bits n * overflow :=
binary_minus_be_carry O Vnil Vnil c := (Vnil, c) ;

binary_minus_be_carry (S n) (Vcons true n tlx) (Vcons true n tly) c 
  <= binary_minus_be_carry tlx tly c => { 
    | pair min' carry := (Vcons 0 min', carry) } ;

binary_minus_be_carry (S n) (Vcons false n tlx) (Vcons false n tly) c 
  <= binary_minus_be_carry tlx tly c => { 
    | pair min' carry := (Vcons 0 min', carry) } ;


(* (b(n-1) * 2^n-1 + ... + b0) - (2^n + b'(n-1) 2^n-1 + ... + b'0 + c) =
   ((2^n - 1) - (b(n-1) * 2^n-1 + ... + b0)) + 1 - c + b'(n-1) 2^n-1 + ... + b'0) *)
binary_minus_be_carry (S n) (Vcons false n tlx) (Vcons true n tly) true
  <= binary_plus_be (binary_inverse tlx) tly => {
    | pair plus overflow := ((overflow |:| plus), 1) } ;

binary_minus_be_carry (S n) (Vcons false n tlx) (Vcons true n tly) false
  <= bits_succ_be (binary_inverse tlx) => {
    | pair plus true := (* [tlx] must have been 0 *) (1 |:| tly, 1);
    | pair plus false <= binary_plus_be plus tly => {
      | pair plus' overflow := (overflow |:| plus', 1)
    }
  } ;

(* (2^n + b(n-1) * 2^n-1 + ... + b0) - (b'(n-1) 2^n-1 + ... + b'0 + c) =
   (2^n - 1) - (b'(n-1) 2^(n-1) + ... + b'0) + 1 - c + (bn * 2^(n-1) + ... + b0) *)

binary_minus_be_carry (S n) (Vcons true n tlx) (Vcons false n tly) true
  <= binary_plus_be (binary_inverse tly) tlx => {
    | pair plus overflow := ((overflow |:| plus), 0) } ;

binary_minus_be_carry (S n) (Vcons true n tlx) (Vcons false n tly) false
  <= bits_succ_be (binary_inverse tly) => {
    | pair plus true := (* [tly] must have been 0 *) (1 |:| tlx, 0);
    | pair plus false <= binary_plus_be plus tlx => {
      | pair plus' overflow := (overflow |:| plus', 0)
    }
  }.

Global Transparent binary_minus_be_carry binary_plus_be bits_succ_be constant_vector vfold_right2 vector_append_one.

Definition binary_minus_be {n} (x y : bits n) : bits n * borrow :=
  binary_minus_be_carry x y false.

Lemma nat_of_binary_bound_eq {n} (x : bits n) : nat_of_binary_be x - pow_of_2 n = 0%nat.
Proof. intros. generalize (nat_of_binary_bound x). omega. Qed.

Hint Rewrite @nat_of_binary_bound_eq : binary.

Lemma minus_plus_lt x y z : x > y -> (x - y + z) = (x + z) - y.
Proof. intros. omega. Qed.
  
Lemma minus_plus_lt2 x y z : x > y -> ((x + z) - y) - x = z - y.
Proof. intros. omega. Qed.

Require Import ROmega.

Instance binary_minus_carry_correct {n} (x y t : bits n) c : 
  provided binary_minus_be_carry x y c = (t, false)
  have [: t ] = [: x ] - (nat_of_bool c + [: y ]).
Proof.
  intros. intro. revert t H. funelim (binary_minus_be_carry x y c).

  rewrite (Hind _ Heq).
  omega.

  apply (binary_plus_be_correct_full _) in Heq.
  rewrite ! nat_of_binary_inverse in Heq.
  generalize (nat_of_binary_bound v0). generalize (nat_of_binary_bound v). intros.
  destruct b; [destruct Heq as [bound Heq]|]; rewrite Heq; clear Heq;
  ring_simplify; try abstract omega.
  
  apply bits_succ_be_overflow in Heq.
  destruct Heq. subst. apply binary_inverse_is_constant in H0. rewrite H0.
  simpbin. omega.

  apply (binary_plus_be_correct_full _) in Heq.
  apply bits_succ_be_correct in Heq0. rewrite Heq0 in *; clear Heq0.
  rewrite ! nat_of_binary_inverse in Heq.
  generalize (nat_of_binary_bound v0). generalize (nat_of_binary_bound v). intros.
  destruct b ; [destruct Heq as [bound Heq]|]; rewrite Heq in *; clear Heq;
  ring_simplify; generalize (pow_of_2_pos n); intros; try abstract omega.

  auto.
Qed.

Instance binary_minus_correct {n} (x y t : bits n) : 
  provided binary_minus_be x y = (t, false)
  have [: x ] - [: y ] = [: t ].
Proof. intros. intro. pose (binary_minus_carry_correct x y t false H). auto. Qed.

Lemma binary_minus_be_zero n (t : bits n) : binary_minus_be t zero = (t, 0).
Proof. unfold binary_minus_be. Opaque binary_minus_be_carry bits_succ_be zero.
  funelim_call @binary_minus_be_carry. Transparent zero. unfold zero in *. 
  simpdep.
  apply (binary_plus_be_correct_full _) in Heq.
  apply bits_succ_be_correct in Heq0. rewrite !nat_of_binary_inverse in Heq0.
  rewrite Heq0 in *; clear Heq0. rewrite nat_of_binary_zero in Heq.
  destruct b; [destruct Heq as [bound Heq]|]. ring_simplify in Heq. 
  assert([: v2] = [: v]). rewrite Heq. generalize (nat_of_binary_bound v). omega.
  inject H. reflexivity. simpl in Heq.
  generalize (nat_of_binary_bound v2); intros; exfalso; omega.
  unfold zero in *. simpdep. 
  rewrite Heq in Hind. noconf Hind.
Qed.

Lemma binary_minus_be_one_overflow n (t : bits (S n)) b : binary_minus_be t one = (b, 1) -> t = zero.
Proof. unfold binary_minus_be. Opaque binary_minus_be_carry bits_succ_be.
  revert b.
  funelim_call @binary_minus_be_carry; try
    (assert(v0 = zero) by (induction n; noconf H);
      subst v0; destruct n; noconf H; depelim v ; reflexivity).

  assert(v0 = zero) by (induction n; noconf H);
    subst v0; setoid_rewrite (binary_minus_be_zero n v) in Heq; noconf Heq.

  destruct n; noconf H; simpdep. rewrite (Hind _ Heq).
  reflexivity.
Qed.

Lemma nat_of_binary_one_is_one n (t : bits (S n)) : [: t ] = 1%nat -> t = one.
Proof. 
  funelim [: t].
  destruct a. simpl in *.
  depelim n; try noconf H0. rewrite <- (nat_of_binary_zero 0) in H0. inject H0. reflexivity.
  simp pow_of_2 in H0. generalize (pow_of_2_pos n). absurd_arith.
  depelim v; try noconf H0. simplify_IH_hyps. rewrite (H H0). reflexivity.
Qed.
  
Open Local Scope bin_scope.

Lemma nat_of_binary_be_zero n (t : bits n) : [: t ] = 0%nat -> t = zero.
Proof. funelim [: t]. destruct a. generalize (pow_of_2_pos n); absurd_arith.
  rewrite <- (nat_of_binary_zero n) in H0. inject H0. reflexivity.
Qed.

Lemma bits_succ_be_zero n : bits_succ_be (@zero (S n)) = (one, 0).
Proof. 
  funelim (bits_succ_be (@zero (S n))).
  destruct n. simp bits_succ_be in Heq. 
  apply bits_succ_be_overflow in Heq. destruct Heq ; subst.
  simplify_IH_hyps. noconf H0.
  destruct n. simp bits_succ_be in Heq. noconf Heq.
  simplify_IH_hyps. apply bits_succ_be_correct in Hind. apply bits_succ_be_correct in Heq. 
  f_equal. apply nat_of_binary_be_inj. simpl. rewrite Heq.
  simpl. setoid_rewrite <- Hind. reflexivity.
Qed.

Hint Resolve nat_of_binary_zero : binary.

Lemma binary_of_nat_be_ok (t : nat) (c : nat) : c < pow_of_2 t -> 
  exists b, binary_of_nat_be t c = Some b /\ [: b ] = c.
Proof.
  intros. funelim_call binary_of_nat_be. 

    exists (@zero t). split ; auto with binary.

    destruct Hind. omega.
    destruct H0. congruence.

    correct Heq. subst.
    apply (nat_of_binary_binary_of_nat_inverse n t full) in Heq0. subst.
    autorewrite with binary in H. absurd_arith.

    apply bits_succ_be_correct in Heq.
    correct Heq0. subst. exists v0; split; auto.
Qed.

Lemma binary_of_nat_inverse {n} (t : bits n) : binary_of_nat_be n [: t ] = Some t.
Proof.
  generalize (nat_of_binary_bound t).
  intros. destruct (binary_of_nat_be_ok _ _ H) as (res & H' & H0).
  rewrite H'. inject H0. reflexivity.
Qed.

Hint Rewrite @binary_of_nat_inverse : binary.

Equations(nocomp) binary_mult_be {m n} (x : bits m) (y : bits n) : bits n * overflow :=
binary_mult_be O n Vnil y := (zero, false) ;
binary_mult_be (S m) n (Vcons false m tlx) y := binary_mult_be tlx y ;
binary_mult_be (S m) n (Vcons true m tlx) y <= 
  binary_shiftl_n y m => 
  { | pair y' true := (y, true) ;
    | pair y' false <= binary_mult_be tlx y => 
      { | pair y'' true := (y, true) ;
        | pair y'' false := binary_plus_be y' y''
      }
  }.

Opaque binary_shiftl.
Transparent nat_of_binary_be. 

Instance binary_shiftl_be_correct {o} {n} (t : bits n) t' : 
  provided binary_shiftl t = (t', o)
  have if o then pow_of_2 n + [: t' ] = 2 * [: t ]
       else [: t' ] = 2 * [: t ].
Proof. intros. intro. funelim (binary_shiftl t).
  case_eq_rew (binary_shiftl v) shiftv; simplify_IH_hyps. noconf H0.
  simpl. destruct o; destruct o0 ; simp pow_of_2 ; try omega.
Qed.

Transparent binary_shiftl.

Instance binary_shiftl_n_be_correct {n} (t : bits n) m t' : 
  provided binary_shiftl_n t m = (t', false)
  have [: t' ] = pow_of_2 m * [: t ].
Proof. intros. intro. funelim (binary_shiftl_n t m).
  rewrite (H _ H0). correct Heq. simpl in *.
  rewrite Heq. simp pow_of_2. ring.
Qed.

Hint Unfold noConfusion_nat : equations.

Opaque binary_mult_be.
Instance binary_mult_correct {n m} (x : bits m) (y : bits n) z : 
  provided binary_mult_be x y = (z, false)
  have [: x ] * [: y ] = [: z ].
Proof. intro. funelim (binary_mult_be x y). 

  auto with binary.

  correct H; correct Heq0.
  rewrite H, Heq0, <- (Hind _ Heq) ; auto.
  ring.
Qed.

Transparent binary_mult_be.

Equations(nocomp) binary_mult_full_be {n m} (x : bits n) (y : bits m) : bits (n + m) :=
binary_mult_full_be O m Vnil y := zero ;

binary_mult_full_be (S n) m (Vcons false n tlx) y :=
   zx_be (binary_mult_full_be tlx y) ;

binary_mult_full_be (S n) m (Vcons true n tlx) y <= 
  binary_plus_be (binary_shiftl_n_full y n) (binary_mult_full_be tlx y) => {
    | pair mult overflow := Vcons overflow mult }.

Opaque binary_shiftl_full.

Lemma binary_shiftl_full_be_correct {n} (t : bits n) : 
  [: binary_shiftl_full t ] = 2 * [: t ].
Proof. depind t; simp binary_shiftl_full.
  destruct a; simpl. rewrite IHt. simp pow_of_2. omega.

  assumption.
Qed.
Hint Rewrite @binary_shiftl_full_be_correct : binary.

Lemma binary_shiftl_full_n_be_correct {n} (t : bits n) m :
  [: binary_shiftl_n_full t m ] = pow_of_2 m * [: t ].
Proof. funelim (binary_shiftl_n_full t m). 
  autorewrite with binary pow_of_2 zarith. rewrite H. ring.
Qed.
Hint Rewrite @binary_shiftl_full_n_be_correct : binary.
  
Transparent binary_shiftl.

Opaque binary_mult_full_be.

Ltac autorewrite_local := repeat
  match goal with 
    | [ H : _ = _ |- _ ] => rewrite H in *
    | [ H : context [ _ = _ ] |- _ ] => rewrite H in *
  end.

Tactic Notation "rew" "*" := autorewrite with binary in *; autorewrite_local.

Ltac arith := 
  try ring_simplify ; [ ring || omega || auto with arith ].

Lemma binary_mult_full_be_correct {n m} (x : bits m) (y : bits n) : 
  [: binary_mult_full_be x y ] = [: x ] * [: y ].
Proof.
  funelim (binary_mult_full_be x y); auto with binary.

  correct Heq. rew*.
  destruct b; [destruct Heq|]; rew*; arith.
Qed.

Hint Rewrite @binary_mult_full_be_correct : binary.

Program Instance bvec_binary_be n : Binary BigEndian (bits (S n)) := {
  bin_size t := S n ;
  
  bin_of_nat := binary_of_nat_be (S n);
  nat_of_bin := nat_of_binary_be;

  bin_succ := bits_succ_be ;

  bin_plus := binary_plus_be ;
  bin_minus := binary_minus_be ;
  bin_mult := binary_mult_be
}.

  Next Obligation. now apply nat_of_binary_binary_of_nat_inverse. Qed.
  Next Obligation. apply binary_of_nat_inverse. Qed.
  Next Obligation. now erewrite bits_succ_be_correct. Qed.
  Next Obligation. now apply binary_plus_be_correct. Qed.
  Next Obligation. symmetry. now apply binary_minus_correct. Qed.
  Next Obligation. symmetry. now apply binary_mult_correct. Qed.

Global Transparent vfold_right2 binary_minus_be bits_succ_be nat_of_binary_be.

(** * Orders *)

Equations(nocomp) binary_be_le {n} (x y : vector bit n) : bool :=
binary_be_le ?(O) Vnil Vnil := true ;
binary_be_le ?(S n) (Vcons a n x) (Vcons a' n y) <= xorb a a' => {
binary_be_le ?(S n) (Vcons a n x) (Vcons a' n y) true := a' ;
binary_be_le ?(S n) (Vcons a n x) (Vcons a' n y) false := binary_be_le x y }.

Instance: BoolReflexive (@binary_be_le n).
Proof. reduce_goal. funelim (binary_be_le x x); intros ; auto.
  destruct a ; simpl ; auto.
Qed.

Instance: BoolTransitive (@binary_be_le n).
Proof. reduce_goal. funelim (binary_be_le x y).
  destruct a ; noconf Heq. depelim z. 
  destruct a ; simp binary_be_le in *. noconf H0.

  depelim z.
  destruct a; destruct a0; noconf Heq; destruct a1; simp binary_be_le in *.
Qed.

Lemma binary_be_le_correct {n} (x y : bits n) : if binary_be_le x y then [: x ] <= [: y ]
  else [: y ] < [: x ].
Proof. funelim (binary_be_le x y); auto.
  destruct a0; destruct a; noconf Heq; simpl.
  pose (nat_of_binary_bound v) ; omega.
  pose (nat_of_binary_bound v0) ; omega.

  destruct a0; destruct a; noconf Heq.
  destruct_call @binary_be_le; omega.
Qed.

Hint Extern 0 => omega : omega.

Lemma binary_be_le_view_true {n} (x y : bits n) : binary_be_le x y = true <-> [: x ] <= [: y ]. 
Proof. split ; intros. generalize (binary_be_le_correct x y). rewrite H. auto.
  funelim (binary_be_le x y); auto.

  destruct a0; destruct a; noconf Heq; simpl.
  pose (nat_of_binary_bound v0) ; exfalso; omega.

  destruct a0; destruct a; noconf Heq. apply H. omega.
Qed.

Lemma binary_be_le_view_false {n} (x y : bits n) : binary_be_le x y = false <-> [: y ] < [: x ]. 
Proof. intros. split; intros. generalize (binary_be_le_correct x y). rewrite H. auto. 
  funelim (binary_be_le x y); auto.

  inversion H.
  destruct a0; destruct a; noconf Heq; simpl.
  pose (nat_of_binary_bound v); exfalso; omega.

  destruct a0; destruct a; noconf Heq. apply H; omega.
Qed.

Inductive binary_be_le_view {n} (x y : bits n) : bool -> Prop :=
| binary_be_le_view_le : [: x ] <= [: y ] -> binary_be_le_view x y true
| binary_be_le_view_gt : [: y ] < [: x ] -> binary_be_le_view x y false.

Lemma binary_be_le_is_view {n} (x y : bits n) : binary_be_le_view x y (binary_be_le x y).
Proof. case_eq (binary_be_le x y); intros. 
  constructor 1. apply -> @binary_be_le_view_true; assumption.
  constructor 2. apply -> @binary_be_le_view_false; assumption.
Qed.

Equations(nocomp) binary_be_lt {n} (x y : bits n) : bool :=
binary_be_lt n x y <= bits_succ_be x => {
  | pair x' true := false ;
  | pair x' _ := binary_be_le x' y }.

Instance: BoolIrreflexive (@binary_be_lt n).
Proof. reduce_goal. funelim_call @binary_be_lt. 
  apply bits_succ_be_correct in Heq.
  rewrite binary_be_le_view_false.
  rewrite Heq. omega.
Qed.
