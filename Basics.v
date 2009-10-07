Require Export Arith Program Equations Have Morphisms EquivDec.
Require Export Relation_Definitions.


Ltac case_eq_rew :=
  fun x => generalize (@eq_refl _ x); pattern x at - 1 in |- *; case x ; intros until 1 ;
    on_last_hyp ltac:(fun H => try rewrite H in *).

Ltac destruct_call_eq f := 
  match goal with
    | |- ?T => on_application f ltac:(fun app => case_eq_rew app) T
    | H : ?T |- _ => on_application f ltac:(fun app => case_eq_rew app) T
  end.

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

Hint Extern 4 => discriminates : core.

Notation " 'convertible' x y " := (eq_refl : x = y) (at level 0, x at next level, y at next level).

Ltac absurd_arith := intros ; elimtype False ; omega.

Ltac simpdep := reverse ; simplify_dep_elim ; simplify_IH_hyps.

Lemma bool_eq_refl b : bool_eq b b = true.
Proof. destruct b ; reflexivity. Qed.

Definition ltb (x y : nat) := leb (S x) y.

Class StrictOrder `(Equivalence A eqA) (ordA : relation A) :=
  { StrictOrder_trans :> Transitive ordA ;
    StrictOrder_irrefl :> Irreflexive ordA }.    

Inductive comparison `{E : Equivalence A eqA} ordA `{O : StrictOrder A eqA ordA} (x y : A) : Type :=
| compare_LT : ordA x y -> comparison ordA x y
| compare_EQ : eqA x y -> comparison ordA x y 
| compare_GT : ordA y x -> comparison ordA x y.

Class CompareDec `(E : Equivalence A eqA) `(O : StrictOrder A eqA ordA) :=
  compare_dec : Π x y : A, comparison ordA x y.

Instance lt_strict_order : ! StrictOrder nat eq lt.
Proof. constructor ; firstorder. Qed.

Instance nat_compare_dec : ! CompareDec nat eq lt.
Proof.
  intros x y. destruct (lt_eq_lt_dec x y) as [ [ lt | eq ] | gt ].
  now apply compare_LT.
  now apply compare_EQ.
  now apply compare_GT.
Defined.


Instance: Proper (le --> le ++> impl) lt.
Proof. reduce_goal. unfold flip in *. omega. Qed.

Instance: Proper (le --> le ++> impl) le.
Proof. reduce_goal. unfold flip in *. omega. Qed.

Instance: Proper (le --> lt ++> impl) le.
Proof. reduce_goal. unfold flip in *. omega. Qed.

Instance: subrelation lt le.
Proof. reduce_goal. omega. Qed.

Instance: Proper (lt --> lt ++> impl) lt.
Proof. reduce_goal. unfold flip in *. omega. Qed.

Instance: Proper (le ++> le ++> le) mult.
Proof. reduce_goal. unfold flip in *. now apply mult_le_compat. Qed.

Program Instance: Reflexive le.
Program Instance: Transitive le := le_trans.
Program Instance: PreOrder le.

Lemma mult_lt_compat : Π n m p q : nat, n < m -> p <= q -> q > 0 -> n * p < m * q.
Proof. intros. induction H. simpl. induction H0 ; try omega. 
  rewrite H0. ring_simplify. omega.
  ring_simplify. omega.
Qed.

Program Fixpoint euclid (n : nat) (m : nat) `{Have (m > 0)} {wf lt n} : nat * nat :=
  match ltb n m with
    | true => (0, n)
    | false => let '(q, r) := euclid (n - m) m return nat * nat in
      (S q, r)
  end.

  Next Obligation.
    unfold ltb in *.
    symmetry in Heq_anonymous.
    apply leb_complete_conv in Heq_anonymous. unfold Have in *. omega.
  Qed.

  Next Obligation. auto with *. Defined.

Ltac ind_on f := 
  match goal with
    |- context [ f ?x ] => let term := fresh "term" in 
      pattern_tele x term ; pattern_call (f term) ; subst term ;
        apply Fix_sub_rect ; fold f ; unfold MR in * ; simpl ; intros
  end.

Lemma euclid_spec n m `{Have (m > 0)} : forall q r, euclid n m = (q, r) -> n = m * q + r /\ r < m.
Proof.
  intros n m H. unfold euclid. ind_on euclid_func. 
  admit.

  destruct x as [ n' [ m' Hm' ] ]; simpl in *.
  case_eq (ltb n' m') ; intro Hlt ; rewrite Hlt in *. 
  program_simpl. split ; try omega. apply leb_complete in Hlt. omega.
  match type of H1 with
    context [ euclid_func ?t ] => specialize (H0 t)
  end.
  simpl in H0.
  destruct_call euclid_func.
  program_simpl.
  apply leb_complete_conv in Hlt.
  assert(n' - m' < n') by (unfold Have in * ; omega).
  specialize (H0 H1).
  simplify_IH_hyps. replace (m' * S n0 + r) with (m' + (m' * n0 + r)) by ring.
  destruct H0.
  rewrite <- H0.
  rewrite <- le_plus_minus. split. reflexivity. auto.
  omega.
Defined.

Lemma euclid_unfold n m `{Have (m > 0)} : euclid n m = 
  if ltb n m then (0, n) else let '(q, r) := euclid (n - m) m in (S q, r).
Proof.
  intros. unfold euclid. ind_on euclid_func. admit.
  destruct x as [ n' [ m' Hm' ] ]; simpl in *.
  destruct_call ltb. reflexivity.
  reflexivity.
Qed.

Eval compute in (euclid 66 8).

Definition quotient_nat n m `{Have (m > 0)} : nat := fst (euclid n m).
Definition modulo_nat n m `{Have (m > 0)} : nat := snd (euclid n m).

Lemma quotient_cancel : forall x y `{Have (y > 0)}, modulo_nat x y = 0 -> quotient_nat x y * y = x.
Proof. intros x y H. unfold modulo_nat, quotient_nat in *. 
  generalize (euclid_spec x y). destruct_call euclid ; intros Heucl ; simplify_IH_hyps.
  destruct Heucl.
  simpl in *. intros. subst. ring.
Defined.

Lemma euclid_0 y `{Have (y > 0)} : euclid 0 y = (0, 0).
Proof. intros.
  generalize (euclid_spec 0 y).
  destruct_call euclid ; intros ; simplify_IH_hyps. destruct H0.
  induction n. ring_simplify in H0. subst ; reflexivity.
  unfold Have in *.
  destruct y. inversion H.
  ring_simplify in H0.
  replace (y * n + y + n + n0 + 1) with (S (y * n + y + n + n0)) in H0 by ring.
  discriminate.
Qed.  

Ltac destruct_equiv x y := let Heq := fresh "H" x y in
  destruct (equiv_dec x y) as [ Heq | Heq ] ; [ try (red in Heq ; subst x) | ].

Lemma modusponens: forall (P Q: Type), P -> (P -> Q) -> Q.
Proof. auto. Qed.

Ltac exploit x :=
    refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _) _)
 || refine (modusponens _ _ (x _ _) _)
 || refine (modusponens _ _ (x _) _).

Tactic Notation "omega" "*" := unfold Have in * ; omega.
Ltac unhave := unfold Have in *.

Lemma quotient_gt_1 x y `{Have (y > 0)} : x > y -> modulo_nat x y = 0 -> quotient_nat x y > 1.
Proof. intros x y H. unfold modulo_nat, quotient_nat. generalize (euclid_spec x y).
  destruct_call euclid ; program_simpl. simplify_IH_hyps. destruct H0. subst x. ring_simplify in H1.
  unhave. repeat (destruct n; try omega).
Qed.
Require Import SetoidTactics.

Lemma plus_minus_le x y : x + y - y = x.
Proof. induction y.
  rewrite <- minus_n_O. auto.
  replace (x + S y) with (S (x + y)) by ring.
  simpl. apply IHy.
Qed.

Lemma euclid_mult y `{Have (y > 0)} n : euclid (n * y) y = (n, 0).
Proof.
  induction n. 
    now rewrite euclid_0.

    rewrite euclid_unfold.
    case_eq (ltb (S n * y) y).
    intros Hxy; apply leb_complete in Hxy. 
    replace (S (S n * y)) with (S y + n * y) in Hxy by ring.
    elimtype False. assert(S y <= S y + n * y) by auto with arith. rewrite <- H0 in Hxy.
    elim (le_Sn_n _ Hxy).

    intros. apply leb_complete_conv in H0. 
    replace (S n * y - y) with (n * y). rewrite IHn. reflexivity.
    simpl. rewrite plus_comm. rewrite plus_minus_le. reflexivity.
Qed.

Lemma modulo_cancel : forall n y `{Have (y > 0)}, modulo_nat (n * y) y = 0.
Proof. intros n y H. unfold modulo_nat in *. rewrite euclid_mult. reflexivity. Qed.

Require Import BinPos Pnat.

Equations(nocomp) pow_of_2_positive (n : nat) : positive :=
pow_of_2_positive O := 1%positive ;
pow_of_2_positive (S n) := ((pow_of_2_positive n)~0)%positive.

Lemma pow_of_2_positive_Sn n : pow_of_2_positive (S n) = Pmult (pow_of_2_positive n) 2.
Proof. intros. simp pow_of_2_positive. rewrite Pmult_comm. simpl.
  reflexivity.
Qed.

(* Equations(nocomp) pow_of_2 (n : nat) : nat := *)
(* pow_of_2 O := 1 ; *)
(* pow_of_2 (S n) := 2 * pow_of_2 n. *)

Equations(nocomp) div2_rest (n : nat) : nat * bool :=
div2_rest O := (0, false) ;
div2_rest (S O) := (0, true) ;
div2_rest (S (S n)) := let (n', rest) := (div2_rest n) in (S n', rest).

Equations(nocomp) div2 (n : nat) : nat :=
div2 O := 0 ;
div2 (S O) := 0 ;
div2 (S (S n)) := S (div2 n).

Global Transparent pow_of_2_positive.

Definition pow_of_2 (n : nat) := nat_of_P (pow_of_2_positive n).

Lemma pow_of_2_nat_pos n : pow_of_2 n > 0.
Proof. intros. unfold pow_of_2. auto using lt_O_nat_of_P. Qed.
Hint Immediate pow_of_2_nat_pos.

Require Import ZArith.
Open Local Scope Z_scope.

Definition pow_of_2_Z (n : nat) := Zpos (pow_of_2_positive n).

Lemma pow_of_2_nat_Z n : Z_of_nat (pow_of_2 n) = pow_of_2_Z n.
Proof. intros. unfold pow_of_2_Z. unfold pow_of_2. rewrite Zpos_eq_Z_of_nat_o_nat_of_P. 
  reflexivity.
Qed.

Lemma pow_of_2_Z_pos n : pow_of_2_Z n > 0.
Proof. intros. unfold pow_of_2_Z. intros. apply Zgt_pos_0. Qed.

Lemma pow_of_2_positive_plus n m : 
  (pow_of_2_positive (n + m) = pow_of_2_positive n * pow_of_2_positive m)%positive.
Proof. induction n ; simpl ; intros ; auto.
  rewrite IHn. reflexivity.
Qed.

Lemma pow_of_2_nat_positive n : pow_of_2 n = nat_of_P (pow_of_2_positive n).
Proof. reflexivity. Qed.

Hint Rewrite pow_of_2_positive_Sn pow_of_2_positive_plus : pow_of_2.
Hint Rewrite pow_of_2_nat_positive : nat_of_P.

Hint Resolve lt_O_nat_of_P : nat_of_P.

Hint Rewrite nat_of_P_succ_morphism nat_of_P_plus_carry_morphism 
  Pmult_nat_l_plus_morphism nat_of_P_plus_morphism Pmult_nat_r_plus_morphism
  nat_of_P_mult_morphism Pmult_nat_mult_permute Pmult_nat_2_mult_2_permute 
  Pmult_nat_4_mult_2_permute nat_of_P_xH nat_of_P_xO nat_of_P_xI
  nat_of_P_o_P_of_succ_nat_eq_succ P_of_succ_nat_o_nat_of_P_eq_succ
  pred_o_P_of_succ_nat_o_nat_of_P_eq_id : nat_of_P.

Hint Rewrite pow_of_2_nat_positive : nat_of_P_inv.

Hint Rewrite <- nat_of_P_succ_morphism nat_of_P_plus_carry_morphism 
  Pmult_nat_l_plus_morphism nat_of_P_plus_morphism Pmult_nat_r_plus_morphism
  nat_of_P_mult_morphism Pmult_nat_mult_permute Pmult_nat_2_mult_2_permute 
  Pmult_nat_4_mult_2_permute nat_of_P_xH nat_of_P_xO nat_of_P_xI
  P_of_succ_nat_o_nat_of_P_eq_succ 
  pred_o_P_of_succ_nat_o_nat_of_P_eq_id : nat_of_P_inv.

Hint Rewrite nat_of_P_minus_morphism using solve [ auto ] : nat_of_P.

Lemma pow_of_2_plus n m : (pow_of_2 (n + m) = pow_of_2 n * pow_of_2 m)%nat.
Proof. unfold pow_of_2. intros. autorewrite with nat_of_P pow_of_2. reflexivity. Qed.

Hint Rewrite inj_0 inj_S inj_plus inj_mult inj_min inj_max : Z_of_nat. 
Hint Rewrite <- inj_eq_iff inj_le_iff inj_lt_iff inj_ge_iff Zpos_eq_Z_of_nat_o_nat_of_P
  Zpos_P_of_succ_nat : Z_of_nat.

Hint Resolve inj_eq inj_neq inj_le inj_gt inj_ge inj_lt : Z_of_nat.

Lemma pow_of_2_Z_plus n m : pow_of_2_Z (n + m) = pow_of_2_Z n * pow_of_2_Z m.
Proof. unfold pow_of_2_Z. intros. autorewrite with Z_of_nat nat_of_P_inv pow_of_2.
  reflexivity. 
Qed.

Lemma pow_of_2_0 : (pow_of_2 0 = 1)%nat.
Proof. 
  intros. simp pow_of_2 nat_of_P. 
Qed.

Lemma pow_of_2_Sn n : (pow_of_2 (S n) = pow_of_2 n + pow_of_2 n)%nat.
Proof. intros. simp pow_of_2 nat_of_P. ring. Qed.

Hint Rewrite pow_of_2_plus pow_of_2_0 pow_of_2_Sn : pow_of_2.

Lemma pow_of_2_pos n : (pow_of_2 n > 0)%nat.
Proof. intros. simp pow_of_2 nat_of_P. auto with nat_of_P. Qed.

Hint Resolve pow_of_2_pos : pow_of_2.