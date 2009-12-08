Require Export Arith Program Equations.Equations Have Morphisms EquivDec.
Require Export Relation_Definitions.

Global Set Automatic Introduction.

Global Generalizable All Variables.

Class Injective {A B} (f : A -> B) :=
  injective : forall x y, f x = f y -> x = y.

Ltac inject H := first [ apply injective in H | simpl in H; apply injective in H | noconf H ] ; subst.

Ltac case_eq_rew :=
  fun x H => generalize (@eq_refl _ x); pattern x at - 1 in |- *; case x ; intros until 1 ;
    on_last_hyp ltac:(fun id => rename id into H ; try rewrite H in *).

Ltac destruct_call_eq f id := 
  match goal with
    | |- ?T => on_application f ltac:(fun app => case_eq_rew app id) T
    | H : ?T |- _ => on_application f ltac:(fun app => case_eq_rew app id) T
  end.

Hint Extern 4 => discriminates : exfalso.

Notation " 'convertible' x y " := (eq_refl : x = y) (at level 0, x at next level, y at next level).

Ltac absurd_arith := intros ; elimtype False ; omega.

Ltac simpdep := program_simpl; reverse; simpl; simplify_dep_elim ; simplify_IH_hyps.

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

Class CompareDec `(O : StrictOrder A eqA ordA) :=
  compare_dec : Π x y : A, comparison ordA x y.

Instance lt_strict_order : ! StrictOrder nat eq lt. 

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

Lemma mult_lt_compat (n m p q : nat) : n < m -> p <= q -> q > 0 -> n * p < m * q.
Proof. intros. induction H. simpl. induction H0 ; try omega. 
  rewrite H0. ring_simplify. omega.
  ring_simplify. omega.
Qed.

Instance: WellFounded lt := lt_wf.

Ltac rec ::= rec_wf_eqns.

Equations euclid (n : nat) (m : nat) `{Have (m > 0)} : nat * nat :=
euclid n m H => rec n =>
euclid n m H <= dec (ltb n m) => {
  | left _ := (0, n) ;
  | right p <= euclid (n - m) m => {
    | pair q r := (S q, r) }
}.
  Next Obligation.
    unfold ltb in *.
    apply leb_complete_conv in p. unfold Have in *. apply euclid. omega.
  Defined.

  Next Obligation.
    rec n rn.
    unfold add_pattern. simp euclid.
    constructor.
    depelim_term (dec (ltb x m)). 
    constructor. 
    constructor. apply leb_complete_conv in e. apply rn. unfold Have in *. omega.
    depelim_term (euclid (x - m) m). autorewrite with euclid. constructor.
  Defined.

Transparent euclid.

Eval compute in (euclid 8 4).

Ltac ind_on f := 
  match goal with
    |- context [ f ?x ] => let term := fresh "term" in 
      pattern_tele x term ; pattern_call (f term) ; subst term ;
        apply Fix_sub_rect ; fold f ; unfold MR in * ; simpl ; intros
  end.

Ltac funelim f ::= funelim_tac f ltac:(fun f => simpl in *; simpdep).

Opaque euclid.

Lemma euclid_spec n m `{Have (m > 0)} : forall q r, euclid n m = (q, r) -> n = m * q + r /\ r < m.
Proof. funelim (euclid n m). clear Heq. apply leb_complete in e. split ; omega.

  clear Heq0. 
  specialize (Hind _ _ Heq). destruct Hind ; split ; auto.
  replace (m * S n0 + r) with (m + (m * n0 + r)) by ring.
  rewrite <- H0. apply leb_complete_conv in e. omega.
Qed.

Lemma euclid_unf n m `{Have (m > 0)} : euclid n m = 
  if ltb n m then (0, n) else let '(q, r) := euclid (n - m) m in (S q, r).
Proof. funelim (euclid n m). rewrite e. reflexivity.
  rewrite e, Heq. reflexivity.
Qed.
Transparent euclid.
Eval compute in (euclid 66 8).

Definition quotient_nat n m `{Have (m > 0)} : nat := fst (euclid n m).
Definition modulo_nat n m `{Have (m > 0)} : nat := snd (euclid n m).

Lemma quotient_cancel (x y : nat) `{Have (y > 0)} : modulo_nat x y = 0 -> quotient_nat x y * y = x.
Proof. unfold modulo_nat, quotient_nat in *. 
  generalize (euclid_spec x y). 
  destruct_call euclid ; intros Heucl ; simpdep. 
  destruct Heucl. subst. ring.
Defined.

Lemma euclid_0 y `{Have (y > 0)} : euclid 0 y = (0, 0).
Proof. funelim (euclid 0 y). 
  clear Heq0. apply leb_complete_conv in e. unfold Have in *. exfalso; omega.
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

Lemma quotient_gt_1 x y `{Have (y > 0)} : x > y -> modulo_nat x y = 0 -> quotient_nat x y > 1.
Proof. unfold modulo_nat, quotient_nat. generalize (euclid_spec x y).
  destruct_call euclid ; simpdep. destruct H0. subst x. ring_simplify in H1.
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

    simp euclid. destruct_call dec. simp euclid. 
    apply leb_complete in e. 
    ring_simplify in e. set(foo:=n * y) in e; exfalso; omega.
    
    rewrite euclid_helper_1_equation_2.
    replace (S n * y - y) with (n * y). rewrite IHn. simp euclid.
    auto with arith.
Qed.

Lemma modulo_cancel n y `{Have (y > 0)} : modulo_nat (n * y) y = 0.
Proof. unfold modulo_nat in *. rewrite euclid_mult. reflexivity. Qed.

Require Import BinPos Pnat.

Equations(nocomp) pow_of_2_positive (n : nat) : positive :=
pow_of_2_positive O := 1%positive ;
pow_of_2_positive (S n) := ((pow_of_2_positive n)~0)%positive.

Lemma pow_of_2_positive_Sn n : pow_of_2_positive (S n) = Pmult (pow_of_2_positive n) 2.
Proof. simp pow_of_2_positive. rewrite Pmult_comm. simpl.
  reflexivity.
Qed.

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
Proof. unfold pow_of_2_Z, pow_of_2. rewrite Zpos_eq_Z_of_nat_o_nat_of_P. 
  reflexivity.
Qed.

Lemma pow_of_2_Z_pos n : pow_of_2_Z n > 0.
Proof. unfold pow_of_2_Z. intros. apply Zgt_pos_0. Qed.

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

Hint Rewrite Psucc_o_double_minus_one_eq_xO
  Pdouble_minus_one_o_succ_eq_xI
  xO_succ_permute Ppred_succ : positive.
Hint Rewrite <- Pplus_one_succ_r Pplus_one_succ_l : positive.

Hint Rewrite pow_of_2_nat_positive : nat_of_P_inv.

Hint Rewrite <- nat_of_P_succ_morphism nat_of_P_plus_carry_morphism 
  Pmult_nat_l_plus_morphism nat_of_P_plus_morphism Pmult_nat_r_plus_morphism
  nat_of_P_mult_morphism Pmult_nat_mult_permute Pmult_nat_2_mult_2_permute 
  Pmult_nat_4_mult_2_permute 
  P_of_succ_nat_o_nat_of_P_eq_succ 
  pred_o_P_of_succ_nat_o_nat_of_P_eq_id : nat_of_P_inv.

Hint Rewrite nat_of_P_minus_morphism using solve [ auto ] : nat_of_P.

Lemma pow_of_2_plus n m : (pow_of_2 (n + m) = pow_of_2 n * pow_of_2 m)%nat.
Proof. unfold pow_of_2. intros. autorewrite with nat_of_P pow_of_2. reflexivity. Qed.

Lemma pow_of_2_0 : (pow_of_2 0 = 1)%nat.
Proof. 
  intros. simp pow_of_2 nat_of_P. 
Qed.

Lemma pow_of_2_Sn n : (pow_of_2 (S n) = pow_of_2 n + pow_of_2 n)%nat.
Proof. intros. simp pow_of_2 nat_of_P. ring. Qed.

Hint Rewrite pow_of_2_plus pow_of_2_0 pow_of_2_Sn  minus_plus_simpl_l_reverse pow_of_2_nat_Z : pow_of_2.

Lemma pow_of_2_pos n : (pow_of_2 n > 0)%nat.
Proof. intros. simp pow_of_2 nat_of_P. auto with nat_of_P. Qed.

Hint Resolve pow_of_2_pos : pow_of_2.

(** Z arith hints. *)

Theorem Zpos_neg : forall p:positive, - Zpos p = Zneg p.
Proof. intros. simpl. reflexivity. Qed.

Hint Rewrite Zopp_neg Zpos_neg Zopp_involutive
  Zplus_0_l Zplus_0_r Zplus_opp_l Zplus_opp_r
  Zmult_1_l Zmult_1_r Zmult_0_r Zmult_0_l
  Zpos_xI Zneg_xI
  Zpos_plus_distr Zneg_plus_distr
  Zpos_mult_morphism Zminus_succ_l
  Zminus_0_r Zminus_diag
  Zopp_neg Zopp_involutive
  : zarith.
(* Zpos_xO Zneg_xO  *)
Hint Rewrite <- Zsucc_pred Zpred_succ : zarith.

Lemma Z_of_nat_1 : Z_of_nat 1 = 1.
Proof. reflexivity. Qed.

Lemma Z_of_nat_0 : Z_of_nat 0 = 0.
Proof. reflexivity. Qed.

Hint Extern 10 => progress exfalso : zarith.
Hint Extern 10 => omega : zarith.

Lemma Z_of_nat_pos n : Z_of_nat n >= 0.
Proof. auto with zarith. Qed.

Hint Rewrite Z_of_nat_1 Z_of_nat_0 inj_0 inj_S inj_plus inj_mult inj_min inj_max : Z_of_nat. 
Hint Rewrite <- inj_eq_iff inj_le_iff inj_lt_iff inj_ge_iff Zpos_eq_Z_of_nat_o_nat_of_P : Z_of_nat.

Hint Resolve Z_of_nat_pos inj_eq inj_neq inj_le inj_gt inj_ge inj_lt : Z_of_nat.

Hint Rewrite <- Z_of_nat_1 Z_of_nat_0 inj_0 inj_S inj_plus inj_mult inj_min inj_max pow_of_2_nat_Z : Z_of_nat_inv. 
Hint Rewrite inj_eq_iff inj_le_iff inj_lt_iff inj_ge_iff Zpos_eq_Z_of_nat_o_nat_of_P : Z_of_nat_inv.
Hint Rewrite <- inj_minus1 using solve [ auto with zarith ] : Z_of_nat_inv.

Lemma Zge_opp_Zle x y : x <= y -> - x >= - y. 
Proof. intros. omega. Qed.
Hint Resolve Zge_opp_Zle : zarith.

Lemma pow_of_2_Z_plus n m : pow_of_2_Z (n + m) = pow_of_2_Z n * pow_of_2_Z m.
Proof. unfold pow_of_2_Z. intros. autorewrite with Z_of_nat nat_of_P_inv pow_of_2.
  reflexivity. 
Qed.

Ltac add_pow_bounds := repeat
  match goal with
    | |- context [ pow_of_2_Z ?n ] => let H := fresh "pow_of_2_pos_" n in
      add_hypothesis H (pow_of_2_Z_pos n)
    | |- context [ pow_of_2 ?n ] => let H := fresh "pow_of_2_pos_" n in
      add_hypothesis H (pow_of_2_pos n)
  end.

Lemma Z_of_nat_pow_of_2_minus_1 n : Z_of_nat (pow_of_2 n - 1) = 
  pow_of_2_Z n - 1.
Proof. intros. add_pow_bounds. rewrite inj_minus. 
  autorewrite with zarith pow_of_2 Z_of_nat. rewrite Zmax_right; omega.
Qed.

Lemma pow_of_2_Z_O : pow_of_2_Z 0 = 1.
Proof. intros. autorewrite with zarith pow_of_2 Z_of_nat_inv. simp pow_of_2. Qed.

Lemma pow_of_2_Z_Sn n : pow_of_2_Z (S n) = 2 * pow_of_2_Z n.
Proof. intros. autorewrite with zarith pow_of_2 Z_of_nat_inv. 
  f_equal. simpl. simp pow_of_2. omega.
Qed.

Hint Rewrite pow_of_2_Z_O pow_of_2_Z_Sn pow_of_2_Z_plus : pow_of_2.
Hint Rewrite Z_of_nat_pow_of_2_minus_1 : Z_of_nat.

Hint Rewrite plus_0_r plus_0_l plus_n_Sm minus_diag
  : arith.

Hint Rewrite <- pred_Sn mult_n_O mult_n_Sm minus_n_O
  minus_plus_simpl_l_reverse
  : arith.
