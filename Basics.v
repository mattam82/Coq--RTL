Require Export Arith Program Equations Have.

Hint Extern 4 => discriminates : core.

Ltac simpdep := reverse ; simplify_dep_elim ; simplify_IH_hyps.

Definition ltb (x y : nat) := leb (S x) y.

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

Lemma euclid_spec n m `{Have (m > 0)} : forall q r, euclid n m = (q, r) -> n = m * q + r.
Proof.
  intros n m H. unfold euclid. ind_on euclid_func. 
  admit.

  destruct x as [ n' [ m' Hm' ] ]; simpl in *.
  case_eq (ltb n' m') ; intro Hlt ; rewrite Hlt in *. 
  program_simpl. omega.
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
  rewrite <- H0.
  rewrite <- le_plus_minus. reflexivity.
  omega.
Defined.

Eval compute in (euclid 66 8).

Definition quotient_nat n m `{Have (m > 0)} : nat := fst (euclid n m).
Definition modulo_nat n m `{Have (m > 0)} : nat := snd (euclid n m).

Lemma quotient_cancel : forall x y `{Have (y > 0)}, modulo_nat x y = 0 -> quotient_nat x y * y = x.
Proof. intros x y H. unfold modulo_nat, quotient_nat in *. 
  generalize (euclid_spec x y). destruct_call euclid ; intros Heucl ; simplify_IH_hyps.
  simpl in *. intros. subst. ring.
Defined.
