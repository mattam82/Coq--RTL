Require Import Omega.
Require Import Equations.

Derive NoConfusion for bool.

Set Automatic Introduction.
Generalizable All Variables.

Class Have (P : Prop) := have : P.

Ltac unhave := unfold Have in *.

Hint Extern 4 (Have ?P) => unhave ; omega : typeclass_instances.

(** Correctness lemmas. *)

Class Correctness (cond : Prop) (concl : Prop) :=
  correctness_prf : Basics.impl cond concl.

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

(** Prop-bool views. *)

Class PropView (b : bool) (P : Prop) :=
  prop_view : b = true <-> P.

Ltac destruct_bool :=
  repeat match goal with
           | b : bool |- _ => destruct b 
         end.

Lemma prop_view_false `{PropView b p} : b = false <-> ~ p.
Proof.
  destruct H.
  split; intros.
  destruct b; firstorder congruence.
  destruct b; firstorder congruence.
Qed.

Instance or_view `{PropView b p, PropView b' p'} : PropView (b || b') (p \/ p').
Proof.
  constructor. intros.
  rewrite <- 2 prop_view. 
  destruct_bool; noconf H1; firstorder.
  intros. 
  rewrite <- 2 prop_view in H1.
  destruct_bool; firstorder.
Qed.

Instance and_view `{PropView b p, PropView b' p'} : PropView (b && b') (p /\ p').
Proof.
  constructor. intros.
  rewrite <- 2 prop_view. 
  destruct_bool; noconf H1; firstorder.
  intros. 
  rewrite <- 2 prop_view in H1.
  destruct_bool; firstorder.
Qed.

Instance xor_view `{PropView b p, PropView b' p'} : PropView (xorb b b') ((p /\ ~ p') \/ (~ p /\ p')).
Proof.
  constructor. intros.
  rewrite <- 2 prop_view. 
  destruct_bool; noconf H1 ; firstorder auto. 
  intros. 
  rewrite <- 2 prop_view in H1.
  destruct_bool; firstorder.
Qed.

Instance negb_view `{PropView b p} : PropView (negb b) (~ p).
Proof.
  constructor; intros; firstorder auto with *. 
  intro. specialize (H1 H2). destruct b; firstorder.
Qed.

Lemma negb_inv b : negb b = false <-> b = true.
Proof. destruct b; firstorder. Qed.
