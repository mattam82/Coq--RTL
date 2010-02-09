(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Certified Haskell Prelude.

   This module implements classes for different varieties of orders: preorders,
   partial orders, total partial orders, strict orders and total strict orders.

   Author: Matthieu Sozeau <sozeau@lri.fr>
   Institution: LRI, CNRS UMR 8623 - Université Paris Sud
                91405 Orsay, France 

*)

(* $Id: FSetAVL_prog.v 616 2007-08-08 12:28:10Z msozeau $ *)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import CSDL.Basics.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Omega.
Require Import Coq.Program.Program.

Infix "+++" := app (at level 30).

Require Import Coq.Strings.String.

Fixpoint string_of_string (s : String.string) : list ascii := 
  match s with
    | String.EmptyString => nil
    | String.String c s => c :: string_of_string s
  end.

Definition string := list ascii.

Definition char_of_bool (b : bool) : ascii := (if b then "1" else "0")%char.

Coercion str_of_string := string_of_string.

Fixpoint shows (s : list ascii) : String.string := 
  match s with
    | nil => String.EmptyString
    | hd :: tl => String.String hd (shows tl)
  end.

Class Show A :=
  show : A -> string.

Definition print `{Show T} (a : T) : String.string := shows (show a).

Open Local Scope char_scope.

Fixpoint div10 n : nat * nat :=
  match n with
    | S (S (S (S (S (S (S (S (S (S x))))))))) => let (q,r) := div10 x in (S q, r)
    | x => (0, x)
  end.

Notation "( x & y )" := (existS _ x y) : core_scope.

Open Local Scope char_scope.

Obligation Tactic := program_simpl ; auto.

Program Definition print_digit (x : nat | x < 10) : ascii :=
  match x with 
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | 9 => "9"
    | _ => !
  end.

Ltac discriminates := try match goal with [ H : ?x <> ?x |- _ ] => elim H ; reflexivity end.

  Next Obligation. intuition. Qed.
  Next Obligation. intuition. Qed.

Program Fixpoint print_nat (x : nat) { wf lt x } : string :=
  let '(q, r) := euclid x 10 in
    match q with 
      | 0 => [print_digit r]
      | S q' => print_nat q ++ [print_digit r]
    end.

  Next Obligation.
    assert (Have (10 > 0)) by (red ; auto with arith).
    generalize (euclid_spec x _ _ _ (symmetry Heq_anonymous)).
    intros. simpl in H0. subst.
    destruct_call euclid. destruct H0 ; auto.
  Qed.


  Next Obligation.
    assert (Have (10 > 0)) by (red ; auto with arith).
    generalize (euclid_spec x _ _ _ (symmetry Heq_anonymous)).
    intros. simpl in H0. subst.
    destruct_call euclid. destruct H0 ; auto.
    subst x. omega.
  Qed.


  Next Obligation.
    assert (Have (10 > 0)) by (red ; auto with arith).
    generalize (euclid_spec x _ _ _ (symmetry Heq_anonymous)).
    intros. simpl in H0. subst.
    destruct_call euclid. destruct H0 ; auto.
  Qed.

Example print2000 := Eval lazy in (print_nat 2000).

Instance nat_show : Show nat :=
  { show := print_nat }.

Open Local Scope string_scope.

Instance bool_show : Show bool :=
  { show x := if x then "true" else "false" }.

Open Local Scope string_scope.

Instance prod_show `(Show a, Show b) : Show (prod a b) :=
  { show x := let (l, r) := x in "(" +++ show l +++ "," +++ show r +++ ")" }.

Instance sum_show `(Show a, Show b) : Show (sum a b) :=
  { show x := match x with
                | inl x => "inl" +++ show x
                | inr y => "inr" +++ show y
              end }.
