Require Import EquivDec.
Require Import Asm.X86.X86.
Require Import Asm.Bitvector.Bitvector.
Require Import CSDL.Vector.
Require Import CSDL.Binary.

Instance: EqDec int32 eq.
Proof. apply const_eq. Defined.

Ltac dec_eq_one := 
  match goal with 
    | H : ?x =/= ?x |- _ => elimtype False; apply H; reflexivity
    | H : ?x === ?y |- _ => red in H; subst
    | |- { ?x === ?x } + { _ } => left; reflexivity
    | |- { _ } + { ?x =/= ?x } => left; f_equal
    | |- { ?x === ?y } + { _ } => right; let H := fresh in intro H; red in H; 
      (injection H || discriminate); intros; subst
  end.

Ltac dec_eq := try solve [ repeat dec_eq_one ];
  repeat match goal with H : _ === _ |- _ => red in H; subst end.

Instance option_eq_dec {A} `(EqDec A eq) : EqDec (option A) eq.
Proof.
  intros x y. destruct x; destruct y; dec_eq.
  destruct (equiv_dec a a0); dec_eq. 
Qed.

Instance reg32_eq_dec : EqDec reg32 eq.
  intros x y. apply reg32_eq_dec. 
Qed.

Instance reg8_eq_dec : EqDec reg8 eq.
  intros x y. change ({x = y} + {x <> y}).
  decide equality x y. 
Qed.

Instance scale_eq_dec : EqDec scale eq.
  intros x y. change ({x = y} + {x <> y}). 
  decide equality x y.
Qed.

Instance: EqDec address eq. 
  red; intros. destruct x; destruct y; dec_eq.
  destruct (equiv_dec addrDisp addrDisp0); dec_eq.
  destruct (equiv_dec addrBase addrBase0); dec_eq.
  destruct (equiv_dec addrIndex addrIndex0); dec_eq.
Qed.

Instance genop_eq_dec : EqDec genop32 eq.
  intros x y. change ({x = y} + {x <> y}).
  decide equality x y. 
  apply int32_eq_dec. apply reg32_eq_dec. 
  apply equiv_dec.
Qed.

Instance genop8_eq_dec : EqDec genop8 eq.
  intros x y. change ({x = y} + {x <> y}).
  decide equality x y. 
  apply int32_eq_dec. apply reg8_eq_dec. 
  apply equiv_dec.
Qed.

Instance arith_op_eq_dec : EqDec arith_op eq.
  intros x y. change ({x = y} + {x <> y}).
  decide equality x y. 
Qed.

Instance condition_eq_dec : EqDec condition eq.
  intros x y. change ({x = y} + {x <> y}).
  decide equality x y. 
Defined.

Instance cc_eq_dec : EqDec cc eq.
  intros x y. change ({x = y} + {x <> y}).
  decide equality x y. 
  apply condition_eq_dec.
  apply equiv_dec.
Qed.

Instance shift_op_eq_dec : EqDec shift_op eq.
  intros x y. change ({x = y} + {x <> y}).
  decide equality x y. 
Qed.

Instance instr_eq_dec : EqDec instr eq.
  intros x y. 
  destruct x; destruct y; dec_eq.

  destruct (equiv_dec a a0); dec_eq.
  destruct (equiv_dec g g1); dec_eq.
  destruct (equiv_dec g0 g2); dec_eq.

  destruct (equiv_dec a a0); dec_eq.
  destruct (equiv_dec g g1); dec_eq.
  destruct (equiv_dec g0 g2); dec_eq.

  destruct (equiv_dec g g0); dec_eq.

  destruct (equiv_dec g g1); dec_eq.
  destruct (equiv_dec g0 g2); dec_eq.

  destruct (equiv_dec g g0); dec_eq.

  destruct (equiv_dec i i0); dec_eq.
  destruct (equiv_dec c c0); dec_eq.

  destruct (equiv_dec g g0); dec_eq.

  destruct (equiv_dec r r0); dec_eq.
  destruct (equiv_dec a a0); dec_eq.

  destruct (equiv_dec g g1); dec_eq.
  destruct (equiv_dec g0 g2); dec_eq.

  destruct (equiv_dec g g1); dec_eq.
  destruct (equiv_dec g0 g2); dec_eq.

  destruct (equiv_dec g g0); dec_eq.

  destruct (equiv_dec g g0); dec_eq.

  destruct (equiv_dec s s0); dec_eq.
  destruct (equiv_dec g g1); dec_eq.
  destruct (equiv_dec g0 g2); dec_eq.
Defined.
