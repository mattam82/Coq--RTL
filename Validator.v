Require Import Equations.

Equations(nocomp) nth_prf {A} (n : nat) (l : list A) (p : n < length l) : A :=
nth_prf A n nil pf :=! pf;
nth_prf A O (cons a l) pf := a ;
nth_prf A (S n) (cons a l) pf := nth_prf n l _.

  Next Obligation. inversion pf. Defined.
  Next Obligation. auto with arith. Defined.
  Next Obligation. find_empty. Defined.

Require Import Asm.X86.X86.
Require Import Asm.Bitvector.Bitvector.
Require Import String.
Require Import Bvector.
Require Import CSDL.Vector.
Require Import CSDL.Binary.
Require Import CSDL.Representable.
Require Import CSDL.BinaryBe.

Definition regset := Int32Map.t bool.

Definition instr_is_disallowed (i : instr) :=
  match i with
    (* Disallow [ret] and indirect calls through memory. *)
    | Ret => true
    | Call op | Jmp op =>
      match op with
        | Address _ => true
        | _ => false
      end
    | _ => false
  end.

Require Import CSDL.Hexadecimal.
Require Import CSDL.Show.

Definition cs_mask : bits 32 :=
  fst (binary_minus_be full (representation 32 31)).

Eval vm_compute in (eq_refl : print cs_mask = "0xffffffe0")%string.

Definition nacl_jmp_instr : (instr * instr) :=
  (Arith And (Reg EAX) (Imm _ cs_mask), Jmp (Reg EAX)).

Require Import EquivDec.

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
  Ltac add_eq :=
    match goal with
      | [ x : ?T, y : ?T |- _ ] =>
        match goal with 
          | H : x === y |- _ => red in H; subst
          | _ => destruct (equiv_dec x y)
        end
    end. 
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

Definition is_nacl_jmp_idiom i j :=
  let '(a, b) := nacl_jmp_instr in
    equiv_decb a i && equiv_decb b j.

Definition block_size := 32. (* bytes *)
Definition block_size_bin : bits 32 := 
  representation (e:=BigEndian) 32 32.
Definition block_size_mask : bits 32 :=
  binary_shiftl_n_full full 5.

Definition block (ip : int32) : int32 :=
  BVand 32 ip (vector_append (full (n:=30)) (zero (n:=2))).

Parameter decode_instr : int32 -> instr * int32.
Parameter instr_length : int32 -> int32.

Definition instr_overlaps_block_size (ip : int32) : bool :=
  let (instrend, of) := binary_plus_be ip (instr_length ip) in
    of || negb (binary_eq zero (BVand 32 block_size_mask instrend)).

Definition instr_is_indirect_jmp_or_call (i : instr) :=
  match i with
    | Jmp (Imm _)
    | Call (Imm _) => false
    | Jmp _ | Call _ => true
    | _ => false
  end.

Definition instr_is_direct_jmp_or_call (i : instr) : option int32 :=
  match i with
    | Jmp (Imm ip) => Some ip
    | Call (Imm ip) => Some ip
    | _ => None
  end.

Inductive valid_error : Set :=
| Disallowed_instruction
| Block_alignment_failure
| Bad_indirect_control
| Call_to_invalid_address.
Print sum.

Definition start_addresses := list int32.

Definition two {n} : bits (Datatypes.S (Datatypes.S n)) :=
  zx_be (Vcons true (Vcons false Vnil)).

(* Equations(nocomp) build_startaddrs (ip : int32) (jtargets : regset) *)
(*   (sa : start_addresses) *)
(*   (icount : nat) (instrs : list instr) (p : bvec_to_nat ip < length instrs) *)
(*   { measure (length instrs - icount) } : (regset * start_addresses) + valid_error := *)
(*   if eq_nat_dec (Datatypes.S (bvec_to_nat ip)) (length instrs) then inl (jtargets, sa) *)
(*   else *)
(*     let instr := nth_prf (bvec_to_nat ip) instrs p in *)
(*       if instr_is_disallowed instr  *)
(*       then inr Disallowed_instruction *)
(*       else *)
(*         let sa := ip :: sa in *)
(*         let jtargets := Int32Map.set ip true jtargets in *)
(*           if instr_overlaps_block_size ip *)
(*           then inr Block_alignment_failure *)
(*           else if instr_is_indirect_jmp_or_call instr  *)
(*             then if ltb icount 2  *)
(*               then inr Bad_indirect_control *)
(*               else if negb (binary_eq (block ip) (block (bdec (bdec ip))))  *)
(*                 then inr Bad_indirect_control *)
(*                 else if negb (is_nacl_jmp_idiom instr (nth_prf (bvec_to_nat (bdec ip)) instrs _))  *)
(*                 then inr Bad_indirect_control *)
(*                 else build_startaddrs (binc ip) jtargets sa (Datatypes.S icount) instrs _ *)
(*             else build_startaddrs (binc ip) jtargets sa (Datatypes.S icount) instrs _. *)

Section Validator.
  Variable text_limit : int32.
  
  Program Fixpoint build_startaddrs (ip : int32) (jtargets : regset) (sa : start_addresses) 
    (prev : list instr) (instrs : list instr) { struct instrs } 
    : (regset * start_addresses) + valid_error :=
    match instrs with
      | nil => inl (jtargets, sa)
      | cons instr instrs =>
        if instr_is_disallowed instr 
        then inr Disallowed_instruction
        else
          let sa := ip :: sa in
          let jtargets := Int32Map.set ip true jtargets in
            if instr_overlaps_block_size ip
            then inr Block_alignment_failure
            else if instr_is_indirect_jmp_or_call instr 
              then if dec (ltb (List.length prev) 2)
                then inr Bad_indirect_control
                else if negb (binary_eq (block ip) (block (bdec (bdec ip)))) 
                  then inr Bad_indirect_control
                  else if negb (is_nacl_jmp_idiom instr (nth_prf (bvec_to_nat (bdec ip)) instrs _)) 
                  then inr Bad_indirect_control
                  else build_startaddrs (binc ip) jtargets sa (instr :: prev) instrs
              else build_startaddrs (binc ip) jtargets sa (instr :: prev) instrs
    end.

  Next Obligation. admit. Defined.


(* Program Fixpoint build_startaddrs (ip : int32) (jtargets : regset) *)
(*   (sa : start_addresses) *)
(*   (icount : nat) (instrs : list instr) (p : bvec_to_nat ip < length instrs) *)
(*   { measure (length instrs - icount) } : (regset * start_addresses) + valid_error := *)
(*   if eq_nat_dec (Datatypes.S (bvec_to_nat ip)) (length instrs) then inl (jtargets, sa) *)
(*   else *)
(*     let instr := nth_prf (bvec_to_nat ip) instrs p in *)
(*       if instr_is_disallowed instr  *)
(*       then inr Disallowed_instruction *)
(*       else *)
(*         let sa := ip :: sa in *)
(*         let jtargets := Int32Map.set ip true jtargets in *)
(*           if instr_overlaps_block_size ip *)
(*           then inr Block_alignment_failure *)
(*           else if instr_is_indirect_jmp_or_call instr  *)
(*             then if ltb icount 2  *)
(*               then inr Bad_indirect_control *)
(*               else if negb (binary_eq (block ip) (block (bdec (bdec ip))))  *)
(*                 then inr Bad_indirect_control *)
(*                 else if negb (is_nacl_jmp_idiom instr (nth_prf (bvec_to_nat (bdec ip)) instrs _))  *)
(*                 then inr Bad_indirect_control *)
(*                 else build_startaddrs (binc ip) jtargets sa (Datatypes.S icount) instrs _ *)
(*             else build_startaddrs (binc ip) jtargets sa (Datatypes.S icount) instrs _. *)

(*   Next Obligation. *)
(* Admitted. *)

(*   Next Obligation. *)
(*     admit. *)
(*   Defined. *)

(*   Next Obligation.  *)
(*     admit. *)
(*   Defined. *)

(*   Next Obligation.  *)
(*     admit. *)
(*   Defined. *)

(*   Next Obligation.  *)
(*     admit. *)
(*   Defined. *)

    Fixpoint direct_transfers (l : list instr) (jtargets : regset) (sa : start_addresses) : unit + valid_error :=
      match sa with
        | nil => inl tt
        | cons ip sas =>
          let instr := List.nth (bvec_to_nat ip) l Ret in
            match instr_is_direct_jmp_or_call instr with
              | Some ip' => 
                if negb (binary_be_lt ip' text_limit) 
                  || negb (Int32Map.get ip' jtargets)
                then inr Call_to_invalid_address
                else direct_transfers l jtargets sas
              | None => direct_transfers l jtargets sas
            end
      end.

    Definition validator (s : list instr) : unit + valid_error :=
      let jump_targets := Reg32Map.init false in
      let ip : int32 := nat_to_bvec 32 0 in
        match build_startaddrs zero jump_targets [] [] s with
          | inl (targets, sa) =>
            direct_transfers s targets sa
          | inr r => inr r
        end.

End Validator.



    