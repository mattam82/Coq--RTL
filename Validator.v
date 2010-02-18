Add LoadPath "~/Downloads/htt/v8.2".
Require Import Equations.
Require Import CSDL.Binary.
Obligation Tactic := program_simpl.

Equations(nocomp) nth_prf {A} (n : nat) (l : list A) (p : n < length l) : A :=
nth_prf A n nil pf :=! pf;
nth_prf A O (cons a l) pf := a ;
nth_prf A (S n) (cons a l) pf := nth_prf n l _.

  Next Obligation. auto with arith. Defined.

Equations(nocomp) bits_enum (n : nat) : list (bits n) :=
bits_enum 0 := [ Vnil] ;
bits_enum (S n) := let bn := bits_enum n in
  map (Vcons true) bn ++ map (Vcons false) bn.

Require Import Asm.X86.X86.
Require Import Asm.Bitvector.Bitvector.
Require Import String.
Require Import Bvector.
Require Import CSDL.Representable.
Require Import CSDL.BinaryBe.

Require Import CSDL.EqDec_instr.

Definition regset := Int32Map.t bool.

(* Disallow [ret] and indirect calls through memory. *)

Equations(nocomp) instr_is_disallowed (i : instr) : bool :=
instr_is_disallowed Ret := true ;
instr_is_disallowed (Call (Address _)) := true ;
instr_is_disallowed (Jmp (Address _)) := true ;
instr_is_disallowed _ := false.

Require Import CSDL.Hexadecimal.
Require Import CSDL.Show.

Definition block_size := 32. (* bytes *)

Definition binary_shiftl_n_full {n} (b : bits n) m : bits (n + m) :=
  vector_append b zero.

Definition block_size_mask : bits 32 :=
  binary_shiftl_n_full (@full 27) 5.

Definition block_offset_mask := 
  binary_inverse block_size_mask.

Fact block_size_mask_hex : print block_size_mask = "0xffffffe0"%string.
Proof. reflexivity. Qed.

Definition nacl_jmp_instr : (instr * instr) :=
  (Arith And (Reg EAX) (Imm _ block_size_mask), Jmp (Reg EAX)).

Definition is_nacl_jmp_idiom i j :=
  let '(a, b) := nacl_jmp_instr in
    equiv_decb a i && equiv_decb b j.

(** 32 byte block of an instruction. *)

Definition block (ip : int32) : int32 :=
  BVand 32 ip block_size_mask.

Definition block_offset (ip : int32) : int32 :=
  BVand 32 ip block_offset_mask.

Parameter decode_instr : int32 -> instr * int32.
Parameter instr_length : int32 -> int32.

Equations(nocomp) instr_overlaps_block_size (ip : int32) : bool :=
instr_overlaps_block_size ip
  with binary_plus_be (block_offset ip) (instr_length ip) :=
  | pair offset of := negb (binary_eq (block offset) zero).

Ltac destruct_bits :=
  repeat match goal with
           | b : bit |- _ => destruct b 
           | b : bool |- _ => destruct b 
         end.

Class Commutative {A B} (f : A -> A -> B) := commutative : Π x y, f x y = f y x.

Instance andb_comm : Commutative andb := andb_comm.
Instance orb_comm : Commutative orb := orb_comm.
Instance xorb_comm : Commutative xorb := xorb_comm.

Instance Vbinary_comm {f} `(Commutative bool bool f) n : 
  Commutative (Vbinary bool f n).
Proof. intros x y. induction n. simpl. reflexivity.
  depelim x; depelim y.
  simpl. rewrite (commutative (f:=f)), IHn. reflexivity.
Qed.

Lemma BVand_mask_zero (x : bits 32) : block x = zero -> [: x] <= pow_of_2 5.
Proof. intros. unfold block in H. Transparent BVand.
  unfold BVand in H.
  repeat depelim x.
  unfold block_size_mask, zero in H.
  rewrite (commutative (f:=Vbinary bool andb 32)) in H.
  simpl in H.
  injection H. clear H; intros; subst.
  change (pow_of_2 5) with 32.
  apply leb_complete. destruct_bits; reflexivity.
Qed.

Notation " f $ x " := (f x) (only parsing, at level 10, x at level 60).

Class Absorbant {A} (f : A -> A -> A) (a : A) := absorbant : forall x, f a x = a.
Class Neutral {A} (f : A -> A -> A) (a : A) := neutral : forall x, f a x = x.

Ltac crush := 
  try red; intros; destruct_bits; firstorder.

Instance andb_absorbant : Absorbant andb false.
Proof. crush. Qed.

Instance andb_neutral : Neutral andb true.
Proof. crush. Qed.

Instance orb_absorbant : Absorbant orb true.
Proof. crush. Qed.

Instance orb_neutral : Neutral orb false.
Proof. crush. Qed.

Instance Vbinary_absorbant `(Absorbant bool f a) n : Absorbant (Vbinary bool f n) (constant_vector n a).
Proof. intros v. induction v. reflexivity.
  simpl. rewrite IHv. rewrite (absorbant a0). reflexivity.
Qed.

Instance Vbinary_neutral `(Neutral bool f a) n : Neutral (Vbinary bool f n) (constant_vector n a).
Proof. intros v. induction v. reflexivity.
  simpl. rewrite IHv. rewrite (neutral a0). reflexivity.
Qed.

Definition next_ip (ip : int32) : int32 :=
  fst $ binary_plus_be ip (instr_length ip).

Parameter text_limit : int32.

Parameter ip_length : forall ip, binary_be_lt ip text_limit = true ->
  binary_be_le (next_ip ip) text_limit = true.

Lemma BVand_shiftl_full n k (x : bits (n + k)) : 
  BVand _ x (binary_shiftl_n_full (@full n) k) = 
  vector_append (fst (vector_split x)) zero.
Proof.
  funelim (vector_split x). Transparent BVand. unfold binary_shiftl_n_full.
  simp vector_append. induction x; simpl; auto.
  rewrite (commutative (f:=andb)). rewrite (absorbant (f:=andb)). 
  fold (@zero n).
  rewrite IHx. reflexivity.
  destruct (vector_split v).
  simpl in *. f_equal.
  rewrite (commutative (f:=andb)). rewrite (neutral (f:=andb)). reflexivity.
  rewrite <- H.
  f_equal.
Qed.

Definition un_of {n} (r : bits n * overflow) : bits n := fst r.
Typeclasses Transparent BVand.

Require Import CSDL.Basics.
Require Import Numbers.Natural.Peano.NPeano.
Import Nat.

Lemma Vbinary_nil (f : bool -> bool -> bool) :
  Vbinary bool f _ Vnil Vnil = Vnil.
Proof.
  simpl. reflexivity.
Qed.

Lemma Vbinary_cons (f : bool -> bool -> bool) n (a b : bool) (x y : bits n) : 
  Vbinary bool f (Datatypes.S n) (a |:| x)%vect (b |:| y)%vect = (f a b |:| Vbinary bool f n x y)%vect.
Proof.
  simpl. reflexivity.
Qed.

Opaque Vbinary.
Hint Rewrite Vbinary_nil Vbinary_cons : Vbinary.

Lemma BVxor_absorbant n (x : bits n) : BVxor n (constant_vector n true) x = binary_inverse x.
Proof.
  induction x; simp binary. simpl. rewrite IHx. reflexivity.
Qed.

Lemma BVxor_neutral n (x : bits n) : BVxor n (constant_vector n false) x = x.
Proof.
  induction x; simp binary. simpl. rewrite IHx. destruct a; reflexivity.
Qed.

Lemma nat_of_vector_split {n k} (x : bits (n + k)) : 
  let (high, low) := vector_split x in
    [: x ] = pow_of_2 k * [: high ] + [: low ].
Proof.
  funelim (vector_split x).
  omega.
  destruct (vector_split v). destruct a.
  simpl. rewrite H. simp pow_of_2. ring.

  rewrite H.
  simpl. auto.
Qed.

Lemma modulo_nat_binary {n k} (x : bits (n + k)) : 
  modulo [: x ] (pow_of_2 k) = [: snd (vector_split x) ].
Proof.
  assert (splitx := nat_of_vector_split x). destruct (vector_split x).
  rewrite splitx.
  simpl.
  rewrite mult_comm, plus_comm.
  rewrite mod_add. rewrite mod_small. 
  reflexivity. apply nat_of_binary_bound.

  pose (pow_of_2_pos k). omega.
Qed.

Lemma block_spec (x : bits 32) : [: block x ] = 
  [: x ] - modulo [: x ] 32.
Proof. unfold block. 
  unfold block_size_mask.
  pose (BVand_shiftl_full 27 5 x).
  Opaque BVand vector_split. simpl in e. rewrite e. clear e.
  pose (nat_of_binary_be_vector_append  (fst (@vector_split _ 27 5 x))
    (@Binary.zero 5)). Opaque pow_of_2. simpl in e. rewrite e. 
  clear e.
  rewrite (@modulo_nat_binary 27 5).
  generalize (@nat_of_vector_split 27 5 x). destruct @vector_split.
  intro Hx.
  replace [: x] with (pow_of_2 5 * [: v] + [: v0]).
  simpl. 
  pose (nat_of_binary_bound v).
  pose (nat_of_binary_bound v0).
  ring_simplify. set(foo:=pow_of_2 5 * [: v]). omega.
Qed.

Lemma instr_overlaps_block_size_spec (ip : int32) :
  instr_overlaps_block_size ip = false -> block ip = block (next_ip ip).
Proof.
  funelim (instr_overlaps_block_size ip).
  apply nat_of_binary_be_inj. 
  rewrite ! block_spec.
  assert([: next_ip ip] > [: ip ]). 

    Unset Printing Notations. 
    idtac.
Set Printing 
    rewrite e.
    simp binary.
    rewrite (@modulo_nat_binary 27 5).
    symmetry.
    assert (minx:=binary_minus_correct x (zx_be (snd (@vector_split _ 27 5 x)))).
    do 2 red in minx.
    replace [: snd (@vector_split _ 27 5 x)] with [: zx_be (t':=32) (snd (@vector_split _ 27 5 x)) ].
    apply minx. clear minx.
    funelim (binary_minus_correct x (zx_be (t':=32) (snd (@vector_split _ 27 5 x)))).
    

    repeat depelim x.
    Opaque nat_of_binary_be. simpl.
    simpl fst.
    simp vector_split.
    simpl.
    simp vector_split.
    unfold binary_shiftl_n_full. Opaque minus modulo_nat. simpl.
    simpl.
    


  apply binary_eq_eq.
  Print Hint binary_eq.
  
  

instr_overlaps_block_size ip
  with binary_plus_be (block_offset ip) (instr_length ip) :=
  | pair offset of := negb (binary_eq (block offset) zero).


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

Section Validator.
  Variable text_limit : int32.


  Equations(nocomp) build_startaddrs (ip : int32) (jtargets : regset) (sa : start_addresses) 
    (prev : list instr) (instrs : list instr) : (regset * start_addresses * int32) + valid_error :=
  build_startaddrs ip jtargets sa prev nil := inl (jtargets, sa, ip);
  build_startaddrs ip jtargets sa prev (cons instr instrs) with instr_is_disallowed instr :=
  | true := inr Disallowed_instruction;
  | false with instr_overlaps_block_size ip :=
    { | true := inr Block_alignment_failure ;
      | false with instr_is_indirect_jmp_or_call instr :=
        { | true with dec (ltb (List.length prev) 2) :=
          { | left := inr Bad_indirect_control;
            | right with negb (binary_eq (block ip) (block (bdec (bdec ip)))) :=
              { | true := inr Bad_indirect_control;
                | false with negb (is_nacl_jmp_idiom instr (nth_prf (bvec_to_nat (bdec ip)) instrs _)) :=
                  { | true := inr Bad_indirect_control;
                    | false := 
                      let sa := ip :: sa in
                      let jtargets := Int32Map.set ip true jtargets in
                      let ip' := fst $ binary_plus_be ip (instr_length ip) in
                        build_startaddrs ip' jtargets sa (instr :: prev) instrs } } 
          } ;
          | false := 
            let sa := ip :: sa in
            let jtargets := Int32Map.set ip true jtargets in
              build_startaddrs (binc ip) jtargets sa (instr :: prev) instrs } }.
  
  Next Obligation. admit. Defined.

  Definition jtargets_inv jtargets limit :=
    forall addr, 
      binary_be_lt addr limit = true ->
      BVand _ addr block_size_mask = addr -> Int32Map.get addr jtargets = true.

  Lemma build_startaddrs_inv (ip : int32) (jtargets : regset) (sa : start_addresses) 
    (prev instrs : list instr) jtargets' sas ip' :
    build_startaddrs ip jtargets sa prev instrs = inl (jtargets', sas, ip') ->
    jtargets_inv jtargets ip ->
    jtargets_inv jtargets' ip'.
  Proof.
    funelim (build_startaddrs ip jtargets sa prev instrs).
    specialize (H (binc ip) _ _ _ H0). apply H.
    red; red in H1.
    intros. 
    rewrite Int32Map.gsspec.
    case_eq (Int32Indexed.eq addr ip). intros.
    subst. clear H4. reflexivity.
    intros diffip _.
    unfold instr_overlaps_block_size in Heq0.
    destruct_call_eq @binary_plus_be bip. 
    destruct o. noconf Heq0. Opaque binary_eq BVand BVxor. simpl in Heq0.
    rewrite negb_false_iff in Heq0.
    apply binary_eq_eq in Heq0.
    correct bip. simpl in bip.
    symmetry in Heq0. apply BVand_mask_zero in Heq0.
    

    Lemma BVxor_be {n} (x y z : bits n) : BVxor n x y = z ->
      [: x ] 
      [: x ] 


    
    


    apply H with (sas). exact (binc ip). assumption.
    clear H0.
    red; red in H1.
    intros. 
    rewrite Int32Map.gsspec.
    case_eq (Int32Indexed.eq addr ip). intros.
    subst. clear H2. reflexivity.
    intros.
    apply H1. assumption.
  Qed.
    

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

    Definition validator (s : list instr) : start_addresses + valid_error :=
      let jump_targets := Reg32Map.init false in
      let ip : int32 := nat_to_bvec 32 0 in
        match build_startaddrs zero jump_targets [] [] s with
          | inl (targets, sa) =>
            match direct_transfers s targets sa with
              | inl tt => inl sa
              | inr r => inr r
            end
          | inr r => inr r
        end.

End Validator.

Definition binary := list instr.

Inductive exec_star : forall (l : list instr) (pc : int32) (s q : state), Prop :=
| exec_one : forall (i : instr) (l : list instr) (pc : int32) (s q : state), 
  exec (i, pc) s q -> exec_star (i :: l) pc s q
| exec_next : forall (i : instr) (l : list instr) (pc : int32) (s q r : state),
  exec (i, pc) s q -> exec_star l (stPc q) q r ->
  exec_star (i :: l) pc s r. 

Definition reachable (p : list instr) (ip : int32) (ip' : int32) : Prop :=
  forall s e : state, exec_star p ip s e -> stPc s = ip -> stPc e = ip'.

Parameter text_limit : int32.

Definition invariant := forall p s, validator text_limit p = inl s ->
  forall ip, In ip s -> 
    forall ip', reachable p ip ip' -> In ip' s.

Theorem safe : invariant.
Proof.
  intros p s val ip ips ip' reach.
  red in reach.  
  induction p. unfold validator in val. simpl in val. injection val.
  intros. subst. inversion ips.
  