Require Import Asm.Bitvector.Bitvector.
Require Import String.
Require Import Bvector.
Require Import CSDL.Representable.
Require Import CSDL.BinaryBe.
Require Import CSDL.EqDec_instr.
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

Definition block_size_mask : bits block_size :=
  binary_shiftl_n_full_comm (@full 27) 5.

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

Definition dword_size := 32.

Definition block (ip : int32) : int32 :=
  BVand dword_size ip block_size_mask.

Definition block_offset (ip : int32) : int32 :=
  BVand dword_size ip block_offset_mask.

Notation " f $ x " := (f x) (only parsing, at level 10, x at level 60).

Derive DependentElimination for vector.
Print DependentElimination_vector.

Lemma elim_vec_Sn (A : Type) n (P : vector A (Datatypes.S n) -> Type) :
  (Π (a : A) (v : vector A n), P (a |:| v)%vect) -> Π v, P v.
Proof. intros. depelim v. auto. Defined.

Instance depelim_vec_Sn {A} n : DependentEliminationPackage (vector A (Datatypes.S n)) :=
  { elim := elim_vec_Sn }.

Lemma BVand_mask_zero (x : bits 32) : block x = zero -> [: x] <= pow_of_2 5.
Proof. intros. unfold block in H. Transparent BVand.
  unfold BVand in H. revert H.
  repeat (elim x using elim_vec_Sn; clear x; intros ? x). depelim x.
  intros H.
  unfold block_size_mask, zero in H.
  rewrite (commutative (f:=Vbinary andb)) in H.
  simpl in H.
  injection H. clear H; intros; subst.
  change (pow_of_2 5) with 32.
  apply leb_complete. unfold bit in *; destruct_bool; reflexivity.
Qed.

Definition un_of {n} (r : bits n * overflow) : bits n := fst r.
Typeclasses Transparent BVand.

Require Import CSDL.Basics.

Require Import Numbers.Natural.Peano.NPeano.
Import Nat.

Lemma block_spec (x : bits 32) : [: block x ] = 
  [: x ] - [: x ] mod 32.
Proof. unfold block. 
  unfold block_size_mask.
  setoid_rewrite (BVand_shiftl_full_comm 27 5 x).
  setoid_rewrite (@nat_of_binary_be_vector_append 27 5).  
  rewrite (@modulo_nat_binary 27 5).
  generalize (@nat_of_vector_split 27 5 x). destruct @vector_split.
  intro Hx.
  replace [: x] with (pow_of_2 5 * [: v] + [: v0]).
  simpl. 
  pose (nat_of_binary_bound v).
  pose (nat_of_binary_bound v0).
  ring_simplify. set(foo:=pow_of_2 5 * [: v]). omega.
Qed.

Lemma block_offset_spec (x : bits 32) : [: block_offset x ] = 
  [: x ] mod 32.
Proof. unfold block_offset.
  unfold block_offset_mask. 
  rewrite (commutative (f:=BVand 32)).
  change (binary_inverse block_size_mask) with (vector_append (@Binary.zero 27) (@full 5)).
  rewrite (@modulo_nat_binary 27 5). 
  destruct x using (vector_split_elim_append (n:=27) (m:=5)).
  rewrite vector_split_append.
  unfold BVand. rewrite (Vbinary_append (@Binary.zero 27) high (@full 5) low).
  Opaque vector_append Vbinary.
  simpl. 
  rewrite (@nat_of_binary_be_vector_append 27 5). 
  setoid_rewrite absorbant. setoid_rewrite neutral. 
  simp binary. 
Qed.

Hint Rewrite @Vbinary_nil @Vbinary_cons : binary.
Hint Rewrite @block_spec @block_offset_spec : binary.

Hint Extern 4 => progress (subst || destruct_conjs) : binary.

Lemma thirty_two_diff_0 : 32 <> 0.
Proof. auto. Qed.
Hint Resolve thirty_two_diff_0 : core.

Lemma block_lt_ip ip : [: block ip ] <= [: ip ].
Proof. rewrite block_spec. generalize (mod_le [: ip ] 32 thirty_two_diff_0). omega. Qed.

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

Require Import Ynot.
Require Import Array.
Require Import UnionFind.
Require Import EqDec.

Instance equiv_dec_eqdec A `(EquivDec.EqDec A Logic.eq) : EqDec A.
Proof. auto. Defined.

Section prevof.

  (* Equations(nocomp) prev_of {A} `{EqDec A Logic.eq} (l : list A) (a : A) : option A := *)
  (* prev_of A eqd nil a := None ; *)
  (* prev_of A eqd (cons hd tl) a with equiv_dec hd a := *)
  (* { | left := hd_error tl ; *)
  (*   | right := prev_of tl a }. *)

  Context {A} `{EqDec A}.

  Equations(nocomp) prev_of (l : list A) (a : A) : option A :=
  prev_of nil a := None ;
  prev_of (cons hd tl) a with eq_dec hd a :=
  { | left := hd_error tl ;
    | right := prev_of tl a }.

End prevof.

Instance binary_be_lt_view n (x y : bits n) : PropView (binary_be_lt x y) ([: x ] < [: y]).
Proof. red. pose (binary_be_lt_is_view x y). depelim b; firstorder. elimtype False; omega. Qed.

Instance binary_be_le_view n (x y : bits n) : PropView (binary_be_le x y) ([: x ] <= [: y]).
Proof. red. pose (binary_be_le_is_view x y). depelim b; firstorder. elimtype False; omega. Qed.

Section Validator.

  Variable text_limit : int32.

  Definition instrs_array := Array.t instr [: text_limit ].
  Variable instrs : instrs_array.
  Variable instrs_fn : inhabited (fin [: text_limit ] -> instr).

  Definition instrs_valid := (instrs_fn ~~ Array.repr instrs instrs_fn)%hprop.

  Parameter decode_instr : int32 -> instr * int32.
  Definition instr_length (ip : int32) :=
    snd (decode_instr ip).

  Parameter instr_length_max : forall ip, [: instr_length ip ] < block_size.
  Parameter instr_length_pos : forall ip, [: instr_length ip ] > 0.

  Definition next_ip (ip : int32) : int32 :=
    fst (binary_plus_be ip (instr_length ip)).

  Definition iter_instr_length (ip : int32) (n : nat) :=
    iter_nat n _ next_ip ip.

  Definition instr_of (ip : int32) := fst (decode_instr ip).

  Definition valid_ip (ip : int32) :=
    exists n, ip = iter_instr_length Binary.zero n /\ 
      binary_be_le ip text_limit = true.

  Parameter ip_length : forall ip, binary_be_lt ip text_limit = true ->
    binary_be_le (next_ip ip) text_limit = true.

  Lemma next_ip_spec ip : [: next_ip ip ] = [: ip ] + [: instr_length ip ].
  Proof. unfold next_ip, instr_length.
    destruct_call_eq @binary_plus_be ip'. simpl.
    correct ip'. destruct o; simpl in *. destruct ip'.
    admit.
    auto.
  Qed.
  
  Lemma ip_lt_next (ip : int32) : [: ip ] < [: next_ip ip ].
  Proof. rewrite next_ip_spec. generalize (instr_length_pos ip). omega. Qed.
    
  Lemma iter_instr_length_lt n m : n < m -> 
    binary_be_lt (iter_instr_length Binary.zero n)
    (iter_instr_length Binary.zero m) = true.
  Proof. intros.
    induction H. unfold iter_instr_length. simpl.
    rewrite prop_view; apply ip_lt_next.
    rewrite prop_view. rewrite prop_view in IHle. 
    rewrite IHle. 
    unfold iter_instr_length at 2. simpl.
    apply ip_lt_next.
  Qed.
  
  Lemma iter_instr_length_S n : iter_instr_length Binary.zero (Datatypes.S n) = 
    next_ip (iter_instr_length Binary.zero n).
  Proof. reflexivity. Qed.

  Lemma iter_instr_length_le n m : n <= m -> 
    binary_be_le (iter_instr_length Binary.zero n)
    (iter_instr_length Binary.zero m) = true.
  Proof. intros.
    induction H. rewrite prop_view ; reflexivity. 
    rewrite iter_instr_length_S. rewrite prop_view in IHle. 
    rewrite prop_view. rewrite IHle. auto using ip_lt_next with arith.
  Qed.
  
  Lemma ip_no_between ip ip' : valid_ip ip -> valid_ip ip' ->
    [: ip ] <> [: ip' ] -> [: ip' ] < [: next_ip ip ] -> 
    [: ip' ] < [: ip ]. 
  Proof.
    intros.
    red in H, H0. repeat (dest_exists || dest_conj).
    case (compare_dec n0 n). intros.
    assert(Datatypes.S n0 <= n) by omega.
    assert([: next_ip ip ] <= [: ip']). 
    pose (iter_instr_length_le _ _ H). rewrite prop_view in e.
    rewrite iter_instr_length_S in e.
    subst ip ip'; auto.
    
    omega.
    intros ; subst. myauto.
    intros.
    subst ip ip'. rewrite <- prop_view. apply iter_instr_length_lt. auto.
  Qed.

  Lemma instr_length_mod ip : [: instr_length ip ] mod 32 = [: instr_length ip ].
  Proof. generalize (instr_length_max ip). unfold block_size. intros.
    generalize (mod_small [: instr_length ip ] 32 H). omega. 
  Qed.

  Equations(nocomp) instr_overlaps_block_size (ip : int32) : bool :=
  instr_overlaps_block_size ip := 
    negb (binary_eq (block (next_ip ip)) (block ip)
    || binary_eq (block (next_ip ip)) (next_ip ip)).

  Lemma instr_overlaps_block_size_spec (ip : int32) :
    instr_overlaps_block_size ip = false -> block ip = block (next_ip ip) \/ block (next_ip ip) = next_ip ip.
  Proof.
    funelim (instr_overlaps_block_size ip).
  Qed.

  Definition bad_indirect_control (icount : nat)
    (prev : option (int32 * instr)) (ip : int32) (i : instr) :=
    match prev with
      | None => true
      | Some (previp, previ) => 
        negb (binary_eq (block ip) (block previp)) ||
          negb (is_nacl_jmp_idiom previ i)
     end.

  Definition prev_instr (ip : int32) (sa : list int32) : option (int32 * instr) :=
    match prev_of sa ip with
      | None => None
      | Some ip => Some (ip, instr_of ip)
    end.

  Definition sa_inv limit (sa : list int32) :=
    forall ip, binary_be_lt ip limit = true -> valid_ip ip ->
      let instr := instr_of ip in
        In ip sa <-> 
        negb (instr_is_disallowed instr ||
          instr_overlaps_block_size ip ||
            (instr_is_indirect_jmp_or_call instr &&
              bad_indirect_control 0 (prev_instr ip sa) ip instr)) = true.

  Equations(nocomp) build_startaddrs_aux (ip : int32) (sa : start_addresses) (jtargets : regset) :
    (int32 * start_addresses * regset) + valid_error :=
    build_startaddrs_aux ip sa jtargets with instr_of ip :=
  | instr with instr_is_disallowed instr :=
    { | true := inr Disallowed_instruction ;
      | false with instr_overlaps_block_size ip :=
        { | true := inr Block_alignment_failure ;
          | false with instr_is_indirect_jmp_or_call instr := {
            | true with bad_indirect_control 0 None ip instr :=
              { | true := inr Bad_indirect_control;
                | false := inl (next_ip ip, ip :: sa, jtargets) } ;
            | false :=
              let jtargets := Int32Map.set ip true jtargets in
                inl (next_ip ip, ip :: sa, jtargets) } } }.

  
  Section Fixp.


    Require Import STsep.
    Require Import Separation.
    Require Import Ynot.
    Open Local Scope stsepi_scope.


    Lemma prev_instr_diff ip ip' sa : ip <> ip' ->
      prev_instr ip' (ip :: sa) = prev_instr ip' sa.
    Proof. intros. unfold prev_instr. rewrite prev_of_equation_2.
      case eq_dec; crush. 
    Qed.

    Definition is_true (b : bool) := b = true.
    Coercion is_true : bool >-> Sortclass.
    Lemma propview `{PropView b p} : b <-> p.
    Proof. unfold is_true. apply prop_view. Qed.

    Lemma eq_false_is_true b : b = false <-> negb b.
    Proof. unfold negb. destruct b; firstorder. Qed.

    Lemma binary_lt_valids ip ip' : valid_ip ip -> valid_ip ip' ->
      binary_be_lt ip' (next_ip ip) -> ip <> ip' -> binary_be_lt ip' ip.
    Proof. intros.
      pose (ip_no_between ip ip' H H0).
      case (compare_dec [: ip' ] [: ip ]); intros; auto with arith. 
      rewrite propview. auto with arith.
      rewrite propview. inject e. myauto.
      rewrite propview.
      rewrite propview in H1. auto with arith zarith.
    Qed.
      
    Lemma prop_true (P : Prop) (p : P) : P <-> True.
    Proof. split; intros; firstorder. Qed.

    Lemma iff_true (P : Prop) : (True <-> P) <-> P.
    Proof. firstorder. Qed. 

    Lemma in_spec : forall {A} (a b:A) (l:list A), In b (a :: l) <-> (a = b \/ In b l).
    Proof. auto. Qed.
      
    Definition build_start :
      forall (ip : int32) (sa : list int32) (jtargets : regset), 
        STsep (instrs_valid * hprop_inj (valid_ip ip /\ sa_inv ip sa))
        (fun res : (int32 * start_addresses * regset) + valid_error =>
          instrs_valid * hprop_inj
            match res with
              | inl (ip', sa, jt) => binary_be_lt text_limit ip' /\ sa_inv ip' sa
              | inr _ => True
            end)%hprop.
    Proof.
      refine (Fix3 _ _
        (fun self ip sa jt =>
          let next := build_startaddrs_aux ip sa jt in
          match next return next = build_startaddrs_aux ip sa jt -> _ with
            | inl (ip', sa', jt') => fun pf =>
              if dec (binary_be_lt text_limit ip') then
                {{Return next}}
              else
                (res <- self ip' sa' jt'; {{Return res}})
            | inr _ => fun pf => {{Return next}}
          end Logic.eq_refl)); sep fail simpl; clear self.
      apply himp_pure'. subst v. subst next.
      funelim (build_startaddrs_aux ip sa jt). 
      rewrite prop_view in _H. intuition auto. revert H0 H1 _H Heq Heq0 Heq1. clear.
      intros. rewrite propview. auto.
      intros ip' ltip' validip'.
      split. 
      case (eq_dec ip' ip). intros ->. intros.
      rewrite Heq0, Heq1, Heq. simpl. auto. 

      intros.
      simpl in H. destruct H; auto.
      rewrite prev_instr_diff; auto.
      specialize (H1 ip'). simpl in H1. rewrite <- H1; auto.
      apply binary_lt_valids; auto.

      intros. case (eq_dec ip ip'). intros. subst ip'. left; auto.

      intros. 
      pose (binary_lt_valids _ _ H0 validip' ltip' n).
      right. rewrite (H1 ip' i validip').
      rewrite <- H. rewrite prev_instr_diff; auto.

      apply himp_pure'.
      funelim (build_startaddrs_aux ip sa jt).
      split; auto. destruct H0 as [n [ Hn Hl ] ]. exists (Datatypes.S n).
      rewrite iter_instr_length_S. rewrite <- Hn.
      intuition auto. rewrite prop_view. rewrite prop_view in Hl.
      rewrite eq_false_is_true in _H. rewrite propview in _H. omega.
      rewrite eq_false_is_true in _H. rewrite propview in _H. 
      intros ip' ltip' validip'.
      rewrite prop_view in ltip'. 
      case (eq_dec ip ip'). intros <-.
      rewrite (prop_true _ (in_eq ip sa)). 

      rewrite iff_true.
      rewrite Heq, Heq0, Heq1. simpl. auto.
      
      intros. rewrite prev_instr_diff; auto.
      rewrite in_spec.

      Lemma elim_p {P Q : Prop} : ~ P -> (P \/ Q <-> Q).
      Proof. firstorder. Qed.

      rewrite (elim_p n). apply (H1 ip'); auto. rewrite prop_view.

      red in n; implify n. 
      

setoid_rewrite n.
      Lemma 

      pose (in_inv ip sa).


      
            
      
      
      _H.
      rewrite prop

Lemma negb_inv b : negb b = false <-> b = true.
Proof. destruct b; firstorder. Qed.

rewrite prop_view in _H.
          


        Inductive ip_chain : int32 -> int32 -> Prop :=
        | ip_chain_start : forall i : nat, ip_chain Binary.zero (next_ip Binary.zero)
        | ip_chain_next : forall i j, ip_chain i j -> ip_chain i (next_ip j).

        


        subst ip ip'.
        unfold next_ip in H1. simpl.

        intros ->; auto with arith.
 
        subst ip ip'.
        

        rewrite prop_view in H1.
      


      
      
      unfold prev_instr. 
      rewrite prev_of_equation_2. rewrite eq_dec_refl. 
      rewrite (prev_of_helper_1_equation_1 _ _ ip Logic.eq_refl). 
      destruct sa. simpl. rewrite _H in H.
      simp instr_overlaps_block_size in Heq0. 
      rewrite Have.negb_inv, prop_view in Heq0.
      

simpl. unfold bad_indirect_control. simpl.


    
    Variable self : build_start_ty.
    
    Definition 

                    {{self ip' sa jtargets}} } } }.
  
Print sumbool. 

  Next Obligation. admit. Defined.
  Next Obligation. admit. Defined.
  Next Obligation. admit. Defined.

  (* Lemma eq_block_valid p : block p = p -> valid_ip p. *)
  (* Proof.  *)
  (*   intros bp. apply (f_equal nat_of_binary_be) in bp. *)
  (*   red. rewrite block_spec in bp. *)
  (*   assert(forall x, x mod 32 <= x). *)
  (*   intro. rewrite mod_le by auto. auto. *)
  (*   assert([: p] mod 32 = 0). specialize (H [: p]). omega. *)
  (*   pose (nat_of_binary_be_inj). implify e.  *)
  (*   setoid_rewrite <- (e _ p). clear e.  *)
  (*   pose (f_equal (nat_of_binary_be (t:=32))). *)

  (* Admitted. *)
  
  Definition start_address_inv sa ip :=
    valid_ip ip /\
    (forall addr, In addr sa -> valid_ip addr) /\
    forall addr,
      binary_be_lt addr ip = true ->
      block addr = addr -> In addr sa.

  Lemma next_ip_iter_instr_length n : next_ip (iter_instr_length Binary.zero n) = 
    iter_instr_length Binary.zero (1 + n).
  Proof. simpl. unfold next_ip. apply nat_of_binary_be_inj.
    simp binary.
  Qed.

  Lemma build_startaddrs_inv (ip : int32) (jtargets : regset) (sa : start_addresses) 
    (prev instrs : list instr) : forall jtargets' sas ip',
    build_startaddrs ip jtargets sa prev instrs = inl (jtargets', sas, ip') ->
    start_address_inv sa ip ->
    start_address_inv sas ip'.
  Proof. clear text_limit. 
    funelim (build_startaddrs ip jtargets sa prev instrs).
    specialize (H _ _ _ H0). apply H; clear H.
    destruct H1 as ((n & ipiter) & H1iter & H1in).
    split.
      exists (Datatypes.S n). unfold iter_instr_length in *. simpl. now rewrite <- ipiter.

      split. intros.
        destruct H. subst. eauto. 
        apply H1iter; auto.

        (* destruct (binary_be_lt_is_view addr (next_ip ip)). clear addrlt. *)
        apply instr_overlaps_block_size_spec in Heq0.
        destruct Heq0.
        rewrite next_ip_iter_instr_length in H1. simpl in H1.


 
        apply (f_equal nat_of_binary_be) in H1.
        rewrite 2 block_spec in H1.
        intro addr_on_bound.
        case_eq (binary_be_lt addr ip). 
        intros.
        right. auto.
        intros.
        pose (binary_be_lt_is_view addr ip). rewrite H2 in b. depelim b.
        left. 
        apply nat_of_binary_be_inj.
        rewrite le_lt_or_eq_iff in H3. destruct H3; auto.
        apply (f_equal nat_of_binary_be) in addr_on_bound.
        setoid_rewrite block_spec in addr_on_bound.
        
        rewrite Hip' in Heq0.
        
        rewrite <- block_spec in Heq0.
        
        destruct H2. reflexivity.
        
        


        apply antisymmetry. auto.
        

        
        
        
    
    
    
    


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
    destruct (binary_be_lt_is_view addr (fst (binary_plus_be ip (instr_length ip)))). clear H2.
    destruct_call_eq @binary_plus_be Hip'. clear H1 H0.
    correct Hip'. simpl in Hip'.
    apply instr_overlaps_block_size_spec in Heq0.
    destruct o. admit. 
    simpl in H4. rewrite Hip' in H4. clear Hip'.
    
    simpl in *.
    
    
    

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
  