Require Import CSDL.Basics CSDL.Binary String.
 (* Program Equations Bvector List Arith Euclid Omega. *)

Definition ty := nat.
Definition const := bits.

Fixpoint type_of_op (l : list ty) (t : ty) :=
  match l with
    | nil => const t
    | t' :: l' => const t' -> type_of_op l' t
  end.

Inductive operator (l : list ty) (t : ty) : Set :=
| OP (op : type_of_op l t).
  
(* Class Operator (A : Type) (a : A) := *)
(*   { args : list ty ; *)
(*     res *)

Inductive endianness := BigEndian | LittleEndian.

Record space := mkSpace {
  space_n : option nat;
  space_address : ty;
  space_cell_size : ty;
  space_cell_size_pos : Have (space_cell_size > 0)
}.

Existing Instance space_cell_size_pos.
  
(* Variable space : Π (number : option nat) (addressing : ty) (size : ty), Set. *)

Inductive loc (n : ty) : Set := LOC (b : bits n).

Variable cells : nat -> Set. 

(* Record cells (t : ty) := CELLS  *)
(*   { cell_num : option nat; *)
(*     cell_adressing : ty; *)
(*     (* cell_start: loc a; *) *)
(*     cell_space : space cell_num cell_adressing t }. *)

Definition lift_const {t : ty} (c : nat) `{r : Representable t c} : const t :=
  representation t c.

(* Instance: Have (w > n) -> Have (w > 0). *)
(* Proof. unfold Have ; intros ; omega. Qed. *)

(* Goal Have (2 > 0). *)
(*   progress eapply @Have_instance_0. *)
(*   progress eapply @Have_instance_0. *)
(*   progress eapply @Have_instance_0. *)
(*   progress eapply @Have_instance_0. *)
(*   progress eapply @Have_instance_0. *)




Inductive exp : ty -> Set :=
| CONST {n : ty} (c : const n) : exp n
| FETCH {n : ty} (l : location n) : exp n
| APP {l n} (o : operator l n) (args : args l) : exp n

with args : list ty -> Set :=
| ARGnil : args []
| ARGcons {ty tys} : exp ty -> args tys -> args (ty :: tys)

with location : ty -> Set :=
| AGG {w} (b : endianness) (s : space) (e : exp s.(space_address))
  `{wgtn : Have (w > s.(space_cell_size))}
  `{wmultn : Have (modulo_nat w s.(space_cell_size) = 0)} : location w.

(* with location : ty -> Set := *)
(* | AGG {n w} (b : endianness) (c : cell n) `{wgtn : Have (w > n)} `{Have (n > 0)} *)
(*   `{wmultn : Have (modulo_nat w n = 0)} : location w *)

(* with cell : ty -> Set := *)
(* | CELL (s : space) (e : exp s.(space_address)) : cell s.(space_cell_size). *)

Inductive effect : Set :=
| STORE {n} (dst : location n) (src : exp n)
| KILL {n} (l : location n).

Inductive guarded : Set :=
| GUARD {n} (e : exp n) (ef : effect).

Definition rtl := list guarded.

Definition cell_name := string.

Definition space_descr (sp : space) :=
  const sp.(space_address) -> forall agg : nat, option (bits (agg * sp.(space_cell_size))).

Record mem := mkMem {
  mem_cell_fetches: forall (sp : space), space_descr sp
}.

Definition interpM a := mem -> (option a * mem)%type.

Definition ret {A} (x : A) : interpM A := fun s => (Some x, s).

Definition bind {A B} (x : interpM A) (y : A -> interpM B) : interpM B :=
  fun s => let (c, s') := x s in 
    match c with
      | None => (None, s')
      | Some c => y c s'
    end.

Axiom cheat : Π {α}, α.


Notation " ( x &? ) " := (exist _ x _).

Notation " ( x & p ) " := (existT _ x p).

Definition mem_cell_fetches_agg {w} (m : mem) (e : endianness) (sp : space) (e : const sp.(space_address)) 
  `(wgtn : Have (w > sp.(space_cell_size))) `(Have (sp.(space_cell_size) > 0)) 
  `(wmultn : Have (modulo_nat w sp.(space_cell_size) = 0)) : 
  option (const w).
  intros.
  pose (fetch := mem_cell_fetches m sp).
  unfold space_descr in fetch.
  set (q := quotient_nat w (space_cell_size sp)).
  pose (fetch e0 q).
  subst q. 
  rewrite quotient_cancel in o. exact o.
  assumption.
Defined.
  
Fixpoint eval_fetch {n} (l : location n) : interpM (const n) :=
  match l in location n return interpM (const n) with
    | AGG w endian sp e wgtn wmultn =>
      bind (eval_exp e) (fun (c : const sp.(space_address)) mem =>
        (mem_cell_fetches_agg mem endian sp c wgtn _ wmultn, mem))
  end

with eval_exp {n} (e : exp n) : interpM (const n) :=
  match e with
    | CONST n c => ret c
    | FETCH n l => eval_fetch l
    | APP l n o es => 
      let 'OP f := o in
        (fix aux l (es : args l) : type_of_op l n -> interpM (const n) :=
          match es in args l return type_of_op l n -> interpM (const n) with
            | ARGnil => fun op => ret op
            | ARGcons ty tys e es => fun op => 
              bind (eval_exp e) (fun e' =>
                aux tys es (op e'))
          end) l es f
  end.

Definition eval_app {n : ty} {l : list ty} (es : args l) : type_of_op l n -> interpM (const n) :=
  (fix aux l (es : args l) : type_of_op l n -> interpM (const n) :=
  match es in args l return type_of_op l n -> interpM (const n) with
    | ARGnil => fun op => ret op
    | ARGcons ty tys e es => fun op => 
      bind (eval_exp e) (fun e' => aux tys es (op e'))
  end) l es.

Lemma eval_exp_const n (c : const n) : eval_exp (CONST c) = ret c.
Proof. trivial. Qed.

Lemma eval_exp_fetch n (l : location n) : eval_exp (FETCH l) = eval_fetch l.
Proof. trivial. Qed.

Lemma eval_fetch_agg {w} (endian : endianness) (sp : space) e wgtn wmultn :
  eval_fetch (@AGG w endian sp e wgtn wmultn) =
  bind (eval_exp e) (fun (c : const sp.(space_address)) mem =>
    (mem_cell_fetches_agg mem endian sp c wgtn _ wmultn, mem)).
Proof. trivial. Qed.

Lemma eval_exp_app {l : list ty} {n : ty} (o : type_of_op l n) (es : args l) :
  eval_exp (APP (OP l n o) es) = eval_app es o.
Proof. intros. simpl. unfold eval_app. trivial. Qed.

Lemma eval_app_nil {n : ty} (o : type_of_op nil n) : eval_app ARGnil o = ret o.
Proof. intros. trivial. Qed.

Lemma eval_app_cons {t : ty} {l : list ty} (e : exp t) (es : args l) {n : ty} (o : type_of_op (t :: l) n) : 
  eval_app (ARGcons e es) o = bind (eval_exp e) (fun e' => eval_app es (o e')).
Proof. intros. trivial. Qed.

Equations(nocomp) binary_eq {n} (x y : const n) : bool :=
binary_eq ?(0) Vnil Vnil := true ;
binary_eq ?(S n) (Vcons a n x) (Vcons b n y) := bool_eq a b && binary_eq x y.

(* Equations(nocomp) binary_eq {n} (x y : const n) : { x = y } + { x <> y } := *)
(* binary_eq ?(0) Vnil Vnil := left eq_refl ; *)
(* binary_eq ?(S n) (Vcons true n x) (Vcons true n y) := if binary_eq x y then in_left else in_right ; *)
(* binary_eq ?(S n) (Vcons false n x) (Vcons false n y) := if binary_eq x y then in_left else in_right ; *)
(* binary_eq ?(S n) (Vcons a n _) (Vcons b n _) := in_right. *)

Require Import EquivDec Bool.
Instance space_eq : EqDec space eq.
Admitted.

Lemma bool_eq_refl b : bool_eq b b = true.
Proof. destruct b ; reflexivity. Qed.

Lemma binary_eq_refl n (b : const n) : binary_eq b b = true.
Proof. intros. remember b as b'. rewrite Heqb' at 1. funind (binary_eq b b') foo. 
  rewrite bool_eq_refl. rewrite IHbinary_eq_ind. reflexivity.
  simp binary_eq in foo. rewrite bool_eq_refl in foo. assumption.
Qed.

Instance const_eq : EqDec (const n) eq.
Proof. 
intros n. red. intros. case_eq (binary_eq x y) ; [ left | right ].

  funind (binary_eq x y) foo. reflexivity.
  red. rewrite andb_true_iff in x. destruct x.
  specialize (IHbinary_eq_ind H1).
  apply bool_eq_ok in H. subst.
  simp binary_eq in foo. rewrite bool_eq_refl in foo. 
  specialize (IHbinary_eq_ind foo). congruence.

  funind (binary_eq x y) foo. red ; intros.
  red in H. noconf H. simp binary_eq in foo.
  rewrite bool_eq_refl, binary_eq_refl in foo.
  simpl in foo. discriminate.
Qed.
  
Definition coerce_bits {n m} (c : bits n) (H : n = m) : bits m.
Proof. intros ; subst. exact c. Defined.

Equations(nocomp) vector_firstn {A} {l : nat} (s : nat) (c : vector A l) (Hsl : s < l) : vector A s :=
vector_firstn A ?(O) s Vnil Hsl :=! Hsl ;
vector_firstn A ?(S n) O (Vcons a n v) Hsl := Vnil ;
vector_firstn A ?(S n) (S m) (Vcons a n v) Hsl := Vcons a (vector_firstn m v _).

  Next Obligation. omega. Defined.

  Next Obligation. revert s Hsl ; induction c ; intros ;
    simp vector_firstn ; auto with * ; destruct s ; simp vector_firstn.
  Defined.

Require Import Morphisms SetoidTactics.
  
Definition mem_cell_store_agg {w} (m : mem) (e : endianness) (sp : space) (addr : const sp.(space_address)) 
  (c : option (const w))
  `{wgtn : Have (w > sp.(space_cell_size))} `{Have (sp.(space_cell_size) > 0)}
  `{wmultn : Have (modulo_nat w sp.(space_cell_size) = 0)} : mem.
  intros.
  pose (fetch := mem_cell_fetches m sp).
  unfold space_descr in fetch.
  set (q := quotient_nat w (space_cell_size sp)).
  constructor.
  intros sp' addr' agg.
  destruct_equiv sp sp'.

    destruct_equiv addr addr'.
    
      destruct (compare_dec agg q).

      (* LT *) assert(Haggw:agg * sp'.(space_cell_size) < w).
      subst q. replace w with (quotient_nat w sp'.(space_cell_size) * sp'.(space_cell_size)).
      unfold Have in *. now apply mult_lt_compat. now rewrite quotient_cancel.
      destruct c.
        exact (Some (vector_firstn _ c Haggw)).
        exact None.

      (* EQ *)
      subst agg q. rewrite quotient_cancel. exact c.
      assumption.

      (* GT *)
      set(w' := agg * sp'.(space_cell_size)).
      pose (@mem_cell_fetches_agg w' m BigEndian sp' addr').
      exploit o. clear o. subst w'. unhave. red. 
      assert(q > 1). subst q. now apply quotient_gt_1.
      red in H0. rewrite l in H0. 
      setoid_replace sp'.(space_cell_size) with (1 * sp'.(space_cell_size)) at 1; [| unfold ty; omega].
      now apply mult_lt_compat.
      
      subst w'. rewrite modulo_cancel. reflexivity. 
      intros cst. exact cst.

      (** Addresses don't match, but may still be part of the aggregate! *)
      apply (fetch addr' agg).

      apply (mem_cell_fetches m sp' addr' agg).
Defined.
  
Equations eval_store {n} (l : location n) (c : option (const n)) : interpM () :=
eval_store n (AGG w endian sp e wgtn wmultn) c := 
  bind (eval_exp e) (fun e' =>
    fun mem => (Some (), mem_cell_store_agg mem endian sp e' c)).

Equations(nocomp) apply_effect (e : effect) : interpM () := 
apply_effect (STORE n dst src) :=
  bind (eval_exp src) (fun e' => eval_store dst (Some e')) ;
apply_effect (KILL n l) := eval_store l None.

Definition one_binary_le {n : nat} : const n := 
  fst (bits_succ _ (constant_vector n false)).
    
Definition one_guarded (g : guarded) : interpM () :=
  let 'GUARD n e ef := g in
    bind (eval_exp e) 
    (fun e' => 
      if binary_eq e' one_binary_le then
        apply_effect ef
       else ret ()).

Definition seq (x y : interpM ()) :=
  bind x (Basics.const y).

Definition eval_rtl (r : rtl) : interpM () :=
  fold_left (fun acc g => seq acc (one_guarded g)) r (ret ()).







