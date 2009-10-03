Require Import CSDL.Basics CSDL.Binary CSDL.BinaryBe String.
Require Import EquivDec Bool SetoidTactics.

Definition ty := nat.
Definition const := bits.

Fixpoint operator (l : list ty) (t : ty) :=
  match l with
    | nil => const t
    | t' :: l' => const t' -> operator l' t
  end.
  
Record space_descr := mkSpaceDescr {
  space_name : string;
  space_address : ty;
  loc := const space_address;
  space_cell_size : ty;
  space_cell_size_pos : Have (space_cell_size > 0);
  space_n : option { num : nat & { max_addr : loc | 
    nat_of_binary_be max_addr = num } } }.

Definition space_eq (x y : space_descr) := 
  x.(space_name) = y.(space_name).

Parameter space_eq_eq : forall (x y : space_descr), space_eq x y -> x = y.

Inductive space (s : space_descr) := mkSpace {
  space_fetch : loc s -> forall agg : nat, option (const (agg * space_cell_size s)) ;
  space_store : loc s -> forall agg : nat, const (agg * space_cell_size s) -> space s
}.

Existing Instance space_cell_size_pos.

(* Definition space_descr (sp : space) := *)
(*   const sp.(space_address) -> forall agg : nat, option (bits (agg * sp.(space_cell_size))). *)

Definition aggregate := nat.
About binary_of_nat_le.

Open Local Scope nat_scope.

Definition in_space (sp : space_descr) (l : loc sp) (a : aggregate) := 
  match sp.(space_n) with
    | None => true
    | Some (existT n (exist nbin _)) => 
      match binary_of_nat_be _ (a * sp.(space_cell_size)) with
        | Some offset =>
          let '(l', b) := binary_plus_be l offset in
            if b then false
            else binary_be_le l' nbin
        | None => false
      end
  end.
      
(* Class SpaceImpl (s : space) := *)
(*   { space_fetch : const s.(space_address) ->  *)
(*       forall agg : nat, option (bits (agg * sp.(space_cell_size))). *)


Inductive exp : ty -> Set :=
| CONST {n : ty} (c : const n) : exp n
| FETCH {n : ty} (l : location n) : exp n
| APP {l n} (o : operator l n) (args : args l) : exp n

with args : list ty -> Set :=
| ARGnil : args []
| ARGcons {ty tys} : exp ty -> args tys -> args (ty :: tys)

with location : ty -> Set :=
| AGG {w} (b : endianness) (s : space_descr) (e : exp s.(space_address))
  `{wgtn : Have (w > s.(space_cell_size))}
  `{wmultn : Have (modulo_nat w s.(space_cell_size) = 0)} : location w.

Inductive effect : Set :=
| STORE {n} (dst : location n) (src : exp n)
| KILL {n} (l : location n).

Inductive guarded : Set :=
| GUARD {n} (e : exp (S n)) (ef : effect).

Definition rtl := list guarded.

Record mem := mkMem {
  mem_cell_fetches: forall (sp : space_descr), space sp
}.

Definition interpM a := mem -> (option a * mem)%type.

Definition ret {A} (x : A) : interpM A := fun s => (Some x, s).

Definition bind {A B} (x : interpM A) (y : A -> interpM B) : interpM B :=
  fun s => let (c, s') := x s in 
    match c with
      | None => (None, s')
      | Some c => y c s'
    end.

Definition seq (x y : interpM ()) :=
  bind x (Basics.const y).

Notation " ( x &? ) " := (exist _ x _).

Notation " ( x & p ) " := (existT _ x p).

Definition mem_cell_fetches_agg {w} (m : mem) (e : endianness) (sp : space_descr) (e : const sp.(space_address)) 
  `(wgtn : Have (w > sp.(space_cell_size))) `(Have (sp.(space_cell_size) > 0)) 
  `(wmultn : Have (modulo_nat w sp.(space_cell_size) = 0)) : 
  option (const w).
  intros.
  pose (fetch := space_fetch _ (mem_cell_fetches m sp)).
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
    | APP l n f es => 
      (fix aux l (es : args l) : operator l n -> interpM (const n) :=
        match es in args l return operator l n -> interpM (const n) with
          | ARGnil => fun op => ret op
          | ARGcons ty tys e es => fun op => 
            bind (eval_exp e) (fun e' =>
              aux tys es (op e'))
        end) l es f
  end.

Definition eval_app {n : ty} {l : list ty} (es : args l) : operator l n -> interpM (const n) :=
  (fix aux l (es : args l) : operator l n -> interpM (const n) :=
  match es in args l return operator l n -> interpM (const n) with
    | ARGnil => fun op => ret op
    | ARGcons ty tys e es => fun op => 
      bind (eval_exp e) (fun e' => aux tys es (op e'))
  end) l es.

Lemma eval_exp_const n (c : const n) : eval_exp (CONST c) = ret c.
Proof. trivial. Qed.

Lemma eval_exp_fetch n (l : location n) : eval_exp (FETCH l) = eval_fetch l.
Proof. trivial. Qed.

Lemma eval_fetch_agg {w} (endian : endianness) (sp : space_descr) e wgtn wmultn :
  eval_fetch (@AGG w endian sp e wgtn wmultn) =
  bind (eval_exp e) (fun (c : const sp.(space_address)) mem =>
    (mem_cell_fetches_agg mem endian sp c wgtn _ wmultn, mem)).
Proof. trivial. Qed.

Lemma eval_exp_app {l : list ty} {n : ty} (o : operator l n) (es : args l) :
  eval_exp (APP o es) = eval_app es o.
Proof. intros. simpl. unfold eval_app. trivial. Qed.

Lemma eval_app_nil {n : ty} (o : operator nil n) : eval_app ARGnil o = ret o.
Proof. intros. trivial. Qed.

Lemma eval_app_cons {t : ty} {l : list ty} (e : exp t) (es : args l) {n : ty} (o : operator (t :: l) n) : 
  eval_app (ARGcons e es) o = bind (eval_exp e) (fun e' => eval_app es (o e')).
Proof. intros. trivial. Qed.

Instance space_eq_dec : EqDec space_descr eq.
Proof. red ; intros. unfold Equivalence.equiv. 
  pose (space_eq_eq x y).
  unfold space_eq in e.
Admitted.

Definition mem_cell_store_agg {w} (m : mem) (e : endianness) (sp : space_descr) (addr : const sp.(space_address)) 
  (c : option (const w))
  `{wgtn : Have (w > sp.(space_cell_size))} `{Have (sp.(space_cell_size) > 0)}
  `{wmultn : Have (modulo_nat w sp.(space_cell_size) = 0)} : mem.
  intros.
  pose (fetch := space_fetch _ (mem_cell_fetches m sp)).
  set (q := quotient_nat w (space_cell_size sp)).
  constructor.
  intros sp'.
  destruct_equiv sp sp'.

    constructor.
    intros addr' agg.
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
      destruct (compare_dec (binary_plus_be addr (binary_of_nat agg * space_cell_size sp') addr').

      apply (fetch addr' agg).

      apply (mem_cell_fetches m sp').

      apply (mem_cell_fetches m sp').
Defined.
  
Equations eval_store {n} (l : location n) (c : option (const n)) : interpM () :=
eval_store n (AGG w endian sp e wgtn wmultn) c := 
  bind (eval_exp e) (fun e' =>
    fun mem => (Some (), mem_cell_store_agg mem endian sp e' c)).

Equations(nocomp) apply_effect (e : effect) : interpM () := 
apply_effect (STORE n dst src) :=
  bind (eval_exp src) (fun e' => eval_store dst (Some e')) ;
apply_effect (KILL n l) := eval_store l None.
    
Definition one_guarded (g : guarded) : interpM () :=
  let 'GUARD n e ef := g in
    bind (eval_exp e) 
    (fun e' => 
      if binary_eq e' one then apply_effect ef
      else ret ()).

Definition eval_rtl (r : rtl) : interpM () :=
  fold_left (fun acc g => seq acc (one_guarded g)) r (ret ()).

Definition run_interp (r : rtl) (m : mem) : mem :=
  snd (eval_rtl r m).




