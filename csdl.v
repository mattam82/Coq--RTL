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

Inductive rtl := RTL (l : list guarded).

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

About mem_cell_fetches. Print space_descr.

Definition coerce_bits {n m} (c : bits n) (H : n = m) : bits m.
intros ; subst. exact c. Defined.

Equations mem_cell_update (m : mem) {n a w} (sp : space n a w) (e : const a) (c : const w) : mem :=
mem_cell_update (mkMem m) n a w sp e c := 
  let mem' n' a' w' (sp' : space n' a' w') (t : ty) (e' : const a') := 
    if eq_nat_dec a a' then
      if binary_eq e (coerce_bits e' _) then 
        Some (coerce_bits c _)
      else None
    else m n' a' w' sp' t e' in mkMem mem'.

  Next Obligation. Defined.
  Next Obligation.   Defined.

  
Equations eval_store {n} (l : location n) (c : const n) : interpM () :=
eval_store n (AGG n w endian (CELL num a w sp e) wgtn wmultn) := 
  bind (eval_exp e) (fun e' : const a =>
    fun mem => ((), mem_cell_update mem sp e' c))
  

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





