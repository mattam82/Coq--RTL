Require Import CSDL.Basics CSDL.Binary String.
 (* Program Equations Bvector List Arith Euclid Omega. *)

Definition ty := nat.
Definition const := bits.
Variable operator : list ty -> ty -> Set.

(* Class Operator (A : Type) (a : A) := *)
(*   { args : list ty ; *)
(*     res *)

Inductive endianness := BigEndian | LittleEndian.

Variable space : Π (number : option nat) (addressing : ty) (size : ty), Set.
Inductive loc (n : ty) : Set := LOC (b : bits n).

Variable cells : nat -> Set. 

(* Record cells (t : ty) := CELLS  *)
(*   { cell_num : option nat; *)
(*     cell_adressing : ty; *)
(*     (* cell_start: loc a; *) *)
(*     cell_space : space cell_num cell_adressing t }. *)

Definition lift_const {t : ty} (c : nat) `{r : Representable t c} : const t :=
  representation t c.

Instance: Have (w > n) -> Have (w > 0).
Proof. unfold Have ; intros ; omega. Qed.

Inductive exp : ty -> Set :=
| CONST {n : ty} (c : const n) : exp n
| FETCH {n : ty} (l : location n) : exp n
| APP {l n} (o : operator l n) (args : args l) : exp n

with args : list ty -> Set :=
| ARGnil : args []
| ARGcons {ty tys} : exp ty -> args tys -> args (ty :: tys)

with location : ty -> Set :=
| AGG {n w} (b : endianness) (c : cell n) `{wgtn : Have (w > n)} `{wmultn : Have (modulo_nat w n = 0)} : location w

with cell : ty -> Set :=
| CELL {n a m} (s : space n a m) (e : exp a) : cell m.

Inductive effect : Set :=
| STORE {n} (dst : location n) (src : exp n)
| KILL {n} (l : location n).

Inductive guarded : Set :=
| GUARD {n} (e : exp n) (ef : effect).

Inductive rtl := RTL (l : list guarded).

Definition cell_name := string.

Definition space_descr (locations : ty) (size : ty) :=
  forall (t : ty), const locations -> option (bits t).

Record mem := {
  mem_cell_fetches: forall {n a m} (sp : space n a m), space_descr a m
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

Fixpoint eval_fetch {n} (l : location n) : interpM (const n) :=
  match l with
    AGG n w endian (CELL num addr n' sp e) wgtn wmultn =>
    bind (eval_exp e) (fun (c : const addr) mem =>
      (mem_cell_fetches mem sp w c, mem))
  end

with eval_exp {n} (e : exp n) : interpM (const n) :=
  match e with
    | CONST n c => ret c
    | FETCH n l => eval_fetch l
    | APP l n o args => 
      fix aux (args : args l) (op :  :=
      match args with
        | ARGnil => 
| ARGcons {ty tys} : exp ty -> args tys -> args (ty :: tys)
      map (eval_exp 

  end.

(* Equations(nocomp) eval_fetch {n} (l : location n) : interpM (const n) := *)
(* eval_fetch w (AGG n w e (CELL num addr n sp e) wgtn wmultn) := *)
(*   bind (eval_exp e) (fun (c : const addr) mem => *)
(*     (mem_cell_fetches mem sp c w, mem)). *)

Equations(nocomp) eval_exp {n} (e : exp n) : interpM (const n) :=
eval_exp n (CONST n c) := ret c ;
eval_exp n (FETCH n l) := fetch l ;
eval_exp n (APP l n o args) := cheat.

  

Definition one_guarded (g : guarded) : interpM () :=
  let 'GUARD n e ef := g in
    if eval_exp e = true then
      apply_effect ef
    else ret ().





