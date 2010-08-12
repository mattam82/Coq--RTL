Require Import List.
Require Import CSDL.Basics Vector Fin.

Equations(nocomp) fin_inj {n} (f : fin n) : fin (S n) :=
fin_inj ?(S n) fz := fz ;
fin_inj ?(S n) (fs f) := fs (fin_inj f).

Equations(nocomp) finle_dec {n} (f f' : fin n) : bool * fin n :=
finle_dec ?(S n) fz diff := (true, diff) ;
finle_dec ?(S n) f fz := (false, f) ;
finle_dec ?(S n) (fs f) (fs f') <= finle_dec f f' =>
  { | pair b f := (b, fs f) }.

(* Equations(nocomp) add_fin {n} (f : fin n) (m : nat) : fin n := *)
(* fin_add ?(S n) fz n := gof n; *)
(* fin_add ?(S n) (fs f) f' := fs (fin_add f f'). *)

Definition range n := list (fin n).

(* Equations(nocomp) vector_of_list {A} (l : list A) : vector A (length l) := *)
(* vector_of_list A nil := Vnil ; *)
(* vector_of_list A (cons x l) := Vcons x (vector_of_list l). *)

(* Definition apply_range {A n} (r : range n) (v : vector A n) : vector A (length r) := *)
(*   vector_of_list (map (nth v : fin n -> A) r). *)


Equations(nocomp) apply_range {A n} (r : range n) (v : vector A n) : vector A (length r) :=
apply_range A n nil v := Vnil ;
apply_range A n (cons f r) v := Vcons (nth v f) (apply_range r v).

Equations(nocomp) fin_of_nat n (m : nat) : option (fin n) :=
fin_of_nat O m := None ;
fin_of_nat (S n) O := Some fz ;
fin_of_nat (S n) (S m) <= fin_of_nat n m => 
  { | None := None ;
    | Some f := Some (fs f) }.

Require Import Representable.

Check (representation 5 3).

Definition range_0 {n : nat} : range (4 + n) := [fs (fs fz); fz].
Transparent fin_of_nat.
Transparent apply_range.
Print Assumptions nth. 
Eval compute in apply_range range_0 (representation 5 5).

Fixpoint maybe_list_maybe {A} (l : list (option A)) : option (list A) :=
  match l with
    | [] => Some []
    | None :: tl => None
    | Some x :: tl => match maybe_list_maybe tl with
                        | Some tl' => Some (x :: tl')
                        | None => None
                      end
  end.

(* Definition map_maybe {A} (l : list A) (f : A -> option B) : option (list B) := *)
(*   maybe_list_maybe (map f l). *)

Definition range_of_nats (l : list nat) (size : nat) : option (range size) :=
  maybe_list_maybe (map (fin_of_nat size) l).

Open Scope nat_scope.

Eval compute in (range_of_nats [1; 4; 5] 6).

Inductive Compare : nat -> nat -> Set :=
  isLt : forall x y, Compare x (x + S y)
| isEq : forall x, Compare x x
| isGt : forall x y, Compare (y + S x) y.

Equations(nocomp) compare (m n : nat) : Compare m n :=
compare O O := isEq O ;
compare O (S n) := isLt O n ;
compare (S m) O := isGt m O ;
compare (S m) (S n) <= compare m n => {
  compare (S ?(x)) (S ?(x + S y)) (isLt x y) := isLt (S x) y ;
  compare (S ?(x)) (S ?(x)) (isEq x) := isEq (S x) ;
  compare (S ?(y + S x)) (S ?(y)) (isGt x y) := isGt x (S y) }.

Equations(nocomp) list_of_nat (m : nat) : list nat :=
list_of_nat 0 := [0];
list_of_nat (S n) := S n :: list_of_nat n.

Equations(nocomp) range_of_bounds (m n : nat) : list nat :=
range_of_bounds m n with compare m n := {
  | isLt x diff := map (plus x) (rev (list_of_nat (S diff))) ;
  | isEq x := [] ;
  | isGt diff x := map (plus x) (list_of_nat (S diff)) }.
    
Transparent compare list_of_nat range_of_bounds.

Class RepresentableRange (l : list nat) (size : nat) := mkRepresentableRange {
  range_repr : range size }.

Ltac build_range l s :=
  let repr := eval compute in (range_of_nats l s) in
    match repr with
      | None => fail 2 "Invalid range: " l
      | Some ?r => exact (mkRepresentableRange l s r)
    end.

Hint Extern 0 (RepresentableRange ?l ?s) => build_range l s : typeclass_instances.

Definition representation_range (l : list nat) (size : nat) `{RepresentableRange l size} := 
  range_repr.

Eval compute in range_of_nats [4;5] 7.
Eval compute in range_of_nats [5;4] 7.
Eval compute in (representation_range [4; 5] 7).
Eval compute in (representation_range [5; 4] 7).

Eval compute in apply_range (representation_range (range_of_bounds 2 3) _) 
  (representation 6 1).
