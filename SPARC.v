Require Import CSDL.Binary CSDL.BinaryBe CSDL.Representable CSDL.Range CSDL.csdl.

Program Definition i : space_descr := 
 {| space_name := "control/status registers";
    space_address := 3;
    space_cell_size := 32;
    space_n := Some (existT _ 6 (representation 3 6))
 |}.

  Next Obligation. unhave; omega. Defined.

About exp.
About eval_exp.
About mem_cell_fetch.
Definition sharp (s : space_descr) (e : exp (s.(space_address))) : interpM (loc s) := 
  eval_exp e.
    
Delimit Scope exp_scope with exp.

Notation " # s [ e ] " := (sharp s e%exp) (s ident).

Notation "0" := zero : exp_scope.
Notation "1" := one : exp_scope.

Coercion CONST : const >-> exp.

Definition bits_const {n} (b : bits n) : exp n :=
  CONST b.

Coercion bits_const : bits >-> exp.

About representation_range.

Definition loc1 := #i[0].
Definition loc2 := #i[1].

Definition loc12 := #i[representation_range (range_of_bounds 0 1) _].

Print loc1.


  

  
