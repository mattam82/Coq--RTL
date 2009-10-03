Require Import CSDL.Binary CSDL.Representable CSDL.csdl.

Program Definition i : space := 
 {| space_name := "control/status registers";
    space_address := 3;
    space_cell_size := 32;
    space_n := Some (existT _ 6 (representation 3 6))
 |}.

About exp.
About eval_exp.
Definition sharp (s : space) {n} (e : exp n) : loc n := 
  

Definition loc1 := $i[0].


  

  
