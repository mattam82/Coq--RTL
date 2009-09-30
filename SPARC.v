Require Import CSDL.Binary CSDL.csdl.

Program Definition i : space := 
 {| space_name := "control/status registers";
    space_address := 3;
    space_cell_size := 32;
    space_n := Some (existT _ 6 (representation 3 6))
 |}.



  

  
