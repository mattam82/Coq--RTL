Require Import Omega.

Class Have (P : Prop) := have : P.

Ltac unhave := unfold Have in *.

Hint Extern 4 (Have ?P) => unhave ; omega : typeclass_instances.

