Require Import Omega.

Class Have (P : Prop) := have : P.

Hint Extern 4 (Have ?P) => unfold Have in * ; omega : typeclass_instances.

Ltac unhave := unfold Have in *.
