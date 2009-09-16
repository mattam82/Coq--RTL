Require Export Program Equations Have.

Hint Extern 4 => discriminates : core.

Ltac simpdep := reverse ; simplify_dep_elim ; simplify_IH_hyps.
