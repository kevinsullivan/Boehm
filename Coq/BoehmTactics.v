(**
A Ltac tactic for reducing the proofs to just one line each.
*)

Ltac Prove_satisfaction requirements context phase stakeholder := constructor; exists requirements; intros; destruct context, phase, stakeholder; auto.
