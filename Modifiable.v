(** Modifiable General Theory *)

(**
In Boehm's taxonomy, modifiable means that someone can change the
system structure or state can be changed to meet new needs.
*)
Require Export System.

Inductive Modifiable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesModifiabilityRequirement:
    (exists modifiable: System msys -> Prop, modifiable sys) -> Modifiable sys.
