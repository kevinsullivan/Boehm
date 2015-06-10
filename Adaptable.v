(** Adaptable General Theory *)

(**
In Boehm's taxonomy, adaptable means that a system can change its
state or behavior (and maybe in the future its structure) to improve its
fitness for purpose. Adapable here really means self-adapting.
*)
Require Export System.

Inductive Adaptable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesAdaptabilityRequirement:
    (exists adaptable: System msys -> Prop, adaptable sys) -> Adaptable sys.
