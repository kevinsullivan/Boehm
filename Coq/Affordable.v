Require Export System.
Require Export MissionEffective.
Require Export Efficient.

(** Affordable *)
(**
[Affordability] is a composite attribute of [MissionEffective] and [Efficient].
A system is [Affordable] only if it meets the requirements of both [MissionEffective] and [Efficient].
*) 

Inductive Affordable (sys_type: SystemType): Prop :=
  satisfiesAffordabilityPrerequisites:
    MissionEffective sys_type ->
    Efficient sys_type ->
    Affordable sys_type.