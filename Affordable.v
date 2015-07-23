Require Export System.
Require Export MissionEffective.
Require Export Efficient.

Inductive Affordable (sys_type: SystemType): Prop :=
  satisfiesAffordabilityPrerequisites:
    MissionEffective sys_type ->
    Efficient sys_type ->
    Affordable sys_type.