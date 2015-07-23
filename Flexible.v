Require Export System.
Require Export Modifiable.
Require Export Tailorable.
Require Export Adaptable.

Inductive Flexible (sys_type: SystemType)
: Prop :=
  satisfiesFlexibilityPrerequisites:
    Modifiable sys_type ->
    Tailorable sys_type ->
    Adaptable sys_type ->
    Flexible sys_type.