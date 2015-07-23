Require Export System.
Require Export Dependable.
Require Export Flexible.
Require Export Changeable.

Inductive Resilient (sys_type: SystemType)
: Prop :=
  satisfiesResiliencyPrerequisites:
    Dependable sys_type ->
    Flexible sys_type ->
    Changeable sys_type ->
    Resilient sys_type.
