Require Export System.
Require Export Cost.
Require Export Duration.
Require Export KeyPersonnel.
Require Export OtherScarceResources.
Require Export Manufacturable.
Require Export Sustainable.

Inductive Efficient (sys_type: SystemType) : Prop :=
  satisfiesEfficiencyPrerequisites:
    Cost sys_type ->
    Duration sys_type ->
    KeyPersonnel sys_type ->
    OtherScarceResources sys_type ->
    Manufacturable sys_type ->
    Sustainable sys_type ->
    Efficient sys_type.