Require Export System.
Require Export Cost.
Require Export Duration.
Require Export KeyPersonnel.
Require Export OtherScarceResources.
Require Export Manufacturable.
Require Export Sustainable.

(** Efficient *)
(**
[Efficient] is parameterized by an instance of type [SystemType]. The constituent attributes of [Efficiency] are
the things it uses efficiently and whether it can be produced and maintained efficiently.

Informally, in English:
An instance of type [SystemType] is deemed [Efficient] 
if and only if all the requirements of its sub-attributes are satisfied given the same conditions.
 *)

Inductive Efficient (sys_type: SystemType) : Prop :=
  satisfiesEfficiencyPrerequisites:
    Cost sys_type ->
    Duration sys_type ->
    KeyPersonnel sys_type ->
    OtherScarceResources sys_type ->
    Manufacturable sys_type ->
    Sustainable sys_type ->
    Efficient sys_type.