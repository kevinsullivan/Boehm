Require Export System.
Require Export PhysicalCapable.
Require Export CyberCapable.
Require Export HumanUsable.
Require Export Speed.
Require Export Endurable.
Require Export Maneuverable.
Require Export Accurate.
Require Export Impactful.
Require Export Scalable.
Require Export Versatile.
Require Export Interoperable.

(** Mission Effective *)
(**
[MissionEffective] is parameterized by an instance of type [SystemType]. The constituent attributes of [MissionEffective] are
the things whether it can be produced and maintained in a mission effective way.

Informally, in English:
An instance of type [SystemType] is deemed [MissionEffective] 
if and only if all the requirements of its sub-attributes are satisfied given the same conditions.
*)

Inductive MissionEffective (sys_type: SystemType): Prop :=
  satisfiesMissionEffectivenessPrerequisites:
    PhysicalCapable sys_type ->
    CyberCapable sys_type ->
    HumanUsable sys_type ->
    Speed sys_type ->
    Endurable sys_type ->
    Maneuverable sys_type ->
    Accurate sys_type ->
    Impactful sys_type ->
    Scalable sys_type ->
    Versatile sys_type ->
    Interoperable sys_type ->
    MissionEffective sys_type.