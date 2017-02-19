Require Export System.
Require Export Secure.
Require Export Safe.
Require Export Reliable.
Require Export Maintainable.
Require Export Available.
Require Export Survivable.
Require Export Robust.

(** Dependable *)
(**
[Dependable] is a composite attribute of [Security], [Safety], [Reliability], ..., and [Robustness].

Informally, 
An instance of type [SystemType] is deemed [Dependable] 
if and only if all the requirements of its sub-attributes are satisfied given the same conditions.
 *)

Inductive Dependable (sys_type: SystemType) : Prop :=
  satisfiesDependabilityPrerequisites:
    Secure sys_type ->
    Safe sys_type ->
    Reliable sys_type ->
    Maintainable sys_type ->
    Available sys_type ->
    Survivable sys_type ->
    Robust sys_type ->
    Dependable sys_type.