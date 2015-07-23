Require Export System.
Require Export Secure.
Require Export Safe.
Require Export Reliable.
Require Export Maintainable.
Require Export Available.
Require Export Survivable.
Require Export Robust.

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