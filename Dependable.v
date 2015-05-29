(** ** Dependable General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes,
Barry Boehm, and Adam Ross

March, 2015
*)
(* begin hide *)
(* hidden things here *)
(* end hide *)

Require Export Secure.
Require Export Safe.
Require Export Reliable.
Require Export Maintainable.
Require Export Available.
Require Export Survivable.
Require Export Robust.

(**
[Dependable] is a composite attribute of [Security], [Safety], [Reliability], ..., and [Robustness].

Informally, 
A system [sys] belonging to the set of systems [System] is deemed [Dependable] given the set of contexts [Context]
and phases [Phase] if and only if all the requirements of its sub-attributes ([Security], [Safety], [Reliability],
..., and [Robustness]) are satisfied given the same conditions.
*)

Inductive Dependable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) : Prop :=
  satisfiesDependabilityPrerequisites:
    Secure System Stakeholder Context Phase sys ->
    Safe System Stakeholder Context Phase sys ->
    Reliable System Stakeholder Context Phase sys ->
    Maintainable System Stakeholder Context Phase sys ->
    Available System Stakeholder Context Phase sys ->
    Survivable System Stakeholder Context Phase sys ->
    Robust System Stakeholder Context Phase sys ->
    Dependable System Stakeholder Context Phase sys.
