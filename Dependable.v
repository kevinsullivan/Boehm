(** ** Dependable General Theory *)

(**
Kevin Sullivan, Koleman Nix, Chong Tang, Ke Dou
with Donna Rhodes, Barry Boehm, and Adam Ross

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

Inductive Dependable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesDependabilityPrerequisites:
    Secure sys ->
    Safe sys ->
    Reliable sys ->
    Maintainable sys ->
    Available sys ->
    Survivable sys ->
    Robust sys ->
    Dependable sys.
