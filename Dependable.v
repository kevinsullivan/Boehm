(** * Dependable General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes,
Barry Boehm, and Adam Ross

March, 2015
*)

Add Rec LoadPath "./ContributeQA".
Require Export Secure.
Require Export Safe.
Require Export Reliable.
Require Export Maintainable.
Require Export Available.
Require Export Survivable.
Require Export Robust.

(** ** DEPENDABLE**)
(**
[Dependable] is parameterized by a [System] type, a [Context] type,
an instance of type [System], and sevaral binary relations over [System] and [Context]
representing the relationship between the given [System] set, [Context] set, and some
constituent attribute. The constituent attributes of [Dependability] are
[Security], [Safety], [Reliability], ..., and [Robustness].

These binary relations represent the given system type's ability to satisfy
the specified requirement in the given context.

Informally, in English:
A system [sys] belonging to the set of systems [System] is deemed [Dependable] given the set of contexts [Context]
if and only if all the requirements of its sub-attributes ([Security], [Safety], [Reliability], ..., and [Robustness])
are satisfied given the same conditions.
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
