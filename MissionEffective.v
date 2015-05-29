(** * MissionEffective General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes,
Barry Boehm, and Adam Ross

March, 2015
*)

Add Rec LoadPath "./ContributeQA".

Require Export PhysicalCapable.
Require Export CyberCapable.
Require Export HumanUsable.
Require Export Speed.
Require Export Endurable.
Require Export Maneuverable.
Require Export Accurate.
Require Export Impact.
Require Export Scalable.
Require Export Versatile.
Require Export Interoperable.

(** ** Mission Effective **)

(**
In the following definition, [MissionEffective] is parameterized by three typeclasses,
[System], [Stakeholder], and [Context], a system, sys, of type [System], and sevaral ternary
relations over [System], [Context], and/or [Stakeholder].
Those ternary relations are associated with its sub-attributes. For example, physicalCapability is a ternary relation,
which is to say, a set of triples, (s, sh, c), between a system, s, a stakeholder, sh, and a context, c,
that we expect to hold (for the proposition to be provable, iff system s satisfies its mission effective
requirement (which isn't represented explicitly here) in context, c.)

Its definition indicates that the property of a [System] being [MissionEffective] for all [Contexts], the system is
mission effective implicitly for all [Stakeholders] in those [Contexts], only if all the requirements of the subattributes
are satisfied.
*)

Inductive MissionEffective (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  isMissionEffective:
    PhysicalCapable System Stakeholder Context Phase sys ->
    CyberCapable System Stakeholder Context Phase sys ->
    HumanUsable System Stakeholder Context Phase sys ->
    Speed System Stakeholder Context Phase sys ->
    Endurable System Stakeholder Context Phase sys ->
    Maneuverable System Stakeholder Context Phase sys ->
    Accurate System Stakeholder Context Phase sys ->
    Impact System Stakeholder Context Phase sys ->
    Scalable System Stakeholder Context Phase sys ->
    Versatile System Stakeholder Context Phase sys ->
    Interoperable System Stakeholder Context Phase sys ->
    MissionEffective System Stakeholder Context Phase sys.
