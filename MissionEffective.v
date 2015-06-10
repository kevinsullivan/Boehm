(** * MissionEffective General Theory *)

(**
Kevin Sullivan, Koleman Nix, Chong Tang, Ke Dou
with Donna Rhodes, Barry Boehm, and Adam Ross

March, 2015
*)

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

Inductive MissionEffective {msys: MetaSystem} (sys: System msys): Prop :=
  isMissionEffective:
    PhysicalCapable sys ->
    CyberCapable sys ->
    HumanUsable sys ->
    Speed sys ->
    Endurable sys ->
    Maneuverable sys ->
    Accurate sys ->
    Impactful sys ->
    Scalable sys ->
    Versatile sys ->
    Interoperable sys ->
    MissionEffective sys.
