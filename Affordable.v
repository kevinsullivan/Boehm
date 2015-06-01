(** ** Affordable General Theory **)
(* begin hide *)
(* hidden things here *)
(* end hide *)

Require Export MissionEffective.
Require Export Efficient.

(**
[Affordability] is a composite attribute of [MissionEffective] and [Efficient].
A system is [Affordable] only if it meets the requirements of both [MissionEffective] and [Efficient].

Informally,
A system [sys] belonging to the set of systems [System] is deemed [Affordable] for all stakeholders
in set [Stakeholder] given the set of phases and contexts [Context] and [Phase] if and only if all the
requirements of its sub-attributes ([MissionEffective], and [Efficient]) are satisfied given
the same conditions. *) 

Inductive Affordable 
            (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
          satisfiesAffordabilityPrerequisites: 
             MissionEffective System Stakeholder Context Phase sys ->
             Efficient System Stakeholder Context Phase sys ->
             Affordable System Stakeholder Context Phase sys.
