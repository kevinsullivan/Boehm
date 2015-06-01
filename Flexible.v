(** * Flexibility General Theory *)

(**
Boehm stipulates that, " ...The three means for achieving the end parent class of 
Flexibility are Modifiability, Tailorability, and Adaptability."
*)

(**
Informally, a system [sys] of type [System] is deemed to be [Flexible] (i.e., to satisfy
its flexibility requirements) for all stakeholders, contexts, and phases, if it satisfies its
lower-level modifiability, tailorability, and adaptability requirements across this set of
parameters. 
*)

Require Export Modifiable.
Require Export Tailorable.
Require Export Adaptable.

(** ** Flexible **)

Inductive Flexible (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System)
: Prop :=
  satisfiesFlexibilityPrerequisites:
    Modifiable System Stakeholder Context Phase sys ->
    Tailorable System Stakeholder Context Phase sys ->
    Adaptable System Stakeholder Context Phase sys ->
    Flexible System Stakeholder Context Phase sys.
