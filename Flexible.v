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

Inductive Flexible {msys: MetaSystem} (sys: System msys)
: Prop :=
  satisfiesFlexibilityPrerequisites:
    Modifiable sys ->
    Tailorable sys ->
    Adaptable sys ->
    Flexible sys.
