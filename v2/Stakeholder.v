(** ** STAKEHOLDERS MODULE**)
Load System.

Module Stakeholder.
(** 
An important class of "subjective" properties concerns stakeholder satisfaction or value.
We thus introduce a data type of "stakeholders in a given system, [s]." The [Stakeholder]
data type is thus parameterized by a given system model of concern.
*)

  Inductive Stakeholder (s: System.System) := aStakeholder.
End Stakeholder.          