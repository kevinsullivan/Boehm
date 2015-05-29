Add Rec LoadPath "./ContributeQA".

Require Import Dependable.
Require Import Flexible.
Require Import Changeable.

(** ** Resilient **)
(**
[Resilient] is a composite attribute of [Dependable] and [Flexible].
A system is [Resilient] only if it meets the requirements of both [Dependable] and [Flexible].

In the following definition, [ResourceUtilization] is parameterized by two typeclasses, [System],
and [Context], a system, sys, of type [System].

Its definition indicates that the property of a [System] being [Resilient] for all [Contexts], the system is
resilient implicitly in those [Contexts], only if a system is both [Dependable] and [Flexible] in those [Contexts].
That is, all the requirements of the subattributes of both [Dependable] and [Flexible] are satisfied.
*)

Inductive Resilient
          (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  isResilient:
    Dependable System Stakeholder Context Phase sys  ->
    Flexible System Stakeholder Context Phase sys  ->
    Changeable System Stakeholder Context Phase sys ->
    Resilient System Stakeholder Context Phase sys.
