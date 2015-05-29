(** ** Resilient General Theory **)
(* begin hide *)
(* end hide *)

Require Import Dependable.
Require Import Flexible.
Require Import Changeable.

(**
[Resiliency] is a composite attribute of [Dependability], [Flexibility], and [Changeability].
A system is [Affordable] only if it meets the requirements of these constient attributes.

Informally,
A system [sys] belonging to the set of systems [System] is deemed [Resilient] for all stakeholders
in set [Stakeholder] given the set of phases and contexts [Context] and [Phase] if and only if all the
requirements of its sub-attributes are satisfied given the same conditions. *) 

Inductive Resilient
          (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  isResilient:
    Dependable System Stakeholder Context Phase sys  ->
    Flexible System Stakeholder Context Phase sys  ->
    Changeable System Stakeholder Context Phase sys ->
    Resilient System Stakeholder Context Phase sys.
