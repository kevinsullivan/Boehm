(** * Flexibility General Theory *)

(*
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes,
Barry Boehm, and Adam Ross
March, 2015
*)

(* begin hide *)
(* end hide *)
Require Export Modifiable.
Require Export Tailorable.
Require Export Adaptable.

(** ** Flexible **)
(**
[Flexible] is parameterized by a [System] type, a [Context] type, an instance of type [System],
and set of phases [Phase]. The constituent attributes of [Flexibility] are [Modifiability],
[Tailorability], and [Adaptability].

Informally,
A system [sys] belonging to the set of systems [System] is deemed [Flexible] given the set of contexts [Context]
if and only if all the requirements of its sub-attributes ([Modifiability], [Tailorability], and [Adaptability])
are satisfied given the same conditions.
*)

Inductive Flexible (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System)
: Prop :=
  satisfiesFlexibilityPrerequisites:
    Modifiable System Stakeholder Context Phase sys ->
    Tailorable System Stakeholder Context Phase sys ->
    Adaptable System Stakeholder Context Phase sys ->
    Flexible System Stakeholder Context Phase sys.
