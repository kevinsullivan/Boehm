(** * System Quality General Theory *)

(*
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes,
Barry Boehm, and Adam Ross
March, 2015
*)
Add Rec LoadPath "./ContributeQA".

Require Export Affordable.
Require Export Resilient.

Class Satisfactory (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) := {
    (* affordable is a composite property of "MissionEffective" and "Efficient"*)
    affordable: Affordable System Stakeholder Context Phase sys ;
    (* Resilient is a composite property of "Dependable", "Flexible" and "Changeable" *)
    resilient: Resilient System Stakeholder Context Phase sys
}.
