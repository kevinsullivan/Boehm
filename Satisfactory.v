(** ** Satisfactory General Theory *)

(*
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes,
Barry Boehm, and Adam Ross
March, 2015
*)

Require Export Affordable.
Require Export Resilient.


(** A given system [sys] of type [System] is satisfactory if, and only if, 
    for the given set of Stakeholders [Stakeholder], contexts [Context],
    and phases [Phase], it is both [Affordable] and [Resilient]. *)

Class Satisfactory (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) := {
    (** affordable is a composite property of "MissionEffective" and "Efficient" *)
    affordable: Affordable System Stakeholder Context Phase sys ;
    (* Resilient is a composite property of "Dependable", "Flexible" and "Changeable" *)
    resilient: Resilient System Stakeholder Context Phase sys
}.
