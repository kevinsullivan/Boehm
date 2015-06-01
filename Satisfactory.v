(** ** Satisfactory General Theory *)

(*
Kevin Sullivan, Koleman Nix, Chong Tang, Ke Dou, with Donna Rhodes,
Barry Boehm, and Adam Ross.
*)

Require Export Affordable.
Require Export Resilient.


(** 
A given system [sys] of type [System] is satisfactory if, and only if, 
for its given set of Stakeholders [Stakeholder], contexts [Context],
and phases [Phase], it is both [Affordable] and [Resilient].  These
system qualities are themselves composites of lower-level system
qualities, as detailed in their respective files.
*)

Class Satisfactory (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) := {
    affordable: Affordable System Stakeholder Context Phase sys ;
    resilient: Resilient System Stakeholder Context Phase sys
}.
