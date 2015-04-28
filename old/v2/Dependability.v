(** * DEPENDABILITY *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March 23, 2015
*)

Require Import System.
Require Import Context.

Module Dependable.
(** ** Some basic objective but context-dependent system attibutes for [Dependability]*)
(**
 Here we define [Security], [Safety], and other "ilities" as
 (objective) properties of specific [Systems] in specific [Contexts]. For each 
 property we provide a proof constructor that returns a proof of validity of a
 proposition that that property holds "axiomatically" -- for any [System] and 
 any [Context].
*) 
  Inductive Security: System.System -> Context.Context -> Prop := 
    proofOfSecurity: forall (s: System.System), forall (c: Context.Context), Security s c.

  Inductive Safety: System.System -> Context.Context -> Prop := 
    proofOfSafety: forall (s: System.System), forall (c: Context.Context), Safety s c.

  Inductive Reliability: System.System -> Context.Context -> Prop := 
    proofOfReliability: forall (s: System.System), forall (c: Context.Context), Reliability s c.

  Inductive Maintainability: System.System -> Context.Context -> Prop := 
    proofOfMaintainability: forall (s: System.System), forall (c: Context.Context), Maintainability s c.

  Inductive Availability: System.System -> Context.Context -> Prop := 
    proofOfAvailability: forall (s: System.System), forall (c: Context.Context), Availability s c.

  Inductive Survivability: System.System -> Context.Context -> Prop := 
    proofOfSurvivability: forall (s: System.System), forall (c: Context.Context), Survivability s c.

  Inductive Robustness: System.System -> Context.Context -> Prop := 
    proofOfRobustness: forall (s: System.System), forall (c: Context.Context), Robustness s c.

(**
This construct defines a binary relation, an instance of which we interpret as a proposition
that a given [System], [s], in a given [Context], c, is subjectively "dependable", and that this is provably the case if and only if the required set of
arguments can be provided to the proof constructor, [is_dependable_in_context]. In
particular, one must provide proofs of all of the constituent propositions, e.g., the system
"has the required security," etc. If the constructor is applied to aguments  of the
required "proof" types, then it will return a proof of dependability for the
given [System] in the given [Context].
*)
  Inductive Dependable_In_Context (s: System.System) (c: Context.Context): Prop :=
    is_dependable_in_context: Security s c -> Safety s c -> Reliability s c ->
                  Maintainability s c -> Availability s c -> Survivability s c ->
                   Robustness s c -> Dependable_In_Context s c.

  Inductive Dependable (s: System.System): Prop :=
    mk_dependability:
      (forall c:Context.Context, Dependable_In_Context s c) -> Dependable s.

End Dependable.