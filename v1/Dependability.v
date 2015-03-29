(** * Draft Coq Spec derived from Boehm 2015 QA Ontology *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March 23, 2015
*)

(** 
Import [CpdtTactics] moduel to use [crush] tactic. 
*)
Require Import CpdtTactics.

Require Import DataType.


(** ** DEPENDABILITY**)
(** ** Some basic objective but context-dependent system attibutes for [Dependability]*)
(**
Here we define [Security], [Safety], and other "ilities" as
(objective) properties of specific [Systems] in specific [Contexts]. For each 
property we provide a proof constructor that returns a proof of validity of a
proposition that that property holds "axiomatically" -- for any [System] and 
any [Context].
*) 
Inductive Security: System -> Context -> Prop := 
  proofOfSecurity: forall (s: System), forall (c: Context), Security s c.

Inductive Safety: System -> Context -> Prop := 
  proofOfSafety: forall (s: System), forall (c: Context), Safety s c.

Inductive Reliability: System -> Context -> Prop := 
  proofOfReliability: forall (s: System), forall (c: Context), Reliability s c.

Inductive Maintainability: System -> Context -> Prop := 
  proofOfMaintainability: forall (s: System), forall (c: Context), Maintainability s c.

Inductive Availability: System -> Context -> Prop := 
  proofOfAvailability: forall (s: System), forall (c: Context), Availability s c.

Inductive Survivability: System -> Context -> Prop := 
  proofOfSurvivability: forall (s: System), forall (c: Context), Survivability s c.

Inductive Robustness: System -> Context -> Prop := 
  proofOfRobustness: forall (s: System), forall (c: Context), Robustness s c.

(**
This construct defines a binary relation, an instance of which we interpret as a proposition
that a given [System], [s], in a given [Context], c, is subjectively "dependable", and that this is provably the case if and only if the required set of
arguments can be provided to the proof constructor, [is_dependable_in_context]. In
particular, one must provide proofs of all of the constituent propositions, e.g., the system
"has the required security," etc. If the constructor is applied to aguments  of the
required "proof" types, then it will return a proof of dependability for the
given [System] in the given [Context].
*)
Inductive Dependable_In_Context (s: System) (c: Context): Prop :=
    is_dependable_in_context: Security s c -> Safety s c -> Reliability s c ->
                  Maintainability s c -> Availability s c -> Survivability s c ->
                   Robustness s c -> Dependable_In_Context s c.

Inductive Dependable (s: System): Prop :=
    mk_dependability:
      (forall c:Context, Dependable_In_Context s c) -> Dependable s.

(** ** Asserting and proving that [aSystem] [isDependableisMissionEffective]. *)
Theorem aSystemisDependable: Dependable aSystem.

Proof.
apply mk_dependability.
intros context.
destruct context as [referent state stage].
destruct referent, state as [internalState externalState].
destruct internalState, externalState, stage. crush.
exact (proofOfSecurity aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfSafety aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfReliability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfMaintainability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfAvailability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfSurvivability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfRobustness aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
Qed.