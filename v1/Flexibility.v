(** * Draft Coq Spec derived from Boehm 2015 QA Ontology *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

(** 
Import [CpdtTactics] moduel to use [crush] tactic. 
*)
Require Import CpdtTactics.

Require Import DataType.


(** ** FLEXIBILITY**)
(**
We first define the basic context-dependent system attributes for [Flexibility].
*)
Inductive Modifiability: System -> Context -> Prop := 
  proofOfModifiability: forall (s: System), forall (c: Context), Modifiability s c.

Inductive Tailorability: System -> Context -> Prop := 
  proofOfTailorability: forall (s: System), forall (c: Context), Tailorability s c.

Inductive Adaptability: System -> Context -> Prop := 
  proofOfAdaptability: forall (s: System), forall (c: Context), Adaptability s c.

(**
As we did before, we define [aSystem is Flexible] in two steps:
  - a system is flexible in a context.
  - a system is universally flexible.
*)
Inductive Flexible_In_Context (s: System) (c: Context) : Prop :=
    is_flexible_in_context: Modifiability s c -> Tailorability s c -> 
        Adaptability s c -> Flexible_In_Context s c.

Inductive Flexible (s: System) : Prop :=
    mk_flexibility: 
        (forall c: Context, Flexible_In_Context s c) -> Flexible s.

(** ** Asserting and proving that [aSystem] [IsFlexible]. *)
Theorem aSystemIsFlexible: Flexible aSystem.
apply mk_flexibility.
intros context.
destruct context as [referent state stage].
destruct referent, state as [internalState externalState].
destruct internalState, externalState, stage. crush.
exact (proofOfModifiability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfTailorability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfAdaptability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
Qed.