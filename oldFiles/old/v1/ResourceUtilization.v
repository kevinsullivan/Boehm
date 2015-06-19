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

(** ** RESOURCE UTILIZATION **)
(** ** The basic system properties for [ResourceUtilization]*)
(**
We define two types of cost: 1) cost in development phase, and 2) cost of running a system in 
different contexts. The development cost is not related to context, but the cost in running time does.
*)

Inductive CostInDev: System -> Prop := 
    proofOfDevCost: forall (s: System), CostInDev s.

Inductive CostInRunning: System -> Context -> Prop := 
  proofOfCostInContext: forall (s: System), forall (c: Context), CostInRunning s c.

Inductive Duration: System -> Context -> Prop := 
  proofOfDuration: forall (s: System), forall (c: Context), Duration s c.

Inductive KeyPersonnel: System -> Context -> Prop := 
  proofOfKeyPersonnel: forall (s: System), forall (c: Context), KeyPersonnel s c.

Inductive OtherScarceResources: System -> Context -> Prop := 
  proofOfOtherScarceResources: forall (s: System), forall (c: Context), OtherScarceResources s c.

Inductive Manufacturability: System -> Context -> Prop := 
  proofOfManufacturability: forall (s: System), forall (c: Context), Manufacturability s c.

Inductive Sustainability: System -> Context -> Prop := 
  proofOfSustainability: forall (s: System), forall (c: Context), Sustainability s c.

(**
ResouceUtilization is not related to Stakeholder.
We define the [ResourceUtilization] property in two steps:
  - the binary relation of the atrribute [ResourceUtilization]  in a context
  - the unary property of being [ResourceUtilization]
*)
Inductive ResourceUtilization_In_Context (s: System) (c: Context): Prop :=
    mk_resource_utilization_in_context: CostInDev s -> CostInRunning s c -> 
                        Duration s c-> KeyPersonnel s c ->
                        OtherScarceResources s c -> Manufacturability s c ->
                        Sustainability s c -> ResourceUtilization_In_Context s c.

Inductive ResourceUtilization (s: System): Prop :=
    mk_resource_utilization: 
      (forall c: Context, ResourceUtilization_In_Context s c) -> ResourceUtilization s.

(** ** Asserting and proving that [aSystem] [isResourceUtilization]. *)
Theorem aSystemisResourceUtilization: ResourceUtilization aSystem.
apply mk_resource_utilization.
intro context.
destruct context as [referent state stage].
destruct referent, state as [internalState externalState].
destruct internalState, externalState, stage. crush.
exact (proofOfDevCost aSystem).
exact (proofOfCostInContext aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfDuration aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfKeyPersonnel aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfOtherScarceResources aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfManufacturability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfSustainability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
Qed.