(** ** RESOURCE UTILIZATION *)
(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

Require Import System.
Require Import Context.

Module ResourceUtilization.
(** ** The basic system properties for [ResourceUtilization]*)
(**
We define two types of cost: 1) cost in development phase, and 2) cost of running a system in 
different contexts. The development cost is not related to context, but the cost in running time is.
*)

Inductive CostInDev: System.System -> Prop := 
    proofOfDevCost: forall (s: System.System), CostInDev s.

Inductive CostInRunning: System.System -> Context.Context -> Prop := 
  proofOfCostInContext: forall (s: System.System), forall (c: Context.Context), CostInRunning s c.

Inductive Duration: System.System -> Context.Context -> Prop := 
  proofOfDuration: forall (s: System.System), forall (c: Context.Context), Duration s c.

Inductive KeyPersonnel: System.System -> Context.Context -> Prop := 
  proofOfKeyPersonnel: forall (s: System.System), forall (c: Context.Context), KeyPersonnel s c.

Inductive OtherScarceResources: System.System -> Context.Context -> Prop := 
  proofOfOtherScarceResources: forall (s: System.System), forall (c: Context.Context), OtherScarceResources s c.

Inductive Manufacturability: System.System -> Context.Context -> Prop := 
  proofOfManufacturability: forall (s: System.System), forall (c: Context.Context), Manufacturability s c.

Inductive Sustainability: System.System -> Context.Context -> Prop := 
  proofOfSustainability: forall (s: System.System), forall (c: Context.Context), Sustainability s c.

(**
ResouceUtilization is not related to Stakeholder.
We define the [ResourceUtilization] property in two steps:
  - the binary relation of the atrribute [ResourceUtilization]  in a context
  - the unary property of being [ResourceUtilization]
*)
Inductive ResourceUtilization_In_Context (s: System.System) (c: Context.Context): Prop :=
    mk_resource_utilization_in_context: CostInDev s -> CostInRunning s c -> 
                        Duration s c-> KeyPersonnel s c ->
                        OtherScarceResources s c -> Manufacturability s c ->
                        Sustainability s c -> ResourceUtilization_In_Context s c.

Inductive ResourceUtilization (s: System.System): Prop :=
    mk_resource_utilization: 
      (forall c: Context.Context, ResourceUtilization_In_Context s c) -> ResourceUtilization s.

End ResourceUtilization.
