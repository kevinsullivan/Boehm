(** * ResourceUtilization General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

Add Rec LoadPath "./ContributeQA".
Require Export Cost.
Require Export Duration.
Require Export KeyPersonnel.
Require Export OtherScarceResources.
Require Export Manufacturable.
Require Export Sustainable.

(** ** Resource Utilization**)
(**
In the following definition, [ResourceUtilization] is parameterized by two typeclasses, [System],
and [Context], a system, sys, of type [System], and sevaral binary relations over [System], [Context].

Those binary relations are associated with its sub-attributes. For example, [Cost] is one of the sub-attributes, 
and cost represents a tenary relation, which is to say, a set of pairs, (s, c), 
between a system, s, and a context, c, that we  intend to hold (for the proposition to be provable, 
iff system s satisfies its [Cost] requirement (which isn't represented explicitly here) in context, c.)

Its definition indicates that the property of a [System] being [ResourceUtilization] for all [Contexts], the system's 
resource utilization requirements are satisfied implicitly in those [Contexts], 
sonly if all the requirements of its sub-attributes are satisfied.
*)

Inductive ResourceUtilization (System: Set) (Context: Set) (sys: System) 
                              (cost: System -> Context -> Prop)
                              (duration: System -> Context -> Prop)
                              (keyPersonnel: System -> Context -> Prop)
                              (otherScareResources: System -> Context -> Prop)
                              (manufacturability: System -> Context -> Prop)
                              (sustainability: System -> Context -> Prop)
                              : Prop := 
  mk_resource_utl:
    Cost System Context sys cost ->
    Duration System Context sys duration ->
    KeyPersonnel System Context sys keyPersonnel ->
    OtherScarceResources System Context sys otherScareResources ->
    Manufacturable System Context sys manufacturability ->
    Sustainable System Context sys sustainability ->
    ResourceUtilization System Context sys cost duration keyPersonnel otherScareResources manufacturability sustainability.