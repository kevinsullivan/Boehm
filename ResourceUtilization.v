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

Inductive ResourceUtilization (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System)  
                              (cost: System -> Stakeholder -> Context -> Phase -> Prop)
                              (duration: System -> Stakeholder -> Context -> Phase -> Prop)
                              (keyPersonnel: System -> Stakeholder -> Context -> Phase -> Prop)
                              (otherScareResources: System -> Stakeholder -> Context -> Phase -> Prop)
                              (manufacturability: System -> Stakeholder -> Context -> Phase -> Prop)
                              (sustainability: System -> Stakeholder -> Context -> Phase -> Prop)
                              : Prop := 
  mk_resource_utl:
    Cost System Stakeholder Context Phase sys cost ->
    Duration System Stakeholder Context Phase sys duration ->
    KeyPersonnel System Stakeholder Context Phase sys keyPersonnel ->
    OtherScarceResources System Stakeholder Context Phase sys otherScareResources ->
    Manufacturable System Stakeholder Context Phase sys manufacturability ->
    Sustainable System Stakeholder Context Phase sys sustainability ->
    ResourceUtilization System Stakeholder Context Phase sys cost duration keyPersonnel otherScareResources manufacturability sustainability.