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
and cs_cx represents a tenary relation, which is to say, a set of pairs, (s, c), 
between a system, s, and a context, c, that we  intend to hold (for the proposition to be provable, 
iff system s satisfies its [Cost] requirement (which isn't represented explicitly here) in context, c.)

Its definition indicates that the property of a [System] being [ResourceUtilization] for all [Contexts], the system's 
resource utilization requirements are satisfied implicitly in those [Contexts], 
sonly if all the requirements of its sub-attributes are satisfied.
*)

Inductive ResourceUtilization (System: Set) (Context: Set) (sys: System) 
                              (ru_cx: System -> Context -> Prop)
                              (cs_cx: System -> Context -> Prop)
                              (dr_cx: System -> Context -> Prop)
                              (kp_cx: System -> Context -> Prop)
                              (osr_cx: System -> Context -> Prop)
                              (mf_cx: System -> Context -> Prop)
                              (sust_cx: System -> Context -> Prop)
                              : Prop := 
  mk_resource_utl:
    Cost System Context sys cs_cx ->
    Duration System Context sys dr_cx ->
    KeyPersonnel System Context sys kp_cx ->
    OtherScarceResources System Context sys osr_cx ->
    Manufacturable System Context sys mf_cx ->
    Sustainable System Context sys sust_cx ->
    ResourceUtilization System Context sys ru_cx cs_cx dr_cx kp_cx osr_cx mf_cx sust_cx.