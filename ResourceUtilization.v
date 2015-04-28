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