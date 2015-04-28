(** * ResourceUtilization General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)


Inductive ResourceUtilization (System: Set) (Context: Set) (sys: System) 
                              (ru_cx: System -> Context -> Prop) : Prop := 
  mk_resource_utl:
    (forall cx: Context, ru_cx sys cx) -> 
      ResourceUtilization System Context sys ru_cx.