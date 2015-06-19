(** * MissionEffective General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

Inductive MissionEffective (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                           (me_sh_cx: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_mission_eff:
    (forall cx: Context, forall sh: Stakeholder, me_sh_cx sys sh cx) -> 
      MissionEffective System Stakeholder Context sys me_sh_cx.