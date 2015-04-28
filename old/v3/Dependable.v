(** * Dependable General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)


Inductive Dependable (System: Set) (Context: Set) (sys: System) 
                     (dp_cx: System -> Context -> Prop) : Prop := 
  mk_dependable:
    (forall cx: Context, dp_cx sys cx) -> 
      Dependable System Context sys dp_cx.