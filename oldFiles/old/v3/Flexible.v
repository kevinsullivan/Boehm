(** * Flexible General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

Inductive Flexible (System: Set) (Context: Set) (sys: System) 
                     (fl_cx: System -> Context -> Prop) : Prop := 
  mk_flexible:
    (forall cx: Context, fl_cx sys cx) -> 
      Flexible System Context sys fl_cx.