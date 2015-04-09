Inductive Interoperable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (io_sh_cx: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_interoperable:
    (forall cx: Context, forall sh: Stakeholder, io_sh_cx sys sh cx) -> 
      Interoperable System Stakeholder Context sys io_sh_cx.