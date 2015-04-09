Add Rec LoadPath "./ContributeQA".

Require Import Dependable.
Require Import Flexible.

Inductive Resilient 
            (System: Set) (Context: Set) (sys: System) 
            (dp_cx: System -> Context -> Prop)
            (sec_cx: System -> Context -> Prop)
            (sf_cx: System -> Context -> Prop)
            (rl_cx: System -> Context -> Prop)
            (mt_cx: System -> Context -> Prop)
            (avl_cx: System -> Context -> Prop)
            (svv_cx: System -> Context -> Prop)
            (fl_cx: System -> Context -> Prop) 
            (mf_cx: System -> Context -> Prop)
            (tl_cx: System -> Context -> Prop)
            (adp_cx: System -> Context -> Prop) : Prop :=
            isResilient: 
                 Dependable System Context sys dp_cx sec_cx sf_cx rl_cx mt_cx avl_cx svv_cx ->
                 Flexible System Context sys fl_cx mf_cx tl_cx adp_cx ->
                 Resilient System Context sys 
                     dp_cx sec_cx sf_cx rl_cx mt_cx avl_cx svv_cx fl_cx mf_cx tl_cx adp_cx.