(** * Flexible General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)
Add Rec LoadPath "./ContributeQA".
Require Export Modifiable.
Require Export Tailorable.
Require Export Adaptable.

Inductive Flexible (System: Set) (Context: Set) (sys: System) 
                     (fl_cx: System -> Context -> Prop) 
                     (md_cx: System -> Context -> Prop)
                     (tl_cx: System -> Context -> Prop)
                     (adp_cx: System -> Context -> Prop)
                     : Prop := 
  isFlexible:
    Modifiable System Context sys md_cx ->
    Tailorable System Context sys tl_cx ->
    Adaptable System Context sys adp_cx ->
    Flexible System Context sys fl_cx md_cx tl_cx adp_cx.