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

(** ** FLEXIBLE**)
(**
In the following definition, [Flexible] is parameterized by two typeclasses, [System],
and [Context], a system, sys, of type [System], and sevaral binary relations over [System], [Context].

Those binary relations are associated with its sub-attributes. For example, [Modifiable] is one of the sub-attributes, 
and md_cx represents a tenary relation, which is to say, a set of pairs, (s, c), 
between a system, s, and a context, c, that we  intend to hold (for the proposition to be provable, 
iff system s satisfies its [Modifiable] requirement (which isn't represented explicitly here) in context, c.)

Its definition indicates that the property of a [System] being [Flexible] for all [Contexts], the system is
flexible implicitly in those [Contexts], only if all the requirements of its sub-attributes are satisfied.
*)

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