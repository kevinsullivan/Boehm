Add Rec LoadPath "./ContributeQA".

Require Import Dependable.
Require Import Flexible.

(** ** RESILIENT**)
(**
[Resilient] is a composite attribute of [Dependable] and [Flexible].
A system is [Resilient] only if it meets the requirements of both [Dependable] and [Flexible].

In the following definition, [ResourceUtilization] is parameterized by two typeclasses, [System],
and [Context], a system, sys, of type [System], and sevaral binary relations over [System], [Context].

Those binary relations are associated with its two sub-attributes, [Dependable] and [Flexible],
and their sub-attributes. For example, dp_cx represents a binary relation, which is to say, a set of pairs, (s, c), 
between a system, s, and a context, c, that we  intend to hold (for the proposition to be provable, 
iff system s satisfies its [Dependable] requirement (which isn't represented explicitly here) in context, c.)

Its definition indicates that the property of a [System] being [Resilient] for all [Contexts], the system is
resilient implicitly in those [Contexts], only if a system is both [Dependable] and [Flexible] in those [Contexts]. 
That is, all the requirements of the subattributes of both [Dependable] and [Flexible] are satisfied.
*)

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