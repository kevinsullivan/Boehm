(** * Dependable General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

Add Rec LoadPath "./ContributeQA".
Require Export Secure.
Require Export Safe.
Require Export Reliable.
Require Export Maintainable.
Require Export Available.
Require Export Survivable.

(** ** DEPENDABLE**)
(**
In the following definition, [Dependable] is parameterized by two typeclasses, [System],
and [Context], a system, sys, of type [System], and sevaral binary relations over [System], [Context].

Those binary relations are associated with its sub-attributes. For example, [Secure] is one of the sub-attributes, 
and sec_cx represents a tenary relation, which is to say, a set of pairs, (s, c), 
between a system, s, and a context, c, that we  intend to hold (for the proposition to be provable, 
iff system s satisfies its [Secure] requirement (which isn't represented explicitly here) in context, c.)

Its definition indicates that the property of a [System] being [Dependable] for all [Contexts], the system is
dependable implicitly in those [Contexts], only if all the requirements of its sub-attributes are satisfied.
*)

Inductive Dependable (System: Set) (Context: Set) (sys: System) 
                     (dp_cx: System -> Context -> Prop)
                     (sec_cx: System -> Context -> Prop)
                     (sf_cx: System -> Context -> Prop)
                     (rl_cx: System -> Context -> Prop)
                     (mt_cx: System -> Context -> Prop)
                     (avl_cx: System -> Context -> Prop)
                     (svv_cx: System -> Context -> Prop)
                     : Prop := 
  mk_dependability:
    Secure System Context sys sec_cx ->
    Safe System Context sys sf_cx ->
    Reliable System Context sys rl_cx ->
    Maintainable System Context sys mt_cx ->
    Available System Context sys avl_cx ->
    Survivable System Context sys svv_cx ->
    Dependable System Context sys dp_cx sec_cx sf_cx rl_cx mt_cx avl_cx svv_cx.