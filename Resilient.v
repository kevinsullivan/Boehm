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
and their sub-attributes. For example, [safety] represents a binary relation, which is to say, a set of pairs, (s, c),
between a system, s, and a context, c, that we expect to hold (for the proposition to be provable,
iff system s satisfies its [Safe] requirement (which isn't represented explicitly here) in context, c.)

Its definition indicates that the property of a [System] being [Resilient] for all [Contexts], the system is
resilient implicitly in those [Contexts], only if a system is both [Dependable] and [Flexible] in those [Contexts].
That is, all the requirements of the subattributes of both [Dependable] and [Flexible] are satisfied.
*)

Inductive Resilient
            (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
            (security: System -> Stakeholder -> Context -> Phase -> Prop)
            (safety: System -> Stakeholder -> Context -> Phase -> Prop)
            (reliability: System -> Stakeholder -> Context -> Phase -> Prop)
            (maintainability: System -> Stakeholder -> Context -> Phase -> Prop)
            (availability: System -> Stakeholder -> Context -> Phase -> Prop)
            (survivability: System -> Stakeholder -> Context -> Phase -> Prop)
            (robustness: System -> Stakeholder -> Context -> Phase -> Prop)
            (manufacturability: System -> Stakeholder -> Context -> Phase -> Prop)
            (tailorability: System -> Stakeholder -> Context -> Phase -> Prop)
            (adaptivity: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
            isResilient:
                 Dependable System Stakeholder Context Phase sys security safety reliability maintainability availability survivability robustness ->
                 Flexible System Stakeholder Context Phase sys manufacturability tailorability adaptivity ->
                 Resilient System Stakeholder Context Phase sys
                     security safety reliability maintainability availability survivability robustness
                     manufacturability tailorability adaptivity.
