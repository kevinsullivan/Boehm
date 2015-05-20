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
Require Export Robustness.

(** ** DEPENDABLE**)
(**
In the following definition, [Dependable] is parameterized by two typeclasses, [System],
and [Context], a system, sys, of type [System], and sevaral binary relations over [System], [Context].

Those binary relations are associated with its sub-attributes. For example, [Secure] is one of the sub-attributes,
and security represents a tenary relation, which is to say, a set of pairs, (s, c),
between a system, s, and a context, c, that we  intend to hold (for the proposition to be provable,
iff system s satisfies its [Secure] requirement (which isn't represented explicitly here) in context, c.)

Its definition indicates that a [System] is [Dependable] for all [Contexts] if only if
all the requirements of its sub-attributes are satisfied.
*)

Inductive Dependable (System: Set) (Context: Set) (sys: System)
                     (security: System -> Context -> Prop)
                     (safety: System -> Context -> Prop)
                     (reliability: System -> Context -> Prop)
                     (maintainability: System -> Context -> Prop)
                     (availability: System -> Context -> Prop)
                     (survivability: System -> Context -> Prop)
                     (robustness: System -> Context -> Prop)
                     : Prop :=
  mk_dependability:
    Secure System Context sys security ->
    Safe System Context sys safety ->
    Reliable System Context sys reliability ->
    Maintainable System Context sys maintainability ->
    Available System Context sys availability ->
    Survivable System Context sys survivability ->
    Robustness System Context sys robustness ->
    Dependable System Context sys security safety reliability maintainability availability survivability robustness.
