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
and modifiability represents a ternary relation, which is to say, a set of pairs, (s, c),
between a system [s], and a context [c], that we expect to hold (The proposition is provable
iff system [s] satisfies its modifiability requirement in context [c].)

Its definition indicates that a [System] is [Flexible] in all [Contexts] iff the system is
all the requirements of its sub-attributes [Modifiability], [Tailorability], [Adaptability] are satisfied.
*)

Inductive Flexible (System: Set) (Context: Set) (sys: System)
                     (modifiability: System -> Context -> Prop)
                     (tailorability: System -> Context -> Prop)
                     (adaptivity: System -> Context -> Prop)
                     : Prop :=
  isFlexible:
    Modifiable System Context sys modifiability ->
    Tailorable System Context sys tailorability ->
    Adaptable System Context sys adaptivity ->
    Flexible System Context sys modifiability tailorability adaptivity.
