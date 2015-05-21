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
[Dependable] is parameterized by a [System] type, a [Context] type,
an instance of type [System], and sevaral binary relations over [System] and [Context]
representing the relationship between the given [System] set, [Context] set, and some
constituent attribute. The constituent attributes of [Dependability] are
[Security], [Safety], [Reliability], ..., and [Robustness].

These binary relations represent the given system type's ability to satisfy
the specified requirement in the given context.

Informally, in English:
A system [sys] belonging to the set of systems [System] is deemed [Dependable] given the set of contexts [Context]
if and only if all the requirements of its sub-attributes ([Security], [Safety], [Reliability], ..., and [Robustness])
are satisfied given the same conditions.
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
