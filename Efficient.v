(** * Efficiency General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

Require Export Cost.
Require Export Duration.
Require Export KeyPersonnel.
Require Export OtherScarceResources.
Require Export Manufacturable.
Require Export Sustainable.

(** ** Efficiency**)
(**
[Efficient] is parameterized by a [System] type, a [Context] type,
an instance of type [System], and sevaral binary relations over [System] and [Context]
representing the relationship between the given [System] set, [Context] set, and some
constituent attribute. The constituent attributes of [Efficiency] are
the things it uses efficiently and whether it can be produced and maintained efficiently.
(Note: We have soon see cause to split these up - they aren't really very similar)

The constituent attributes are given by binary relations represent the given system type's ability to satisfy
the specified requirement in the given context.

Informally, in English:
A system [sys] belonging to the set of systems [System] is deemed [Efficient] given the set of contexts [Context]
if and only if all the requirements of its sub-attributes are satisfied given the same conditions.
*)

Inductive Efficient (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) : Prop := 
  satisfiesEfficiencyPrerequisites:
    Cost System Stakeholder Context Phase sys ->
    Duration System Stakeholder Context Phase sys ->
    KeyPersonnel System Stakeholder Context Phase sys ->
    OtherScarceResources System Stakeholder Context Phase sys ->
    Manufacturable System Stakeholder Context Phase sys ->
    Sustainable System Stakeholder Context Phase sys ->
    Efficient System Stakeholder Context Phase sys.