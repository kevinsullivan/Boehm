(** * Efficiency General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

Add Rec LoadPath "./ContributeQA".
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

Inductive Efficient (System: Set) (Context: Set) (sys: System) 
                              (cost: System -> Context -> Prop)
                              (duration: System -> Context -> Prop)
                              (keyPersonnel: System -> Context -> Prop)
                              (otherScareResources: System -> Context -> Prop)
                              (manufacturability: System -> Context -> Prop)
                              (sustainability: System -> Context -> Prop)
                              : Prop := 
  mk_efficient:
    Cost System Context sys cost ->
    Duration System Context sys duration ->
    KeyPersonnel System Context sys keyPersonnel ->
    OtherScarceResources System Context sys otherScareResources ->
    Manufacturable System Context sys manufacturability ->
    Sustainable System Context sys sustainability ->
    Efficient System Context sys cost duration keyPersonnel otherScareResources manufacturability sustainability.