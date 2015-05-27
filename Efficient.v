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

Inductive Efficient (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System)  
                              (cost: System -> Stakeholder -> Context -> Phase -> Prop)
                              (duration: System -> Stakeholder -> Context -> Phase -> Prop)
                              (keyPersonnel: System -> Stakeholder -> Context -> Phase -> Prop)
                              (otherScareResources: System -> Stakeholder -> Context -> Phase -> Prop)
                              (manufacturability: System -> Stakeholder -> Context -> Phase -> Prop)
                              (sustainability: System -> Stakeholder -> Context -> Phase -> Prop)
                              : Prop := 
  mk_efficient:
    Cost System Stakeholder Context Phase sys cost ->
    Duration System Stakeholder Context Phase sys duration ->
    KeyPersonnel System Stakeholder Context Phase sys keyPersonnel ->
    OtherScarceResources System Stakeholder Context Phase sys otherScareResources ->
    Manufacturable System Stakeholder Context Phase sys manufacturability ->
    Sustainable System Stakeholder Context Phase sys sustainability ->
    Efficient System Stakeholder Context Phase sys cost duration keyPersonnel otherScareResources manufacturability sustainability.