(** Boehm version *)


(*
Adaptivity represents a binary relation, which is to say, a set of
pairs, (s, c), between a system, s, and a context, c, that we 
intend to hold (for the proposition to be provable, iff system 
s satisfies its adaptability requirement (which isn't represented
explicitly here) in context, c.
 
*)

Inductive Adaptable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                     (adaptable: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  mk_adaptability:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, adaptable sys sh cx ps) ->
      Adaptable System Stakeholder Context Phase sys adaptable.


