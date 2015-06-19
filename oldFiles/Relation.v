(**QUALITY STRATEGY RELATION DEFINITION**)

(* 
Here we define the Relation typeclass
A relation type class takes two arguments: Quality and Strategy
*)
Class Relation (Quality: Set) (Strategy: Set) := {
    q: Quality
  ; s: Strategy
  ; helps: Strategy -> Quality -> Prop
  ; harms: Strategy -> Quality -> Prop
  ; synergy: forall q1:Quality, forall q2: Quality, exists s:Strategy, 
                  q1 <> q2 /\ (helps s q1 <-> helps s q2)
  ; conflicts: forall q1:Quality, forall q2: Quality, exists s:Strategy, 
                  q1 <> q2 /\ (helps s q1 -> harms s q2 \/ harms s q2 -> helps s q1)
}.