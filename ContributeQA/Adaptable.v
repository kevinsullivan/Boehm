(** Boehm version *)


(*
adaptivity represents a binary relation, which is to say, a set of
pairs, (s, c), between a system, s, and a context, c, that we 
intend to hold (for the proposition to be provable, iff system 
s satisfies its adaptability requirement (which isn't represented
explicitly here) in context, c.
 
*)

Inductive Adaptable (System: Set) (Context: Set) (sys: System) 
                     (adaptability: System -> Context -> Prop) : Prop :=
  mk_adaptability:
    (forall cx: Context, adaptability sys cx) -> 
      Adaptable System Context sys adaptability.

(** Ross version *)

Require Import Changeable.

(** 
It seems like we need a new relation, associating a system, a context, and a 
specific adaptability requirement, with a proof iff that specific system is 
deemed to satisfy that specific requirement in that specific context. 
*)

Definition anAdaptabilityRequirement: changeStatement :=
  mk_changeStatement 
    (perturbation_shift "some event")
    (context_circumstantial "some circumstantial context")
    phase_preOps 
    (agent_internal "aAgent")
    (mk_change direction_increase (parameter_level "aParameter") (origin_one "anOrginin") (destination_one "aDestination") aspect_function)
    (mechanism_description "some mechanism") 
    (mk_change direction_increase(parameter_level "anotherParameter") (origin_one "anotherOrginin") (destination_one "anotherDestination") aspect_function)
    (abstraction_architecture "anAbstraction")
    (valuable_compound "valuable because of" 
      (reaction_sooner_than 10 unit_time_second)
      (span_shorter_than 1 unit_time_day)
      (cost_less_than 100 unit_money_dollar)
      (benefit_same_as "keep power on")).

(**
Here's where we provide proofs that a system satsfies specific requirements, given
as changeStatements.
*)

Inductive satisfiesAdapabilityRequirement (System: Set) (sys: System) (Context: Set) (req: changeStatement): Prop := .

(** 
What's left to do is to connect adaptivity to satisfiesAdapatabilityRequirment. 

A note: A real system will have multiple adapability requirements. We could conjoin them all together into one
big one, or modified the theory so that what's required is a "forall."
*)


