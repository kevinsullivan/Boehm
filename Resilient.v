Require Export Dependable.
Require Export Flexible.
Require Export Changeable.
Require Export Changeable_Ross.
Require Export System.

(** 
Boehm stipulates that [Resiliency] is a composite quality comprising [Dependability] 
and [Flexibility]. That is, a system can be deemed to be resilient across stakeholders,
operational contexts, and lifecycle phases if it is deemed to be dependable and flexible in
all these dimensions.

The definition we give here includes [Changeable] as a sub-quality of resiliency, as
well. We have inserted this node to illustrate how we can begin to combine Boehm's
top-level taxonomy with quality-specific formal theories developed by others. 
*)

(** ** Resilient  **)

Inductive Resilient {model: Model} (sys: System model)
: Prop :=
  satisfiesResiliencyPrerequisites:
    Dependable sys ->
    Flexible sys ->
    Changeable sys ->
    Changeable_Ross sys ->
    Resilient sys.


(**
In this case, the [Changeable] concept embodies a theory from Ross et al. at MIT.
They have developed a somewhat elaborate theory of change-related qualities. We
have formalized, cleaned up, and extended their concepts and have integrated them
here into Boehm's taxonomy in the form of a formal little language for expressing and
for classifying change-related requirements.

More generally, we see the need and opportunity to develop an evolving suite of 
quality-specific, formal little languages for a broad range of system qualities. Some 
of them could be based on already excellent but still informal work, e.g., of Laprie 
et al. on dependability qualities. In some areas the science is so under-developed
that de novo research may be needed.
 *) 

