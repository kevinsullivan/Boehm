(** 
Boehm stipulates that, "Tailorability accomplishes Flexibility without changes in the 
system's  overall structure or state, via such mechanisms as generics, design patterns, 
and plug-compatible receptors."

We model [Tailorable] in a completely generic way, providing the user of the taxonomy
with a place to plug in system-specific tailorability requirements for a given system for
each combination of stakeholder, context, and phase. As long as certificates are given
for satisfaction on these system-specific, end-user requirements, the proof constructor
of this type will be able to construct a proof/certificate that a given system is [Tailorable].

Note that at this level, we do not attempt to formalize the notion that tailorability means
flexibility without changes in system structure or state. Nor do we model mechanisms
that support tailorability. Our approach to these issues will have two parts. First, we will
defer specification of such details to quality-specific (e.g., flexibility-specific) languages.
Second, we will elaborate system models to include such concepts as structure and 
state, and we will devise little lanuages that are sensitive to such parameters. We have
not developed this idea as of June 1, 2015.
*)

(** ** Tailorable *)

Inductive Tailorable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesTailorabilityRequirement:
    (exists tailorable: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, tailorable sys sh cx ps)) ->
       Tailorable System Stakeholder Context Phase sys.