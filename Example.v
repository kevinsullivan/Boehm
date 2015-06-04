(** * Example -- Smart Home *)

Require Export Satisfactory.

(**
To model a specific system, we must specify four types, which we
will then use as actual parameter values for the formal parameters
of the reusable taxonomy. Recall that the taxonomy is parameterized
by types [System], [Stakeholder], [Context], and [Phase], and that it
takes a final parameter, [sys], which is a value of type [System]. 
*)

(**
We now define a set of actual types and values for an imaginary and
unrealistically simple smart home system. This example shows how 
we can "stub out" properties that we don't care about, by giving trivial
proof constructors for those properties; how we can define arbitrary
additional quality requirements that we can plug in to a system-specific
instance of the taxonomy; how we instantiate the taxonomy for this
particular system; and how Coq supports and enforces the provisioning
and construction of proofs/certificates for all of the required properties. 
*)

(**
We begin by selecting or defining a value for the [System] type. This type is
used to model not a single system but a whole class of systems, of which our
system will be an instance. Here we pick the simplest of all possible types: the
Coq standard [unit] type. This has only one value and thus carries absolutely 
no details about the system. Any arbitrarily complex type could be provided 
here, e.g., one that carries SysML, timed and hybrid automata models, etc.
In principle, proofs of properties could be deduced from such models. In this
example, we do not illustrate this concept. Rather, we model a situation in
which all properties are ultimately certified by means outside the logic, e.g.,
by human judgment and sign-offs by lead engineers.
*)

Definition Smart_Home_System := Datatypes.unit.

(**
Coq's [unit] type has only one value. It's called [tt]. This value is thus the only
possible value for our system instance.
*)

Definition our_system := tt.

(**
We imagine that stakeholders in the project to develop, deploy, operate, and
evolve this system include the following (represented as members of a simple
enumerate type).
*)

Inductive Smart_Home_Stakeholder := investor | end_user | developer | maintainer | public.

(** 
For purposes of this demo, we model only one operating context, [normal]. We could
easily add a second context, such as [emergency]. We would then have to amend our
proof constructions (below) to demonstrate that the system has all the required qualities
in this new context. It's easy to write "don't care" rules, as we will see.
*)

Inductive Smart_Home_Context := normal.

(**
Finally, consistent with Boehm's proposal, we model a project with two unelaborated 
development phases, here just called [phase1] and [phase2]. The practical effect is to
ensure that Coq demands proofs of all qualities for each of these phases.
*)

Inductive Smart_Home_Phase := phase1 | phase2.

(* 
We model system-specific requirements, outside of the reusable taxonomy, as properties 
of the system being modeled along with rules for producing certificates (formally, proofs) 
that such properties hold for the given system. The modeler can provide a certification by
fiat, by adding what amount to axioms (proof constructors with no preconditions) that the
property is satisfied. Here we model two properties that will become system-specific parts
of the [PhysicalCapability] property defined by the taxonomy, and we provide axiomatic
proofs that such properties are satisfied (for all systems of type [Smart_Home_System]!)
 *)
Inductive systemCanControlFurnaceOnOffSwitch: Smart_Home_System -> Prop := 
  systemCanControlFurnaceOnOffSwitch_proof: 
    forall s: Smart_Home_System, systemCanControlFurnaceOnOffSwitch s.

Inductive systemCanControlGarageDoorOpener: Smart_Home_System -> Prop :=
  systemCanControlGarageDoorOpener_proof: 
    forall s: Smart_Home_System, systemCanControlGarageDoorOpener s.

(**
The following hint tells the Coq proof assistant about the new proof constructors 
so that it can use them in trying to automatically construct proofs of higher-level
properties.
*)

Hint Constructors systemCanControlFurnaceOnOffSwitch systemCanControlGarageDoorOpener.

(**
Now we illustrate how we parameterize the reusable taxonomic hierarchy with
out system-specific requirements. The rules encoded in the hierarchy take care
of folding proofs of low-level, detailed, system-specific properties, such as those
defined here, into top-level proofs that given systems are satisfactory. Of course
such a proof, or certificate, can only be constructed if there really are proofs of
all lower-level propositions. 
*)

Inductive physicalCapability 
  (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop := 
    physicalCapability_proof: systemCanControlFurnaceOnOffSwitch sys /\ 
    systemCanControlGarageDoorOpener sys -> 
      physicalCapability sys sh cx ps.

(**
The following many requirements plug-ins illustrate how we indicate "don't care" 
for given system qualities. In a nutshell, we provide a trivial proof constructor by
which we (or Coq) can produce certificates for all combinations of stakeholder, 
context, and phase.
*)

Inductive adaptability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    adaptability_proof: adaptability sys sh cx ps.

Inductive cyberCapability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    cyberCapability_proof: cyberCapability sys sh cx ps.

Inductive humanUsability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    humanUsability_proof: humanUsability sys sh cx ps.

(* 
Here's another example of adding a new property as a precondition for concluding
that a taxonomic property, [speed], is satisfiedl First we define a responsiveness
property of [Smart_Home_System], ...
*)

Inductive systemIsResponsive : Smart_Home_System -> Prop :=
  systemIsResponsive_proof: forall sys: Smart_Home_System, systemIsResponsive sys.

Hint Constructors systemIsResponsive.

(**
... now we add it as a precondition for concluding that a system has the
standardized [speed] quality attribute.
*)

Inductive speed (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    speed_proof: systemIsResponsive sys -> speed sys sh cx ps.

(**
Here are many more "dont' cares."
*)

Inductive endurability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    endurability_proof: endurability sys sh cx ps.

Inductive maneuverability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    maneuverability_proof: maneuverability sys sh cx ps.

Inductive accuracy (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    accuracy_proof: accuracy sys sh cx ps.

Inductive impact (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    impact_proof: impact sys sh cx ps.

Inductive scalability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    scalability_proof: scalability sys sh cx ps.

Inductive versatility (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    versatility_proof: versatility sys sh cx ps.

(* 
We formalize the concept that "a system is interoperable (has the interoperability
property) if it "can work well with other systems" (e.g., public emergency respose
systems), and can be accessed from other systems (pc, car, phone)." We provide
axiomatic certificates of these properties, and then incorporate them into the 
standardized [interoperability] quality. 
*)

Inductive systemCanWorkWithOtherSystems: Smart_Home_System -> Prop := 
  systemCanWorkWithOtherSystems_proof: 
    forall sys: Smart_Home_System, systemCanWorkWithOtherSystems sys.

Inductive systemCanBeAccessedFromOtherSystems: Smart_Home_System -> Prop :=
  systemCanBeAccessedFromOtherSystems_proof: forall sys: Smart_Home_System, 
    systemCanBeAccessedFromOtherSystems sys.

Hint Constructors systemCanWorkWithOtherSystems systemCanBeAccessedFromOtherSystems.

Inductive interoperability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    interoperability_proof: 
      systemCanWorkWithOtherSystems sys /\ 
      systemCanBeAccessedFromOtherSystems sys -> 
        interoperability sys sh cx ps.

(** 
And now here are some additional "don't cares."
*)

Inductive cost (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    cost_proof: cost sys sh cx ps.

Inductive duration (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    duration_proof: duration sys sh cx ps.

Inductive keyPersonnel (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    keyPersonnel_proof: keyPersonnel sys sh cx ps.

Inductive otherScarceResources (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    otherScareResources_proof: otherScarceResources sys sh cx ps.

Inductive manufacturability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    manufacturability_proof: manufacturability sys sh cx ps.

Inductive sustainability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    sustainability_proof: sustainability sys sh cx ps.

(* 
We formalize the property that a system as the "security" properti if
it is "difficult to hack" and "does not put the owners of the home in 
danger." We again model that these properties have been certified
by external means, as indicated by the provision of trivial proofs.
 *)

Inductive systemIsDifficultToHack: Smart_Home_System -> Prop :=
  systemIsDifficultToHack_proof: forall sys: Smart_Home_System, 
    systemIsDifficultToHack sys.

Inductive systemDoesNotHarmOwners: Smart_Home_System -> Prop :=
  systemDoesNotHarmOwners_proof: forall sys: Smart_Home_System, 
    systemDoesNotHarmOwners sys.

Hint Constructors systemIsDifficultToHack systemDoesNotHarmOwners.

Inductive security (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    security_proof: 
      systemIsDifficultToHack sys /\ 
      systemDoesNotHarmOwners sys -> 
        security sys sh cx ps.

(**
More "don't cares."
*)

Inductive safety (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    safety_proof: safety sys sh cx ps.

Inductive reliability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    reliability_proof: reliability sys sh cx ps.

Inductive maintainability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    maintainability_proof: maintainability sys sh cx ps.

Inductive availability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    availability_proof: availability sys sh cx ps.

Inductive survivability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    survivability_proof: survivability sys sh cx ps.

Inductive robustness (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    robustness_proof: robustness sys sh cx ps.

Inductive modifiability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    modifiability_proof: modifiability sys sh cx ps.

Inductive tailorability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop := 
    tailorability_proof: tailorability sys sh cx ps.


Inductive changeability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop := 
    changeability_proof: changeability sys sh cx ps.

Inductive changeability_usc (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop := 
    changeability_usc_proof: changeability_usc sys sh cx ps.

(**
We inform Coq about the new constructors that we will permit it to use in trying 
to automatically construct required proofs/certificates.
*)

Hint Constructors
     MissionEffective Dependable Flexible Changeable Efficient Affordable 
     Resilient Adaptable PhysicalCapable CyberCapable HumanUsable Speed 
     Endurable Maneuverable Accurate Impactful Scalable Versatile Interoperable 
     Cost Duration KeyPersonnel OtherScarceResources Manufacturable Sustainable 
     Secure Safe Reliable Maintainable Available Survivable Robust Modifiable Tailorable
     adaptability physicalCapability cyberCapability humanUsability speed endurability 
     maneuverability accuracy impact scalability versatility interoperability cost duration 
     keyPersonnel otherScarceResources manufacturability sustainability security safety 
     reliability maintainability availability survivability robustness modifiability tailorability 
     changeability changeability_usc.

(**
Now we reach a critical juncture. We assert that our [Smart_Home_System] is an
instance of our theory of what makes a [Satisfactory] system, as defined by the
hierarchy of (families of) propositions and  proof constructors for all of the various
system qualities. We do this without providing proofs of the second-level properties,
which Coq then demands. 
*)

Instance Smart_Home_Instance: Satisfactory Smart_Home_System 
                                                                         Smart_Home_Stakeholder 
                                                                         Smart_Home_Context 
                                                                         Smart_Home_Phase 
                                                                         our_system := 
                                                                         {}.

(** 
If the instance can be proved, then we show the given system has all required qualities.
If we cannot find proofs of this instance, then we can conclude that the system is not accepted. 
 *)
Proof.
  (* affordable *)
  constructor.
    (* mission effective *)
    constructor.

        (* physical capability *)
        constructor. 
        exists physicalCapability. 
        intros.
        destruct sh, cx, ps.
        apply physicalCapability_proof.
        split.
        apply systemCanControlFurnaceOnOffSwitch_proof.
        apply systemCanControlGarageDoorOpener_proof.
        auto. auto. auto. auto. auto. auto. auto. auto. auto.
 
        (* cyber capability, etc *) 
        constructor. exists cyberCapability. auto.
        constructor. exists humanUsability. auto.
        constructor. exists speed. auto.
        constructor. exists endurability. auto.
        constructor. exists maneuverability. auto.
        constructor. exists accuracy. auto.
        constructor. exists impact. auto.
        constructor. exists scalability. auto.
        constructor. exists versatility. auto.
        constructor. exists interoperability. auto.
    (* efficient *)
    constructor.
        constructor. exists cost. auto.
        constructor. exists duration. auto.
        constructor. exists keyPersonnel. auto.
        constructor. exists otherScarceResources. auto.
        constructor. exists manufacturability. auto.
        constructor. exists sustainability. auto.
  (* resilient *)
  constructor.
    (* dependable *)
    constructor.
      constructor. exists security. auto.
      constructor. exists safety. auto.
      constructor. exists reliability. auto.
      constructor. exists maintainability. auto.
      constructor. exists availability. auto.
      constructor. exists survivability. auto.
      constructor. exists robustness. auto.
    (* flexible *)
    constructor.
      constructor. exists modifiability. auto.
      constructor. exists tailorability. auto.
      constructor. exists adaptability. auto.
    (* changeable *)
    constructor. exists changeability. auto. 
    constructor. exists changeability_usc. auto.
Qed.

Print Smart_Home_Instance.
