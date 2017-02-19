Require Export List String.


(** We represent a design structure as a set of relations parameterized over an arbitrary set 
    of parameters [params]. *)
Section DesignStructure.
  Context  {params : Set}.
  
  (** Enable dot-notation for record projections *)
  Set Printing Projections.

  (** A module is simply a named grouping of parameters *)
  Record Module : Set := mk_module {
   elements: list params;
   name: string
  }.

  (** Recursive function computing a proposition representing whether a given parameter
      is in a given module *)
  Fixpoint inModule (m: Module) (p: params): Prop :=
    In p m.(elements).

  (** The main record: A design structure consists of
       - a list of modules, [Modules]
       - a unary relation [Volatile] defining which parameters are "volatile" or likely to change
       - a binary relation [Uses] defining which parameters "use" each other
       - and a binary [Satisfies] relation defining which parameters satisfy each other *) 
  Record DesignStructure : Type := mk_ds {
    Modules : list Module;
    Volatile : params -> Prop;
    Uses : params -> params -> Prop;
    Satisfies : params -> params -> Prop
  }.

  Definition test_parameter (p: params) d := {| Modules := d.(Modules);
                                                Volatile := (fun x: params => p = x);
                                                Uses := d.(Uses);
                                                Satisfies := d.(Satisfies) |}.

  (** If everything was placed in a single module,
      it would satisfy our spec.
      TODO: Notion of cohesion ? *)

  Fixpoint inDesign (ds: DesignStructure) (m: Module): Prop :=
    In m ds.(Modules).

  (** We'd like to be able to prove certain properties of design structures, such as the fact
      that implementation details remain encapsulated, things that are likely to change are hidden
      behind stable interfaces, there are no circular dependencies across modules, and others.

      In order to prove these properties, we need some tools and relations, defined below. *) 


  (** VolatileStar is the relation we'll use to determine if a parameter has had volatility
      "leaked to it". In order to be VolatileStar, a parameter P must either
      - VRefl - Be declared volatile in the [Volatile] relation
      - VUse - Make direct use of something that is itself [VolatileStar]
      - VSatisfies - Directly satisfy the interface of something that is itself [VolatileStar] *)
  Inductive VolatileStar (ds : DesignStructure) : params -> Prop :=
  | VRefl : forall p, ds.(Volatile) p -> VolatileStar ds p
  | VUse : forall a b, VolatileStar ds b
                  -> ds.(Uses) a b
                  -> VolatileStar ds a
  | VSatisfies : forall a b, VolatileStar ds b
                        -> ds.(Satisfies) a b
                        -> VolatileStar ds a.

  (** Proposition representing whether or not a and b are in separate modules *)
  Definition separate_modules (ds : DesignStructure) (a b: params): Prop :=
    forall m, inDesign ds m
         -> inModule m a
         -> ~ inModule m b.

  (** Proposition representing whether or not a and b are in the same module.
      We need both of these, note the subtle difference between the following
      two statements:
         1) A and B do not share a module
         2) A and B are in separate modules
      If 1 is equivalent to 2, that means all parameters are in a module, which may not be true. *)
  Definition same_module (ds : DesignStructure) (a b: params): Prop :=
    exists m, inDesign ds m -> (inModule m a /\ inModule m b).

  (** Important relation over an entire design structure: states whether volatility is "leaked"
      across modules. It states, essentially, that if [A] uses or satisfies a [B] that is likely
      to change [VolatileStar], A and B must be in the same module.

      This prevents, for instance, access to a module's implementation secret from another module. *)
  Definition hides_volatility (ds : DesignStructure): Prop :=
    forall a b, ds.(Satisfies) a b \/ ds.(Uses) a b
           -> VolatileStar ds b
           -> same_module ds a b.

  (** If A and B use each other, they are not in separate modules (its easier to prove when stated this way) *)
  Definition no_cross_module_circular_use (ds : DesignStructure): Prop :=
    forall a b, ds.(Uses) a b ->
           ds.(Uses) b a ->
           ~ separate_modules ds a b.

  (** No two parameters (assumed to be interfaces here) can satisfy each other, it makes no sense. *)
  Definition no_circular_satisfaction (ds : DesignStructure): Prop :=
    forall a b, ds.(Satisfies) a b -> ~ ds.(Satisfies) b a.
  
  (** If [no_circular_satisfaction], [hides_volatility], and [no_cross_module_circular_use] are all
      satisfied, then the system is deemed "modular" *)
  Definition modular (ds : DesignStructure): Prop :=
    no_circular_satisfaction ds
    /\ no_cross_module_circular_use ds
    /\ hides_volatility ds.

  (** In order to test more specifically whether a system is modular with respect to a single
      parameter, prove the following theorem instead *)
  Definition modular_wrt (p : params) (ds : DesignStructure): Prop :=
    let ds := test_parameter p ds in
    modular ds.

  Lemma separate_commute : forall d a b, separate_modules d a b -> separate_modules d b a.
  Proof.
    unfold separate_modules.
    intros.
    specialize H with (m := m).
    intuition.
  Qed.      
      
  Unset Printing Projections.

End DesignStructure.

