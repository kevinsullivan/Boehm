/- We represent a design structure as a set of relations parameterized over an arbitrary set 
    of parameters [params]. -/

/- A module is simply a named grouping of parameters -/
record Module {params : Type} :=
mk :: (elements: (list params)) (name : string)

/- Prop that an element is in a list -/
universe variables u
def In {A : Type u} : A -> (list A) -> Prop
| a [] := false
| a (b :: m) := b = a \/ In a m

/- Recursive function computing a proposition representing whether a given parameter
      is in a given module -/
def inModule {params : Type} (m: (@Module params)) (p: params) : Prop :=
  In p m^.elements

/- The main record: A design structure consists of
       - a list of modules, [Modules]
       - a unary relation [Volatile] defining which parameters are "volatile" or likely to change
       - a binary relation [Uses] defining which parameters "use" each other
       - and a binary [Satisfies] relation defining which parameters satisfy each other -/
record DesignStructure {params : Type} :=
mk :: (Modules : (list (@Module params))) 
      (Volatile : params -> Prop) 
      (Uses: params -> params -> Prop) 
      (Satisfies : params -> params -> Prop)

def test_parameter {params : Type} : params -> (@DesignStructure params) -> (@DesignStructure params)
| p d := { Modules := d^.Modules, Volatile:= (fun (x:params), p = x), Uses := d^.Uses, Satisfies := d^.Satisfies}

/-    If everything was placed in a single module,
      it would satisfy our spec.
      TODO: Notion of cohesion ? -/
def inDesign {params : Type} : (@DesignStructure params) -> (@Module params) -> Prop 
| ds m := In m ds^.Modules


/-    We'd like to be able to prove certain properties of design structures, such as the fact
      that implementation details remain encapsulated, things that are likely to change are hidden
      behind stable interfaces, there are no circular dependencies across modules, and others.
      In order to prove these properties, we need some tools and relations, defined below. -/


/-    VolatileStar is the relation we'll use to determine if a parameter has had volatility
      "leaked to it". In order to be VolatileStar, a parameter P must either
      - VRefl - Be declared volatile in the [Volatile] relation
      - VUse - Make direct use of something that is itself [VolatileStar]
      - VSatisfies - Directly satisfy the interface of something that is itself [VolatileStar] -/
inductive VolatileStar {params : Type} : (@DesignStructure params) -> params ->  Prop
| VRefl : forall (ds : DesignStructure) (p : params), ds^.Volatile p -> VolatileStar ds p
| VUse : forall (ds : DesignStructure) (a b : params), VolatileStar ds b -> ds^.Uses a b -> VolatileStar ds a
| VSatisfies : forall (ds : DesignStructure) (a b : params), VolatileStar ds b -> ds^.Satisfies a b -> VolatileStar ds a

/- Proposition representing whether or not a and b are in separate modules -/
definition separate_modules {params : Type} (ds : DesignStructure) (a b: params): Prop :=
  forall m, inDesign ds m
            -> inModule m a
            -> not (inModule m b)
/-    Proposition representing whether or not a and b are in the same module.
      We need both of these, note the subtle difference between the following
      two statements:
         1) A and B do not share a module
         2) A and B are in separate modules
      If 1 is equivalent to 2, that means all parameters are in a module, which may not be true. -/
definition same_module {params : Type} (ds : DesignStructure) (a b: params): Prop :=
  exists m, inDesign ds m -> (inModule m a /\ inModule m b)

/-    Important relation over an entire design structure: states whether volatility is "leaked"
      across modules. It states, essentially, that if [A] uses or satisfies a [B] that is likely
      to change [VolatileStar], A and B must be in the same module.
      This prevents, for instance, access to a module's implementation secret from another module. -/
definition hides_volatility {params : Type} (ds : (@DesignStructure params)): Prop :=
  forall a b, ds^.Satisfies a b \/ ds^.Uses a b
              -> VolatileStar ds b
              -> same_module ds a b
/-    If A and B use each other, they are not in separate modules (its easier to prove when stated this way) -/
definition no_cross_module_circular_use {params : Type} (ds : (@DesignStructure params)): Prop :=
  forall a b, ds^.Uses a b ->
              ds^.Uses b a ->
              not (separate_modules ds a b)

/-    No two parameters (assumed to be interfaces here) can satisfy each other, it makes no sense. -/
definition no_circular_satisfaction {params : Type} (ds : (@DesignStructure params)): Prop :=
  forall a b, ds^.Satisfies a b -> not (ds^.Satisfies b a)

/-    If [no_circular_satisfaction], [hides_volatility], and [no_cross_module_circular_use] are all
      satisfied, then the system is deemed "modular" -/
definition modular {params : Type} (ds : (@DesignStructure params)): Prop :=
    no_circular_satisfaction ds
    /\ no_cross_module_circular_use ds
    /\ hides_volatility ds


/-    In order to test more specifically whether a system is modular with respect to a single
      parameter, prove the following theorem instead -/
definition modular_wrt {params : Type} (p : params) (ds : (@DesignStructure params)): Prop :=
    let ds := test_parameter p ds in
      modular ds

lemma separate_commute {params : Type} : forall (d : (@DesignStructure params)) (a b : params), separate_modules d a b -> separate_modules d b a :=
begin
    unfold separate_modules,    
    intros,    
    unfold not,
    intros,
    apply a_1,
    apply a_2,
    apply a_4,
    apply a_3
end  