record Module {params : Type} :=
mk :: (elements: (list params)) (name : string)

universe variables u
def In {A : Type u} : A -> (list A) -> Prop
| a [] := false
| a (b :: m) := b = a \/ In a m

def inModule {params : Type} (m: (@Module params)) (p: params) : Prop :=
  In p m^.elements

record DesignStructure {params : Type} :=
mk :: (Modules : (list (@Module params))) (Volatile : params -> Prop) (Uses: params -> params -> Prop) (Satisfies : params -> params -> Prop)

def test_parameter {params : Type} : params -> (@DesignStructure params) -> (@DesignStructure params)
| p d := { Modules := d^.Modules, Volatile:= (fun (x:params), p = x), Uses := d^.Uses, Satisfies := d^.Satisfies}

def inDesign {params : Type} : (@DesignStructure params) -> (@Module params) -> Prop 
| ds m := In m ds^.Modules

inductive VolatileStar {params : Type} : (@DesignStructure params) -> params ->  Prop
| VRefl : forall (ds : DesignStructure) (p : params), ds^.Volatile p -> VolatileStar ds p
| VUse : forall (ds : DesignStructure) (a b : params), VolatileStar ds b -> ds^.Uses a b -> VolatileStar ds a
| VSatisfies : forall (ds : DesignStructure) (a b : params), VolatileStar ds b -> ds^.Satisfies a b -> VolatileStar ds a

definition separate_modules {params : Type} (ds : DesignStructure) (a b: params): Prop :=
  forall m, inDesign ds m
            -> inModule m a
            -> not (inModule m b)

definition same_module {params : Type} (ds : DesignStructure) (a b: params): Prop :=
  exists m, inDesign ds m -> (inModule m a /\ inModule m b)

definition hides_volatility {params : Type} (ds : (@DesignStructure params)): Prop :=
  forall a b, ds^.Satisfies a b \/ ds^.Uses a b
              -> VolatileStar ds b
              -> same_module ds a b

definition no_cross_module_circular_use {params : Type} (ds : (@DesignStructure params)): Prop :=
  forall a b, ds^.Uses a b ->
              ds^.Uses b a ->
              not (separate_modules ds a b)

definition no_circular_satisfaction {params : Type} (ds : (@DesignStructure params)): Prop :=
  forall a b, ds^.Satisfies a b -> not (ds^.Satisfies b a)

definition modular {params : Type} (ds : (@DesignStructure params)): Prop :=
    no_circular_satisfaction ds
    /\ no_cross_module_circular_use ds
    /\ hides_volatility ds

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