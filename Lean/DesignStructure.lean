record Module :=
mk :: (elements: (list Type)) (name : string)

universe variables u
def In {A : Type u} : A -> (list A) -> Prop
| a [] := false
| a (b :: m) := b = a \/ In a m

def inModule (m: Module) (p: Type) : Prop :=
  In p m^.elements

record DesignStructure :=
mk :: (Modules : (list Module)) (Volatile : Type -> Prop) (Uses: Type -> Type -> Prop) (Satisfies : Type -> Type -> Prop)

def test_parameter : Type -> DesignStructure -> DesignStructure
| p d := { Modules := d^.Modules, Volatile:= (fun (x:Type), p = x), Uses := d^.Uses, Satisfies := d^.Satisfies}

def inDesign : DesignStructure -> Module -> Prop 
| ds m := In m ds^.Modules

inductive VolatileStar (ds : DesignStructure) (p : Type) : Prop
| VRefl : (ds^.Volatile) p -> VolatileStar
| VUse : forall b : Type, (VolatileStar ds b) -> ds^.Uses p b -> VolatileStar
--| VSatisfies : forall a b : Type, (VolatileStar ds b) -> (ds^.Satisfies a b) -> (VolatileStar ds a)