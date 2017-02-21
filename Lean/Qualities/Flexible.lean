import SystemModel.System
import Qualities.Modifiable
import Qualities.Tailorable
import Qualities.Adaptable

/- Flexible-/
/-
Boehm stipulates that, " ...The three means for achieving the end parent class of
Flexibility are Modifiability, Tailorability, and Adaptability."
-/

/-
[Flexible] is a composite attribute of [Modifiable], [Tailorable], and [Adaptable].
Informally, 
An instance of type [SystemType] is deemed [Dependable] 
if and only if all the requirements of its sub-attributes are satisfied given the same conditions.
-/

inductive Flexible (sys_type: SystemType) : Prop
| intros:
    Modifiable sys_type ->
    Tailorable sys_type ->
    Adaptable sys_type ->
    Flexible 