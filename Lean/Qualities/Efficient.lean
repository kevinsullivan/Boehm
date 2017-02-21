import ..System.System
import .Cost
import .Duration
import .KeyPersonnel
import .OtherScarceResources
import .Manufacturable
import .Sustainable

/- Efficient -/
/-
[Efficient] is parameterized by an instance of type [SystemType]. The constituent attributes of [Efficiency] are
the things it uses efficiently and whether it can be produced and maintained efficiently.
Informally, in English:
An instance of type [SystemType] is deemed [Efficient] 
if and only if all the requirements of its sub-attributes are satisfied given the same conditions.
-/

inductive Efficient (sys_type: SystemType) : Prop
| intro :
    Cost sys_type ->
    Duration sys_type ->
    KeyPersonnel sys_type ->
    OtherScarceResources sys_type ->
    Manufacturable sys_type ->
    Sustainable sys_type ->
    Efficient 