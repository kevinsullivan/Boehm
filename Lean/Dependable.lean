import System
import Secure
import Safe
import Reliable
import Maintainable
import Available
import Survivable
import Robust

/- Dependable -/
/-
[Dependable] is a composite attribute of [Security], [Safety], [Reliability], ..., and [Robustness].
Informally, 
An instance of type [SystemType] is deemed [Dependable] 
if and only if all the requirements of its sub-attributes are satisfied given the same conditions.
-/

inductive Dependable (sys_type: SystemType) : Prop 
| intro : 
    Secure sys_type ->
    Safe sys_type ->
    Reliable sys_type ->
    Maintainable sys_type ->
    Available sys_type ->
    Survivable sys_type ->
    Robust sys_type ->
    Dependable 