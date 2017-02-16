import System
import Cost
import Duration
import KeyPersonnel
import OtherScarceResources
import Manufacturable
import Sustainable

inductive Efficient (sys_type: SystemType) : Prop
| intro :
    Cost sys_type ->
    Duration sys_type ->
    KeyPersonnel sys_type ->
    OtherScarceResources sys_type ->
    Manufacturable sys_type ->
    Sustainable sys_type ->
    Efficient 