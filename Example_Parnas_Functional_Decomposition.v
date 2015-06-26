Require Import DesignStructure.

(**************************Example of the proposal one *********************************)
Definition designStructure_functional_decomposition: designStructure :=
  mk_design_structure
    (mk_sys_parameter
       [EP "Computer", EP "Corpus", EP "User"]
       [DR "In Type", DR "Circ Type", DR "Alph Type", DR "Out Type", DR "In Data", DR "Circ Data", DR "Alph Data", DR "Out Data"]
       [DP "In Alg", DP "Circ Alg", DP "Out Alg", DP "Master"])
    [[false, true,  true,  false, false, false, false, true,  true,  true,  true,  true,  false, true,  true,  false],
     [false, false, false, false, false, false, false, true,  true,  true,  true,  true,  true,  true,  true,  false], 
     [false, true,  false, false, false, false, false, false, false, false, false, false, true,  true,  false, true], 
     [false, false, false, false, false, false, false, false, false, false, false, true,  false, false, false, true], 
     [false, false, false, false, false, false, false, false, false, false, false, false, true,  false, false, true], 
     [false, false, false, false, false, false, false, false, false, false, false, false, false, true,  false, true], 
     [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true,  true], 
     [false, false, false, false, false, false, false, false, true,  true,  false, true,  true,  true,  true,  false], 
     [false, false, false, false, false, false, false, true,  true,  false, false, false, false, true,  true,  false], 
     [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true,  false], 
     [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], 
     [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], 
     [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], 
     [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], 
     [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
    ].

(** Compute the direct cost of making changes to a [environmentParameter], EP "Computer" *)
Compute get_cost_ep (EP "User") (designStructure_functional_decomposition).

Compute get_cost_ep_indirect (EP "User") (designStructure_functional_decomposition).


(**************************Example of the proposal two *********************************)
Definition designStructure2_functional_decomposition: designStrucuture2 :=
  mk_design_structure2
    ([
     EPD "Computer" [false, true,  true,  false, false, false, false, true,  true,  true,  true,  true,  false, true,  true,  false],
     EPD "Corpus"   [false, false, false, false, false, false, false, true,  true,  true,  true,  true,  true,  true,  true,  false], 
     EPD "User"     [false, true,  false, false, false, false, false, false, false, false, false, false, true,  true,  false, true]
    ])
    ([ 
     DRD "In Type"   [false, false, false, false, false, false, false, false, false, false, false, true,  false, false, false, true], 
     DRD "Circ Type" [false, false, false, false, false, false, false, false, false, false, false, false, true,  false, false, true], 
     DRD "Alph Type" [false, false, false, false, false, false, false, false, false, false, false, false, false, true,  false, true], 
     DRD "Out Type"  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true,  true], 
     DRD "In Data"   [false, false, false, false, false, false, false, false, true,  true,  false, true,  true,  true,  true,  false], 
     DRD "Circ Data" [false, false, false, false, false, false, false, true,  true,  false, false, false, false, true,  true,  false], 
     DRD "Alph Data" [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true,  false], 
     DRD "Out Data"  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] 
     ])
     ([
     DPD "In Alg"   [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], 
     DPD "Circ Alg" [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], 
     DPD "Out Alg"  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], 
     DPD "Master"   [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
     ]).

