inductive kwicContexts 
| nominal

inductive kwicPhases 
| design 
| implementation 
| maintenance

inductive kwicStakeholders 
| developer 
| customer

record kwicValue :=
mk :: (modulesChanged: nat)

inductive computerState 
| computer_pre 
| computer_post

inductive corpusState 
| corpus_pre 
| corpus_post.

inductive userState 
| user_pre 
| user_post.

record kwicVolatileState := 
mk :: (computer_state: computerState) (corpus_state: corpusState) (user_state: userState)
