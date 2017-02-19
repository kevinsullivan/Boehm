-- Context 
inductive kwicContexts 
| nominal

-- Phase 
-- [kwicPhases] represents the lifecycle phases of a software system.
-- design, implementation and maintenance are talked about in the paper
inductive kwicPhases 
| design 
| implementation 
| maintenance

-- Stakeholder
-- [kwicStakeholders] represents the set of potential system change agents
inductive kwicStakeholders 
| developer 
| customer

-- Value for measuring cost-benefit
-- [kwicValue] is a framework for quantifying time, money, and other
-- elements of value that can be gained or lost as a result of a change.
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
