module NMuddyChildren
    ( muddyModelFor
    , makeMuddyWorlds
    , makeMuddyWorldsAux
    , makeMuddyWorldforN
    , makeMuddyWorldforNAux
    , makeNMuddyChildren
    , makeChildren
    , makePropositions
    , getMMuddyWorlds
    , check
    , findMuddyNumbers
    ) where

import ModelChecker
import ThreeMuddyChildren

-- n children, of which m are muddy
-- NOTE: I chose to return a list of all worlds where m children are muddy,
--       instead of just the first.
muddyModelFor :: Int -> Int -> (Model,[Int])
muddyModelFor n m = ( Mo worlds relations, mWorlds) where
  worlds = makeMuddyWorlds n
  relations = makeNMuddyChildren worlds n
  mWorlds = getMMuddyWorlds worlds m

-- makes all possible worlds for up to n children
makeMuddyWorlds :: Int -> [ (Int, [Proposition]) ]
makeMuddyWorlds 0 = [ (0, []) ]
makeMuddyWorlds n = (makeMuddyWorldforN n n worldList) ++ worldList  where
  worldList = makeMuddyWorldsAux (n - 1) n

-- auxiliary function for makeNMuddyWorlds that remembers the total number n.
makeMuddyWorldsAux :: Int -> Int -> [ (Int, [Proposition]) ]
makeMuddyWorldsAux m n = makeMuddyWorldforN m n worldList ++ worldList where
  worldList = makeMuddyWorldsAux (m - 1) n

-- makes all possible worlds for exactly n children
-- NOTE: not implemented yet!
makeMuddyWorldforN :: Int -> Int -> [ (Int, [Proposition]) ] -> [ (Int, [Proposition]) ]
makeMuddyWorldforN m n worlds = makeMuddyWorldforNAux m n (take m (cycle [True]) ++ take (n - m) (cycle [False])) worlds
--makeNMuddyWorldforN _ _ _ = undefined

-- NOTE: not implemented yet!
makeMuddyWorldforNAux :: Int -> Int -> [Bool] -> [ (Int, [Proposition]) ] -> [ (Int, [Proposition]) ]
makeMuddyWorldforNAux m n curCombi ((x,_):_) = if curCombi == (take (n - m) (cycle [False]) ++ take m (cycle [True])) then [ (x + 1, assignment) ] else undefined where
  assignment = undefined

-- makes n children and their relations
-- NOTE: not implemented yet!
makeNMuddyChildren :: [ (Int, [Proposition]) ] -> Int -> [ (Agent, [[Int]]) ]
-- go through all worlds and match them with the world in which their own
-- corresponding isMuddy proposition's truthvalue is switched
makeNMuddyChildren = undefined

-- makes list of all the agents in the model
-- NOTE: n^2 where it really shouldn't have to be...
makeChildren :: Int -> [Agent]
makeChildren 0 = []
makeChildren 1 = [ "childA" ]
makeChildren n = makeChildren (n - 1) ++ [ "child" ++ [child n] ] where
  child :: Int -> Char
  child 2 = 'B'
  child n = succ (child (n - 1))

-- makes list of all the propositions in the model (1 = isMuddyA, 2 = isMuddyB, etc.)
makePropositions :: Int -> [Proposition]
makePropositions 0 = []
makePropositions n = [1..n]

-- gets a list of all worlds in which exactly m children are muddy
getMMuddyWorlds :: [ (Int, [Proposition]) ] -> Int -> [Int]
getMMuddyWorlds [] _ = []
getMMuddyWorlds (x:rest) m = if length (snd x) == m then fst x : getMMuddyWorlds rest m else getMMuddyWorlds rest m

-- benchmark this!
-- use :
-- λ> :set +s
-- λ> ...
-- ...
-- (0.01 secs, 112,200 bytes)
check :: Int -> Int -> Bool
check n m = findMuddyNumbers (muddyModelFor n m) == m

findMuddyNumbers :: (Model,[Int]) -> Int
findMuddyNumbers (_, []) = -1
findMuddyNumbers (m, w:rest) =
  if curNumber == nextNumber || nextNumber == -1
    then curNumber
    else error "not all models have the same number of muddy children" where
      curNumber = findMuddyNumber (m, w)
      nextNumber = findMuddyNumbers (m, rest)
