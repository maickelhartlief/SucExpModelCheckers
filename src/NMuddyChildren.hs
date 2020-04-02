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
  relations = makeMuddyChildren worlds n
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
makeMuddyWorldforN m n worlds = undefined

-- makes n children and their relations
makeMuddyChildren :: [ (Int, [Proposition]) ] -> Int -> [ (Agent, [[Int]]) ]
makeMuddyChildren _ (-1) = []
makeMuddyChildren worlds 0 = [ (child, rel) | child <- makeChild 0
                                             , rel <- makeRelations worlds 0 ]
makeMuddyChildren worlds n = makeMuddyChildren worlds (n - 2) ++
                              [ (child, rel) | child <- makeChild n - 1
                                             , rel <- makeRelations worlds n - 1 ]

-- makes childN
-- NOTE: creates the entire list everytime or only once per run?
--       if first: inefficient... if second: haskell is great!
makeChild :: Int -> Agent
makeChild 0 = "childA"
makeChild n = "child" ++ [child n] where
  child :: Int -> Char
  child 1 = 'B'
  child n = succ (child (n - 1))

-- makes relations for childN
makeRelations :: [ (Int, [Proposition]) ] -> Int -> [[Int]]
makeRelations [] _ = []
makeRelations ((world, ass):nextWorld) n = [ [world, indistinct], makeRelations nextWorld ] where
  -- finds the world that is indistinguishable from 'world' for child n
  -- NOTE: not implemented yet!
  indistinct = undefined

-- makes list of all the propositions in the model (1 = isMuddyA, 2 = isMuddyB, etc.)
makePropositions :: Int -> [Proposition]
makePropositions n = [0..(n - 1)]

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
