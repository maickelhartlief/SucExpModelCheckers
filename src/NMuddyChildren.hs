module NMuddyChildren where

import Data.List (sortOn,groupBy,sort,delete)

import ModelChecker

-- n children, of which m are muddy
-- returns with a list of all possible actual worlds
muddyModelFor :: Int -> Int -> (Model,[Int])
muddyModelFor n m = ( Mo worlds relations, mWorlds) where
  worlds = makeMuddyWorlds n
  relations = makeMuddyChildren worlds n
  mWorlds = getMMuddyWorlds worlds m

-- makes all possible worlds for up to n children
makeMuddyWorlds :: Int -> [ (Int, [Proposition]) ]
makeMuddyWorlds n = zip [0..] (powerList [0 .. (n-1)])

-- powerList [1,2,3] = [[1,2,3], [1,2], [1,3], [1], [2,3], [2], [3], []]
powerList :: [a] -> [[a]]
powerList []     = [ [] ]
powerList (x:xs) = [ x:rest | rest <- powerList xs ] ++ powerList xs

-- makes n children and their relations
makeMuddyChildren :: [ (Int, [Proposition]) ] -> Int -> [ (Agent, [[Int]]) ]
makeMuddyChildren worlds n = [ (makeChild k, rel) | k <- [0..(n-1)]
                                                  , let rel = makeRelations worlds k ]

-- makes childN
makeChild :: Int -> Agent
makeChild n = "child" ++ show n -- show 23 == "23"

-- makes relations for childN
makeRelations :: [ (Int, [Proposition]) ] -> Int -> [[Int]]
makeRelations worlds n = sort
                       . map (sort . map fst)
                       . groupBy (\w1 w2 -> observationAt w1 == observationAt w2)
                       . sortOn (observationAt)
                       $ worlds where
  observationAt w = delete n $ snd w

-- gets a list of all worlds in which exactly m children are muddy
getMMuddyWorlds :: [ (Int, [Proposition]) ] -> Int -> [Int]
getMMuddyWorlds [] _ = []
getMMuddyWorlds (x:rest) m = if length (snd x) == m then fst x : getMMuddyWorlds rest m else getMMuddyWorlds rest m

-- checks the number of children for the function muddyModelFor
check :: Int -> Int -> Bool
check n m = findMuddyNumbers (muddyModelFor n m) == m

-- finds the number of muddy children in several worlds in a model (should all have the same number)
findMuddyNumbers :: (Model,[Int]) -> Int
findMuddyNumbers (_, []) = -1
findMuddyNumbers (m@(Mo _ rel), w:rest) =
  if curNumber == nextNumber || nextNumber == -1
    then curNumber
    else error "not all models have the same number of muddy children" where
      curNumber = findMuddyNumber (length rel) (m, w)
      nextNumber = findMuddyNumbers (m, rest)

-- finds the number of announcements necessary in a model with n children
findMuddyNumber :: Int -> (Model,Int) -> Int
findMuddyNumber n (m,w) = if (m,w) |= somebodyKnows n then 0 else loop (m ! atLeastOneMuddy n, w) + 1 where
           loop (m,w) = if (m,w) |= somebodyKnows n then 0 else loop (m ! nobodyKnows n, w) + 1

-- formula of whether at least 1 of n children are muddy
atLeastOneMuddy :: Int -> Formula
atLeastOneMuddy n = Dis [ P k | k <- [0..(n-1)] ]

-- formula of whether none of the n children know their own state
nobodyKnows :: Int -> Formula
nobodyKnows n = Con [ Neg $ knowWhether ("child" ++ show k) (P k) | k <- [0..(n-1)] ]

-- formula of whether at least 1 of the n children know their own state
somebodyKnows :: Int -> Formula
somebodyKnows n = Dis [ knowWhether ("child" ++ show k) (P k) | k <- [0..(n-1)] ]
