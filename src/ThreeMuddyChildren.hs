module ThreeMuddyChildren where

import ModelChecker

-- Muddy Children
muddyModel :: Model
muddyModel =  Mo worldSpace childrenRelations

-- all possible combinations of children being muddy or not.
worldSpace :: [(Int, Assignment)]
worldSpace = [ (0, []),
               (1, [isMuddy0]),
               (2, [isMuddy1]),
               (3, [isMuddy2]),
               (4, [isMuddy0, isMuddy1]),
               (5, [isMuddy0, isMuddy2]),
               (6, [isMuddy1, isMuddy2]),
               (7, [isMuddy0, isMuddy1, isMuddy2])]

-- the agents and relations, worlds where agents are muddy are reachable from
-- worlds where they are not, given that the rest is the same. This is because
-- they do not know the state of their own muddiness. the rest is observable
childrenRelations :: [ (Agent, [[Int]]) ]
childrenRelations = [ (muddyChild0, [[0, 1], [2, 4], [3, 5], [6, 7]])
                    , (muddyChild1, [[0, 2], [1, 4], [3, 6], [5, 7]])
                    , (muddyChild2, [[0, 3], [1, 5], [2, 6], [4, 7]]) ]

-- the children, with the names of donald duck's nephews for no good reason
muddyChild0, muddyChild1, muddyChild2 :: Agent
muddyChild0 = "child0"
muddyChild1 = "child1"
muddyChild2 = "child2"

-- whether a child is muddy or not
isMuddy0, isMuddy1, isMuddy2 :: Proposition
isMuddy0 = 0
isMuddy1 = 1
isMuddy2 = 2

-- returns the model in which a announcements have been made
muddyAfter :: Int -> Model
muddyAfter 0 = muddyModel
muddyAfter 1 = muddyModel ! atLeastOneMuddy
muddyAfter k = muddyAfter (k - 1) ! nobodyKnows

atLeastOneMuddy :: Formula
atLeastOneMuddy = Dis [P isMuddy0, P isMuddy1, P isMuddy2]

nobodyKnows :: Formula
nobodyKnows = Con [ Neg $ knowWhether muddyChild0 (P isMuddy0)
                  , Neg $ knowWhether muddyChild1 (P isMuddy1)
                  , Neg $ knowWhether muddyChild2 (P isMuddy2) ]

somebodyKnows :: Formula
somebodyKnows = Dis [ knowWhether muddyChild0 (P isMuddy0)
                    , knowWhether muddyChild1 (P isMuddy1)
                    , knowWhether muddyChild2 (P isMuddy2) ]

-- NOTE: make this even nicer
findMuddyNumber :: (Model,Int) -> Int
findMuddyNumber (m,w) = if (m,w) |= somebodyKnows then 0 else loop (m ! atLeastOneMuddy, w) + 1 where
           loop (m,w) = if (m,w) |= somebodyKnows then 0 else loop (m ! nobodyKnows, w) + 1
