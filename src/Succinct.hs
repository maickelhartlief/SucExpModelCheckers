module NMuddyChildren where

import Data.List (elem, sort, delete, union)

import ModelChecker

-- (state is just world with only valuation. used in succinct models)
-- (mental program == acasibility program in DEL)
-- http://people.irisa.fr/Tristan.Charrier/AAMAS2017.pdf
-- long version: https://hal.archives-ouvertes.fr/hal-01487001/


-- Definitions of mental programs
-- NOTE: not sure how this works, so most of what i made this week is guesswork.
--       from the paper I got that mental programs can take other mental programs
--       as arguments, but also formulas, so I made the F case and made the rest
--       recursive.
data MenProg = F Formula
             | Ass Proposition MenProg -- Assign prop to truthvalue of form
             | Tst MenProg             -- Test form
             | Exe [MenProg]           -- Execute forms sequencially
             | Cup [MenProg]           -- execute either of the forms
             | Cap [MenProg]           -- intersection of forms
             | Inv MenProg             -- inverse of form
             deriving (Show, Eq, Ord)
-- \pi ::= p <- β | β? | (\pi ; \pi) | (\pi ∪ \pi) | (\pi ∩ \pi) | \pi^−1

type State = [Proposition]

areConnected :: MenProg -> State -> State -> Bool
areConnected mp  s1 s2 = s2 `elem` reachableFromHere mp s1
areConnected (F f) s1 s2 = undefined
-- not sure is areConnected or a modified version of isTrue should be used here.
areConnected (Ass p mp) s1 s2 = if areConnected mp s1 s2
                               then union [p] s1 == s2
                               else delete p s1 == s2
areConnected (Tst mp) s1 s2 = undefined
areConnected (Exe (mp:rest)) s1 s2 = undefined
areConnected (Cup (mp:rest)) s1 s2 = undefined
areConnected (Cap (mp:rest)) s1 s2 = undefined
areConnected (Inv mp) s1 s2 = undefined
-- example: areConnected (Set 9 True) [1,3] [1,3,9]
-- example: areConnected (Set 9 True; Set 1 False) [1,3] [3,9]
-- example: areConnected ((Set 9 True) U (Set 1 False)) [1,3] [1,3,9]
-- example: areConnected ((Set 9 True) U (Set 1 False)) [1,3] [3]


reachableFromHere :: MenProg -> State -> [State]
reachableFromHere (F f) s = undefined
reachableFromHere (Ass p mp) s = undefined
reachableFromHere (Tst mp) s = undefined
reachableFromHere (Exe (mp:rest)) s = undefined
reachableFromHere (Cup (mp:rest)) s = undefined
reachableFromHere (Cap (mp:rest)) s = undefined
reachableFromHere (Inv mp) s = undefined


-- translate definitions of succinct models to Haskell
