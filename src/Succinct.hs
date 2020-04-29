module Succinct where

import Data.List (elem, sort, delete, nub, union, intersect)

import ModelChecker
import NMuddyChildren (powerList)

-- (state is just world with only valuation. used in succinct models)
-- (mental program == acasibility program in DEL)
-- http://people.irisa.fr/Tristan.Charrier/AAMAS2017.pdf
-- long version: https://hal.archives-ouvertes.fr/hal-01487001/


-- Definitions of mental programs
-- NOTE: not sure how this works, so most of what i made this week is guesswork.
--       from the paper I got that mental programs can take other mental programs
--       as arguments, but also formulas, so I made the F case and made the rest
--       recursive.
data MenProg = Ass Proposition Formula -- Assign prop to truthvalue of form
             | Tst Formula             -- Test form
             | Seq [MenProg]           -- Execute forms sequencially
             | Cup [MenProg]           -- execute either of the forms
             | Cap [MenProg]           -- intersection of forms
             | Inv MenProg             -- inverse of form
             deriving (Show, Eq, Ord)
-- \pi ::= p <- β | β? | (\pi ; \pi) | (\pi ∪ \pi) | (\pi ∩ \pi) | \pi^−1

-- a set of propositions that are true
type State = [Proposition]

boolIsTrue :: State -> Formula -> Bool
boolIsTrue _  Top       = True
boolIsTrue _  Bot       = False
boolIsTrue s (P p)      = p `elem` s
boolIsTrue a (Neg f)    = not $ boolIsTrue a f
boolIsTrue a (Con fs)   = and (map (boolIsTrue a) fs)
boolIsTrue a (Dis fs)   = or (map (boolIsTrue a) fs)
boolIsTrue a (Imp f g)  = not (boolIsTrue a f) || boolIsTrue a g
boolIsTrue a (Bim f g)  = boolIsTrue a f == boolIsTrue a g


allStatesFor :: [Proposition] -> [State]
allStatesFor = powerList

areConnected :: [Proposition] -> MenProg -> State -> State -> Bool
-- areConnected mp  s1 s2 = s2 `elem` reachableFromHere mp s1

-- this is ugly, later we should use Data.Set or ensure States are always sorted when they are made/changed
setEq :: (Ord a, Eq a) => [a] -> [a] -> Bool
setEq xs ys = nub (sort xs) == nub (sort ys)

-- not sure is areConnected or a modified version of boolIsTrue should be used here.
areConnected _ (Ass p f) s1 s2       = if boolIsTrue s1 f
                                         then union [p] s1 `setEq` s2
                                         else delete p s1 `setEq` s2
areConnected _ (Tst f) s1 s2         = s1 == s2 && boolIsTrue s1 f
areConnected _ (Seq []       ) s1 s2 = s1 == s2
areConnected v (Seq (mp:rest)) s1 s2 = or [ areConnected v (Seq rest) s3 s2 | s3 <- reachableFromHere v mp s1 ]
areConnected _ (Cup []       ) _ _ = False
areConnected v (Cup (mp:rest)) s1 s2 = areConnected v mp s1 s2 || areConnected v (Cup rest) s1 s2
areConnected _ (Cap []       ) _ _ = True
areConnected v (Cap (mp:rest)) s1 s2 = areConnected v mp s1 s2 && areConnected v (Cap rest) s1 s2
areConnected v (Inv mp       ) s1 s2 = areConnected v mp s2 s1
-- make testing from this?
-- example: areConnected [1,3,9] (Ass 9 Top) [1,3] [1,3,9] -- should be True
-- example: areConnected [1,3,9] (Seq [Ass 9 Top, Ass 1 Bot]) [1,3] [3,9] -- should be True
-- example: areConnected [1,3,9] (Cup [Ass 9 Top, Ass 1 Bot]) [1,3] [1,3,9] -- should be True
-- example: areConnected [1,3,9] (Cup [Ass 9 Top, Ass 1 Bot]) [1,3] [3] -- should be True
-- TODO: move these to tests/ and add some which are false

reachableFromHere :: [Proposition] -> MenProg -> State -> [State]
reachableFromHere _ (Ass p f) s = if boolIsTrue s f
                                     then [sort $ union [p] s]
                                     else [sort $ delete p s]
reachableFromHere _ (Tst f) s         = [ s | boolIsTrue s f ] -- if boolIsTrue s f then [s] else []
reachableFromHere _ (Seq []) s        = [ s ]
reachableFromHere v (Seq (mp:rest)) s = concat [ reachableFromHere v (Seq rest) s' | s' <- reachableFromHere v mp s ]
                                     -- concatMap (reachableFromHere v (Seq rest)) (reachableFromHere v mp s)
reachableFromHere _ (Cup []) s        = []
reachableFromHere v (Cup (mp:rest)) s = reachableFromHere v mp s ++ reachableFromHere v (Cup rest) s
reachableFromHere _ (Cap []) s        = []
reachableFromHere v (Cap (mp:rest)) s = intersect (reachableFromHere v mp s) (reachableFromHere v (Cap rest) s)
reachableFromHere v (Inv mp)        s = [ s' | s' <- allStatesFor v, areConnected v mp s' s ]


-- (Model,world) |= phi ???

-- (SuccintModel,State)  |= phi  ??

-- Model = (worlds, valuation, relation for each agent)

-- SuccintModel = (vocabulary, a boolean formula, mental program for each agent)

-- data/type SuccintModel = ... -- see definition 8 in 2017 paper

-- example: the succinct model for 3 muddy children

-- isTrue :: (SuccinctModel,State) -> Formula -> Bool
-- interesting case: isTrue .. (K i phi) = ... using reachableFromHere!



-- suc2exp :: (SuccinctModel,State) -> (Model,World) -- 3.2.2 in 2017 paper
-- exp2suc :: ... -- 3.2.3 in 2017 paper


--concat :: [[a]] -> [a]
--concat [[1,2],[3,4,5]] == [1,2,3,4,5]


-- reachableFromHere mp s = [ s' | s' <- allStates, areconnected mp s s' ]

--(p<-False  U  r<- True)  [p,q]   =  [ [q] , [p,q,r] ]

--(p<-False ; r<- True)  [p,q]   [q,r]
--         [q]methodsection

-- translate definitions of succinct models to Haskell

--meetingnotes: discussion about whether allStates are needed to make reachableFromHere work for inv
-- thesis: defining logics used from other papers and stuff. not question, method, results, but in terms of when things can be defined. bottomup approach? methodsection could be benchmarking methods and such
