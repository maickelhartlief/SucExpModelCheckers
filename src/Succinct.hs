module Succinct where

import Data.List (elem, sort, delete, nub, union, intersect)

import ModelChecker
import NMuddyChildren (powerList)

-- (state is just world with only valuation. used in succinct models)
-- (mental program == acasibility program in DEL)
-- http://people.irisa.fr/Tristan.Charrier/AAMAS2017.pdf
-- long version: https://hal.archives-ouvertes.fr/hal-01487001/


-- Definitions of mental programs
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

-- checks whether a formula is true given an list of true propositions
boolIsTrue :: State -> Formula -> Bool
boolIsTrue _  Top       = True
boolIsTrue _  Bot       = False
boolIsTrue s (P p)      = p `elem` s
boolIsTrue a (Neg f)    = not $ boolIsTrue a f
boolIsTrue a (Con fs)   = all (boolIsTrue a) fs
boolIsTrue a (Dis fs)   = any (boolIsTrue a) fs
boolIsTrue a (Imp f g)  = not (boolIsTrue a f) || boolIsTrue a g
boolIsTrue a (Bim f g)  = boolIsTrue a f == boolIsTrue a g

-- a list with all possible states given a finite set of probabilities
allStatesFor :: [Proposition] -> [State]
allStatesFor = powerList

-- whether a state is reachable from another state (first argument is full vocabulary)
areConnected :: [Proposition] -> MenProg -> State -> State -> Bool
areConnected _ (Ass p f) s1 s2       = if boolIsTrue s1 f
                                         then union [p] s1 `setEq` s2
                                         else delete p s1 `setEq` s2
areConnected _ (Tst f) s1 s2         = s1 == s2 && boolIsTrue s1 f
areConnected _ (Seq []       ) s1 s2 = s1 == s2
areConnected v (Seq (mp:rest)) s1 s2 = or [ areConnected v (Seq rest) s3 s2 | s3 <- reachableFromHere v mp s1 ]
areConnected _ (Cup []       ) _ _   = False
areConnected v (Cup (mp:rest)) s1 s2 = areConnected v mp s1 s2 || areConnected v (Cup rest) s1 s2
areConnected _ (Cap []       ) _ _   = True
areConnected v (Cap (mp:rest)) s1 s2 = areConnected v mp s1 s2 && areConnected v (Cap rest) s1 s2
areConnected v (Inv mp       ) s1 s2 = areConnected v mp s2 s1

-- this is ugly, later we should use Data.Set or ensure States are always sorted when they are made/changed
setEq :: (Ord a, Eq a) => [a] -> [a] -> Bool
setEq xs ys = nub (sort xs) == nub (sort ys)

-- returns all states that are reachable from a certain state in a mental program
-- (first argument is full vocabulary)
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

data SuccinctModel = SMo [Proposition] Formula [(Agent, MenProg)] deriving (Eq,Ord,Show)

-- isTrue for succinct models
sucIsTrue :: (SuccinctModel, State) -> Formula -> Bool
sucIsTrue _  Top       = True
sucIsTrue _  Bot       = False
sucIsTrue (_ ,s) (P p) = p `elem` s
sucIsTrue a (Neg f)    = not $ sucIsTrue a f
sucIsTrue a (Con fs)   = and (map (sucIsTrue a) fs)
sucIsTrue a (Dis fs)   = or (map (sucIsTrue a) fs)
sucIsTrue a (Imp f g)  = not (sucIsTrue a f) || sucIsTrue a g
sucIsTrue a (Bim f g)  = sucIsTrue a f == sucIsTrue a g
-- formula should be true in all states reachable from the actual state for the
-- agent that are in the stateSpace of the model (checked for by checking if the
-- state is also true for the formula given in the SuccinctModel)
sucIsTrue (m@(SMo v fm rel), s) (Kno i f) =
  all (\s' -> sucIsTrue (m,s') f and boolIsTrue s' fm) (reachableFromHere v (unsafeLookup i rel) s)
sucIsTrue (m, s) (Ann f g)  = if sucIsTrue (m,s) f then sucIsTrue (m ! f, s) g else True

-- NOTE: doesn't work if haskell doesn't support function overloading, which i
--       think is the case. Is there another way to be able to use the same
--       shorthand for both versions of publicannouncements? classes maybe?
-- shorthand for public announcement for sucinct models
(!) :: SuccinctModel -> Formula -> SuccinctModel
(!) = sucPublicAnnounce

-- NOTE: copied from ModelChecker.hs. not modified yet
sucPublicAnnounce :: SuccinctModel -> Formula -> SuccinctModel
sucPublicAnnounce m@(SMo v _ rel) f = Mo newVal newRel where
  newVal = [ (w,v) | (w,v) <- val, (m,w) |= f ] -- exercise: write with filter using fst or snd
  newRel = [ (i, filter (/= []) $ prune parts) | (i,parts) <- rel ]
  prune :: [[Int]] -> [[Int]]
  prune [] = []
  prune (ws:rest) = [ w | w <- ws, w `elem` map fst newVal ] : prune rest






-- (Model,world) |= phi ???

-- (SuccintModel,State)  |= phi  ??

-- Model = (worlds, valuation, relation for each agent)

-- SuccintModel = (vocabulary, a boolean unsafeLookup w valformula, mental program for each agent)

-- data/type SuccintModel = ... -- see definition 8 in 2017 paper

-- example: the succinct model for 3 muddy children

-- isTrue :: (SuccinctModel,State) -> Formula -> Bool
-- interesting case: isTrue .. (K i phi) = ... using reachableFromHere!

--concat :: [[a]] -> [a]
--concat [[1,2],[3,4,5]] == [1,2,3,4,5]


-- reachableFromHere mp s = [ s' | s' <- allStates, areconnected mp s s' ]

--(p<-False  U  r<- True)  [p,q]   =  [ [q] , [p,q,r] ]

--(p<-False ; r<- True)  [p,q]   [q,r]
--         [q]methodsection

-- translate definitions of succinct models to Haskell

--meetingnotes: discussion about whether allStates are needed to make reachableFromHere work for inv
-- thesis: defining logics used from other papers and stuff. not question, method, results, but in terms of when things can be defined. bottomup approach? methodsection could be benchmarking methods and such
