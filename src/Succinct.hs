module Succinct where

import Data.List (elem, sort, delete, nub, union, intersect)

import ModelChecker
import NMuddyChildren (powerList)
import SMCDEL.Language hiding(isTrue, (|=))

-- (state is just world with only valuation. used in succinct models)
-- (mental program == acasibility program in DEL)
-- http://people.irisa.fr/Tristan.Charrier/AAMAS2017.pdf
-- long version: https://hal.archives-ouvertes.fr/hal-01487001/


-- Definitions of mental programs
data MenProg = Ass Prp Form -- Assign prop to truthvalue of form
             | Tst Form             -- Test form
             | Seq [MenProg]           -- Execute forms sequencially
             | Cup [MenProg]           -- execute either of the forms
             | Cap [MenProg]           -- intersection of forms
             | Inv MenProg             -- inverse of form
             deriving (Show, Eq, Ord)
-- \pi ::= p <- β | β? | (\pi ; \pi) | (\pi ∪ \pi) | (\pi ∩ \pi) | \pi^−1

-- a set of propositions that are true
type State = [Prp]

-- a Succinct representation of a model
-- third parameter [Form]: announced formulas, listed with the newest announcement first
data SuccinctModel = SMo [Prp] Form [Form] [(Agent, MenProg)] deriving (Eq,Ord,Show)

statesOf :: SuccinctModel -> [State]
statesOf (SMo vocab betaM []     _) = filter (`boolIsTrue` betaM) (allStatesFor vocab)
statesOf (SMo vocab betaM (f:fs) rel) = filter (\s -> sucIsTrue (oldModel,s) f) (statesOf oldModel) where
  oldModel = SMo vocab betaM fs rel

-- checks whether a formula is true given an list of true propositions
boolIsTrue :: State -> Form -> Bool
boolIsTrue _  Top       = True
boolIsTrue _  Bot       = False
boolIsTrue s (PrpF p)      = p `elem` s
boolIsTrue a (Neg f)    = not $ boolIsTrue a f
boolIsTrue a (Conj fs)   = all (boolIsTrue a) fs
boolIsTrue a (Disj fs)   = any (boolIsTrue a) fs
boolIsTrue a (Impl f g)  = not (boolIsTrue a f) || boolIsTrue a g
boolIsTrue a (Equi f g)  = boolIsTrue a f == boolIsTrue a g
boolIsTrue _ (K _ _) = error "This is not a boolean formula"
boolIsTrue _ (Kw _ _) = error "This is not a boolean formula"
boolIsTrue _ (PubAnnounce _ _) = error "This is not a boolean formula"
boolIsTrue _ (Xor _) = error "not implemented by this system"
boolIsTrue _ (Forall _ _) = error "not implemented by this system"
boolIsTrue _ (Exists _ _) = error "not implemented by this system"
boolIsTrue _ (Ck _ _) = error "not implemented by this system"
boolIsTrue _ (Ckw _ _) = error "not implemented by this system"
boolIsTrue _ (PubAnnounceW _ _) = error "not implemented by this system"
boolIsTrue _ (Announce _ _ _) = error "not implemented by this system"
boolIsTrue _ (AnnounceW _ _ _) = error "not implemented by this system"
boolIsTrue _ (Dia _ _) = error "not implemented by this system"

-- a list with all possible states given a finite set of probabilities
allStatesFor :: [Prp] -> [State]
allStatesFor = powerList


--
isStateOf :: State -> SuccinctModel -> Bool
isStateOf s (SMo _     betaM []     _  ) = s `boolIsTrue` betaM
isStateOf s (SMo vocab betaM (f:fs) rel) =
   sucIsTrue (oldModel,s) f && (s `isStateOf` oldModel) where
     oldModel = SMo vocab betaM fs rel

-- whether a state is reachable from another state (first argument is full vocabulary)
areConnected :: [Prp] -> MenProg -> State -> State -> Bool
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
reachableFromHere :: [Prp] -> MenProg -> State -> [State]
reachableFromHere _ (Ass p f) s = if boolIsTrue s f
                                     then [sort $ union [p] s]
                                     else [delete p s]
reachableFromHere _ (Tst f) s         = [ s | boolIsTrue s f ] -- if boolIsTrue s f then [s] else []
reachableFromHere _ (Seq []) s        = [ s ]
reachableFromHere v (Seq (mp:rest)) s = concat [ reachableFromHere v (Seq rest) s' | s' <- reachableFromHere v mp s ]
                                     -- concatMap (reachableFromHere v (Seq rest)) (reachableFromHere v mp s)
reachableFromHere _ (Cup []) _        = []
reachableFromHere v (Cup (mp:rest)) s = nub $ reachableFromHere v mp s ++ reachableFromHere v (Cup rest) s
reachableFromHere _ (Cap []) _        = []
reachableFromHere v (Cap (mp:rest)) s = reachableFromHere v (Cap rest) s `intersect` reachableFromHere v mp s
reachableFromHere v (Inv mp)        s = [ s' | s' <- allStatesFor v, areConnected v mp s' s ]

-- isTrue for succinct models
sucIsTrue :: (SuccinctModel, State) -> Form -> Bool
sucIsTrue _  Top       = True
sucIsTrue _  Bot       = False
sucIsTrue (_ ,s) (PrpF p) = p `elem` s
sucIsTrue a (Neg f)    = not $ sucIsTrue a f
sucIsTrue a (Conj fs)   = all (sucIsTrue a) fs
sucIsTrue a (Disj fs)   = any (sucIsTrue a) fs
sucIsTrue a (Impl f g)  = not (sucIsTrue a f) || sucIsTrue a g
sucIsTrue a (Equi f g)  = sucIsTrue a f == sucIsTrue a g
-- formula should be true in all states reachable from the actual state for the
-- agent that are in the stateSpace of the model (checked for by checking if the
-- state is also true for the formula given in the SuccinctModel)
--sucIsTrue (m@(SMo v _ _ rel), s) (Kno i f) =
--  all (\s' -> sucIsTrue (m,s') f) (reachableFromHere v (unsafeLookup i rel) s `intersect` statesOf m)
sucIsTrue (m@(SMo v _ _ rel), s) (K i f) =
   all
    (\s' -> sucIsTrue (m,s') f)
    (filter (`isStateOf` m) $ reachableFromHere v (unsafeLookup i rel) s)
sucIsTrue a (Kw i f) = sucIsTrue a (Disj [ K i f, K i (Neg f) ])
sucIsTrue (m, s) (PubAnnounce f g)  = not (sucIsTrue (m, s) f) ||
                              sucIsTrue(m ! f, s) g
sucIsTrue _ (Xor _) = error "not implemented by this system"
sucIsTrue _ (Forall _ _) = error "not implemented by this system"
sucIsTrue _ (Exists _ _) = error "not implemented by this system"
sucIsTrue _ (Ck _ _) = error "not implemented by this system"
sucIsTrue _ (Ckw _ _) = error "not implemented by this system"
sucIsTrue _ (PubAnnounceW _ _) = error "not implemented by this system"
sucIsTrue _ (Announce _ _ _) = error "not implemented by this system"
sucIsTrue _ (AnnounceW _ _ _) = error "not implemented by this system"
sucIsTrue _ (Dia _ _) = error "not implemented by this system"


-- NOTE: doesn't work if haskell doesn't support function overloading, which i
--       think is the case. Is there another way to be able to use the same
--       shorthand for both versions of publicannouncements? classes maybe?
-- shorthand for public announcement for sucinct models
instance UpdateAble SuccinctModel where
   (!) = sucPublicAnnounce


-- NOTE: doesn't work if typeOf doesn't work on self-made types
-- (!) :: a -> Formula -> a
-- (!) = if a `typeOf` Model then publicAnnounce
--       else if a `typeOf` SuccinctModel then sucPublicAnnounce
--       else error "only accepts Model or SuccinctModel"

-- returns the new succinct model that results from having a public announcentmin a succinct model
sucPublicAnnounce :: SuccinctModel -> Form -> SuccinctModel
sucPublicAnnounce (SMo v fm fs rel) f = SMo v fm (f:fs) rel

-- (Model,world) |= phi ???

-- (SuccintModel,State)  |= phi  ??

--concat :: [[a]] -> [a]
--concat [[1,2],[3,4,5]] == [1,2,3,4,5]

-- reachableFromHere mp s = [ s' | s' <- allStates, areconnected mp s s' ]

--(p<-False  U  r<- True)  [p,q]   =  [ [q] , [p,q,r] ]

--(p<-False ; r<- True)  [p,q]   [q,r]
--         [q]methodsection

--meetingnotes: discussion about whether allStates are needed to make reachableFromHere work for inv
-- thesis: defining logics used from other papers and stuff. not question, method, results, but in terms of when things can be defined. bottomup approach? methodsection could be benchmarking methods and such
