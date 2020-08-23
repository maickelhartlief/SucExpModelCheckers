module ModelChecker where

import Data.Maybe
import SMCDEL.Language hiding(isTrue, (|=))

class UpdateAble a where
  (!) :: a -> Form -> a

instance UpdateAble Model where
  (!) = publicAnnounce

-- Assignments are a list of propositions that are true in a world
type Assignment = [Prp]

-- Worlds are a possible reality where propositions get assigned a truth truthvalue
type World = Int

-- An explicit model is represented by a list of worlds with their assignments,
-- and a list of agents with their relations (relations: list of lists of worlds.
-- all worlds should be present exactly once, and  being in the same list means
-- the worlds are indistinguishable)
data Model = Mo [(World,Assignment)] [(Agent,[[World]])] deriving (Eq,Ord,Show)

-- diamond version of announcement: f is true and after announcing it we have g
ann :: Form -> Form -> Form
ann f g = Conj [f , PubAnnounce f g]

-- a version of an exiting function that returns the second of a tuple of which
-- the first in the input from a list of tuples.
myLookup :: Eq a => a -> [(a,b)] -> Maybe b
myLookup _ []       = Nothing
myLookup x (y:rest) = if x == fst y then Just (snd y) else myLookup x rest

-- version of lookup that assumes the first one of the tuple exists in the list
unsafeLookup :: Eq a => a -> [(a,b)] -> b
unsafeLookup x list = Data.Maybe.fromMaybe undefined (lookup x list)

-- returns all the worlds of a model
worldsOf :: Model -> [World]
worldsOf (Mo val _rel) = map fst val

-- shorthand for funstion: isTrue
(|=) :: (Model,World) -> Form -> Bool
(|=) = isTrue

-- returns whether a Form is true in a pointed model (a perticular world in a model)
isTrue :: (Model,Int) -> Form -> Bool
isTrue _  Top       = True
isTrue _  Bot       = False
isTrue (Mo val _,w) (PrpF p) = p `elem` unsafeLookup w val
isTrue a (Neg f)    = not $ isTrue a f
isTrue a (Conj fs)   = all (isTrue a) fs
isTrue a (Disj fs)   = any (isTrue a) fs
isTrue a (Impl f g)  = not (isTrue a f) || isTrue a g
isTrue a (Equi f g)  = isTrue a f == isTrue a g
isTrue (m, w) (K i f) =
  all
    (\w' -> isTrue (m,w') f)
    (localState (m, w) i)
isTrue a (Kw i f) = isTrue a (Disj [ K i f, K i (Neg f) ])
isTrue (m, w) (PubAnnounce f g)  = not (isTrue (m,w) f) ||
                           isTrue (m ! f, w) g
isTrue _ (Xor _) = error "not implemented by this system"
isTrue _ (Forall _ _) = error "not implemented by this system"
isTrue _ (Exists _ _) = error "not implemented by this system"
isTrue _ (Ck _ _) = error "not implemented by this system"
isTrue _ (Ckw _ _) = error "not implemented by this system"
isTrue _ (PubAnnounceW _ _) = error "not implemented by this system"
isTrue _ (Announce _ _ _) = error "not implemented by this system"
isTrue _ (AnnounceW _ _ _) = error "not implemented by this system"
isTrue _ (Dia _ _) = error "not implemented by this system"

-- returns worlds that are reachable for an agent from the actual world?
localState :: (Model,Int) -> Agent -> [Int]
localState (Mo _ rel,w) i = case filter (w `elem`) (unsafeLookup i rel) of
  []      -> error $ "agent " ++ i ++ " has no equivalence class"
  [set]   -> set
  -- at least 2 elements:
  (_:_:_) -> error $ "agent " ++ i ++ " has more than one equivalence class: " ++ show (unsafeLookup i rel)

-- returns the new model that results from having a public announcement in a model
publicAnnounce :: Model -> Form -> Model
publicAnnounce m@(Mo val rel) f = Mo newVal newRel where
  newVal = [ (w,v) | (w,v) <- val, (m,w) |= f ]
  newRel = [ (i, filter (/= []) $ prune parts) | (i,parts) <- rel ]
  prune :: [[Int]] -> [[Int]]
  prune = map (\ws -> [w | w <- ws, w `elem` map fst newVal])

-- WAS PUT INTO ISTRUE AS Kw
-- Form of an agent knowing whether or not a given Form is true
-- knowWhether :: Agent -> Form -> Form
-- knowWhether i f = Disj [ K i f, K i (Neg f) ]


-- approach 1: fork  SMCDEL and add my stuff. drawbacks: will be very big and long to compile after every change.

-- add SMCDEL as package. only import language module. use Form datatype from SMCDEL instead of my own.

-- translator change or add. between SMCDEL explicit and my succinct.

-- add to stack and dependencies
-- import SMCDEL.language into modelchecker and
