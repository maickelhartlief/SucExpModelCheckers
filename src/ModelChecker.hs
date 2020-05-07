module ModelChecker where

-- Agents are represented by strings
type Agent = String

-- Propositions are represented by Ints
type Proposition = Int

-- a formula has some base cases and some operators on functions
data Formula = Top                     -- True
             | Bot                     -- False
             | P Proposition           -- proposition
             | Neg Formula             -- negation
             | Con [Formula]           -- conjunction
             | Dis [Formula]           -- disjunction
             | Imp Formula Formula     -- implication
             | Bim Formula Formula     -- bi-implication
             | Kno Agent Formula       -- knowing
             | Ann Formula Formula
             deriving (Show,Eq,Ord)
--    \phi  ::= \top | \bot | p | \phi ^ \phi

-- Assignments are a list of propositions that are true in a world
type Assignment = [Proposition]

-- Worlds are a possible reality where propositions get assigned a truth truthvalue
type World = Int

-- An explicit model is represented by a list of worlds with their assignments,
-- and a list of agents with their relations (relations: list of lists of worlds.
-- all worlds should be present exactly once, and  being in the same list means
-- the worlds are indistinguishable)
data Model = Mo [(World,Assignment)] [(Agent,[[World]])] deriving (Eq,Ord,Show)

-- diamond version of announcement: f is true and after announcing it we have g
ann :: Formula -> Formula -> Formula
ann f g = Con [f , Ann f g]

-- a version of an exiting function that returns the second of a tuple of which
-- the first in the input from a list of tuples.
myLookup :: Eq a => a -> [(a,b)] -> Maybe b
myLookup _ []       = Nothing
myLookup x (y:rest) = if x == fst y then Just (snd y) else myLookup x rest

-- version of lookup that assumes the first one of the tuple exists in the list
unsafeLookup :: Eq a => a -> [(a,b)] -> b
unsafeLookup x list = case lookup x list of
  Just y -> y
  Nothing -> undefined

-- returns all the worlds of a model
worldsOf :: Model -> [World]
worldsOf (Mo val _rel) = map fst val

-- shorthand for funstion: isTrue
(|=) :: (Model,Int) -> Formula -> Bool
(|=) = isTrue

-- returns whether a formula is true in a pointed model (a perticular world in a model)
isTrue :: (Model,Int) -> Formula -> Bool
isTrue _  Top       = True
isTrue _  Bot       = False
isTrue (Mo val _,w) (P p) = p `elem` unsafeLookup w val
isTrue a (Neg f)    = not $ isTrue a f
isTrue a (Con fs)   = and (map (isTrue a) fs)
isTrue a (Dis fs)   = or (map (isTrue a) fs)
isTrue a (Imp f g)  = not (isTrue a f) || isTrue a g
isTrue a (Bim f g)  = isTrue a f == isTrue a g
isTrue (m,w) (Kno i f) =
  all (\w' -> isTrue (m,w') f) (localState (m, w) i)
isTrue (m, w) (Ann f g)  = if isTrue (m,w) f then isTrue (m ! f, w) g else True

-- not sure anymore what this does.
-- returns worlds that are reachable for an agent from the actual world?
localState :: (Model,Int) -> Agent -> [Int]
localState (Mo _ rel,w) i = case filter (w `elem`) (unsafeLookup i rel) of
  []      -> error $ "agent " ++ i ++ " has no equivalence class"
  [set]   -> set
  -- at least 2 elements:
  (_:_:_) -> error $ "agent " ++ i ++ " has more than one equivalence class: " ++ show (unsafeLookup i rel)

-- shorthand for function: publicAnnounce
(!) :: Model -> Formula -> Model
(!) =  publicAnnounce

-- returns the new model that results from having a public announcement in a model
publicAnnounce :: Model -> Formula -> Model
publicAnnounce m@(Mo val rel) f = Mo newVal newRel where
  newVal = [ (w,v) | (w,v) <- val, (m,w) |= f ] -- exercise: write with filter using fst or snd
  newRel = [ (i, filter (/= []) $ prune parts) | (i,parts) <- rel ]
  prune :: [[Int]] -> [[Int]]
  prune [] = []
  prune (ws:rest) = [ w | w <- ws, w `elem` map fst newVal ] : prune rest

-- formula of an agent knowing whether or not a given formula is true
knowWhether :: Agent -> Formula -> Formula
knowWhether i f = Dis [ Kno i f, Kno i (Neg f) ]
