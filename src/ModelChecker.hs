module ModelChecker
    ( Agent(..)
    , Proposition(..)
    , Formula(..)
    , ann
    , Assignment(..)
    , Model(..)
    , myLookup
    , unsafeLookup
    , worldsOf
    , (|=)
    , isTrue
    , localState
    , (!)
    , publicAnnounce
    ) where

      type Agent = String

      type Proposition = Int

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

      type Assignment = [Proposition]

      data Model = Mo [(Int,Assignment)] [(Agent,[[Int]])] deriving (Eq,Ord,Show)

      -- diamond version of announcement: f is true and after announcing it we have g
      ann :: Formula -> Formula -> Formula
      ann f g = Con [f , Ann f g]

      myLookup :: Eq a => a -> [(a,b)] -> Maybe b
      myLookup _ []       = Nothing
      myLookup x (y:rest) = if x == fst y then Just (snd y) else myLookup x rest

      unsafeLookup :: Eq a => a -> [(a,b)] -> b
      unsafeLookup x list = case lookup x list of
        Just y -> y
        Nothing -> undefined

      worldsOf :: Model -> [Int]
      worldsOf (Mo val _rel) = map fst val

      (|=) :: (Model,Int) -> Formula -> Bool
      (|=) = isTrue

      isTrue :: (Model,Int) -> Formula -> Bool
      isTrue _  Top       = True
      isTrue _  Bot       = False
      isTrue (Mo val _,w) (P p) = p `elem` unsafeLookup w val
      isTrue a (Neg f)    = not $ isTrue a f
      isTrue a (Con fs)   = and (map (isTrue a) fs)
      isTrue a (Dis fs)   = or (map (isTrue a) fs)
      isTrue a (Imp f g)  = not (isTrue a f) || isTrue a g
      isTrue a (Bim f g)  = isTrue a f == isTrue a g
      isTrue (m@(Mo _ _),w) (Kno i f) =
        all (\w' -> isTrue (m,w') f) (localState (m, w) i)
      isTrue (m, w) (Ann f g)  = if isTrue (m,w) f then isTrue (m ! f, w) g else True

      localState :: (Model,Int) -> Agent -> [Int]
      localState (Mo _ rel,w) i = case filter (w `elem`) (unsafeLookup i rel) of
        []      -> error $ "agent " ++ i ++ " has no equivalence class"
        [set]   -> set
        -- at least 2 elements:
        (_:_:_) -> error $ "agent " ++ i ++ " has more than one equivalence class: " ++ show (unsafeLookup i rel)


      (!) :: Model -> Formula -> Model
      (!) =  publicAnnounce

      publicAnnounce :: Model -> Formula -> Model
      publicAnnounce m@(Mo val rel) f = Mo newVal newRel where
        newVal = [ (w,v) | (w,v) <- val, (m,w) |= f ] -- exercise: write with filter using fst or snd
        newRel = [ (i, filter (/= []) $ prune parts) | (i,parts) <- rel ]
        prune :: [[Int]] -> [[Int]]
        prune [] = []
        prune (ws:rest) = [ w | w <- ws, w `elem` map fst newVal ] : prune rest

      -- practical stuff:
      -- use git repository!
      -- NOTE: the remote repository is called BP.

      -- move tests to test and use HSpec (then you can run "stack test --coverage")
      -- make benchmarks and use "stack bench"


      -- next week: mental programs
      -- data MenProg = ...
