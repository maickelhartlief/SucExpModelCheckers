module Main where

main :: IO ()
main = putStrLn "hallo"

type Agent = String

me, herb, jack, supervisor :: Agent
me = "Maickel"
herb = "Herb"
jack = "Jack"
supervisor = "Malvin"

type Proposition = Int

pA, pB, pC :: Proposition
pA = 0
pB = 1
pC = 2

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

-- diamond version of announcement: f is true and after announcing it we have g
ann :: Formula -> Formula -> Formula
ann f g = Con [f , Ann f g]

type Assignment = [Proposition]

data Model = Mo [(Int,Assignment)] [(Agent,[[Int]])] deriving (Eq,Ord,Show)

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


-- some test models and formulas
mod1, mod2, mod3 :: Model
mod1 = Mo [(0, [pA]), (1, [])] [(me, [[0, 1]])]
mod2 = Mo [(0, [pA]), (1, [pA, pB]), (2, [])]
            [(me, [[0, 1, 2]]), (jack, [[0], [1], [2]])]
mod3 = Mo [(0, [pA]), (1, [])] [(me, [[0, 1]]), (jack, [[0], [1]])]

form1, form2, form3 :: Formula
form1 = Con [P pA, Neg $ Kno me (P pA)]
form2 = Neg (Kno me (Kno jack $ Dis [P pA, P pB]))
form3 = Con [Kno jack (Dis [P pA, P pB]),
             Neg $ Kno me (Kno jack (Dis [P pA, P pB]))]


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

knowWhether :: Agent -> Formula -> Formula
knowWhether i f = Dis [ Kno i f, Kno i (Neg f) ]

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

-- testing muddy children
test1, test2, test3, test4, test5, test6 :: Bool
-- child 2 is muddy. child 0 should know.
test1 = (muddyModel, 3) |= Con [ P isMuddy2, Kno muddyChild0 (P isMuddy2) ]

-- child 2 is muddy. child 2 should not know.
test2 = (muddyModel, 3) |= Con [ P isMuddy2, Neg (Kno muddyChild2 (P isMuddy2)) ]

-- child 2 is muddy. after 1 announcement child 2 should know.
test3 = (muddyModel, 3) |= ann atLeastOneMuddy (Kno muddyChild2 (P isMuddy2))

-- all children are muddy. no child should know their own muddiness.
test4 = (muddyModel, 7) |= Con [ P isMuddy0, P isMuddy1, P isMuddy2, nobodyKnows ]

-- all children are muddy. child 0 should know child 1 and 2 are muddy.
test5 = (muddyModel, 7) |= Con [ P isMuddy0, P isMuddy1, P isMuddy2
                               , Kno muddyChild0 (Con [P isMuddy1, P isMuddy2])]

-- all children are muddy. after 3 announcements all children should know their own muddiness.
test6 = (muddyModel, 7) |= ann atLeastOneMuddy (ann nobodyKnows (ann nobodyKnows
                            (Con [ P isMuddy0, P isMuddy1, P isMuddy2
                                 , Kno muddyChild0 (P isMuddy0)
                                 , Kno muddyChild1 (P isMuddy1)
                                 , Kno muddyChild2 (P isMuddy2) ])))

-- NOTE: make this even nicer
findMuddyNumber :: (Model,Int) -> Int
findMuddyNumber (m,w) = if (m,w) |= somebodyKnows then 0 else loop (m ! atLeastOneMuddy, w) + 1 where
           loop (m,w) = if (m,w) |= somebodyKnows then 0 else loop (m ! nobodyKnows, w) + 1

findMuddyNumbers :: (Model,[Int]) -> Int
findMuddyNumbers (_, []) = -1
findMuddyNumbers (m, w:rest) =
  if curNumber == nextNumber || nextNumber == -1
    then curNumber
    else error "not all models have the same number of muddy children" where
      curNumber = findMuddyNumber (m, w)
      nextNumber = findMuddyNumbers (m, rest)

-- this will run all tests and write whether they passed or failed
test :: IO ()
test = putStr (unlines [s1, s2, s3, s4, s5, s6]) where
  s1 = "test1 " ++ (if test1 then "passed" else "failed")
  s2 = "test2 " ++ (if test2 then "passed" else "failed")
  s3 = "test3 " ++ (if test3 then "passed" else "failed")
  s4 = "test4 " ++ (if test4 then "passed" else "failed")
  s5 = "test5 " ++ (if test5 then "passed" else "failed")
  s6 = "test6 " ++ (if test6 then "passed" else "failed")


-- NOTE: exercises!

-- n children, of which m are muddy
-- NOTE: I chose to return a list of all worlds where m children are muddy,
--       instead of just the first.
muddyModelFor :: Int -> Int -> (Model,[Int])
muddyModelFor n m = ( Mo worlds relations, mWorlds) where
  worlds = makeMuddyWorlds n
  relations = makeNMuddyChildren worlds n
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
makeMuddyWorldforN m n worlds = makeMuddyWorldforNAux m n (take m (cycle [True]) ++ take (n - m) (cycle [False])) worlds
--makeNMuddyWorldforN _ _ _ = undefined

-- NOTE: not implemented yet!
makeMuddyWorldforNAux :: Int -> Int -> [Bool] -> [ (Int, [Proposition]) ] -> [ (Int, [Proposition]) ]
makeMuddyWorldforNAux m n curCombi ((x,_):_) = if curCombi == (take (n - m) (cycle [False]) ++ take m (cycle [True])) then [ (x + 1, assignment) ] else undefined where
  assignment = undefined

-- makes n children and their relations
-- NOTE: not implemented yet!
makeNMuddyChildren :: [ (Int, [Proposition]) ] -> Int -> [ (Agent, [[Int]]) ]
-- go through all worlds and match them with the world in which their own
-- corresponding isMuddy proposition's truthvalue is switched
makeNMuddyChildren = undefined

-- makes list of all the agents in the model
-- NOTE: n^2 where it really shouldn't have to be...
makeChildren :: Int -> [Agent]
makeChildren 0 = []
makeChildren 1 = [ "childA" ]
makeChildren n = makeChildren (n - 1) ++ [ "child" ++ [child n] ] where
  child :: Int -> Char
  child 2 = 'B'
  child n = succ (child (n - 1))

-- makes list of all the propositions in the model (1 = isMuddyA, 2 = isMuddyB, etc.)
makePropositions :: Int -> [Proposition]
makePropositions 0 = []
makePropositions n = [1..n]

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


-- practical stuff:
-- use git repository!
-- NOTE: the remote repository is called BP.

-- move tests to test and use HSpec (then you can run "stack test --coverage")
-- make benchmarks and use "stack bench"


-- next week: mental programs
-- data MenProg = ...
