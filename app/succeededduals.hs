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
             | Con Formula Formula     -- conjunction
             | Dis Formula Formula     -- disjunction
             | Imp Formula Formula     -- implication
             | Bim Formula Formula     -- bi-implication
             | Kno Agent Formula       -- knowing
             | Ann Formula Formula
             deriving (Show,Eq,Ord)
--    \phi  ::= \top | \bot | p | \phi ^ \phi

form :: Formula
form = Con (P pA) (P pB)

type Assignment = [Proposition]

data Model = Mo [(Int,Assignment)] [(Agent,[[Int]])] deriving (Eq,Ord,Show)

mod1, mod2, mod3 :: Model
mod1 = Mo [(0, [pA]), (1, [])] [(me, [[0, 1]])]
mod2 = Mo [(0, [pA]), (1, [pA, pB]), (2, [])]
            [(me, [[0, 1, 2]]), (jack, [[0], [1], [2]])]
mod3 = Mo [(0, [pA]), (1, [])] [(me, [[0, 1]]), (jack, [[0], [1]])]

form1, form2, form3 :: Formula
form1 = Con (P pA) (Neg $ Kno me (P pA))
form2 = Neg (Kno me (Kno jack $ Dis (P pA) (P pB)))
form3 = Con (Kno jack (Dis (P pA) (P pB)))
             (Neg (Kno me (Kno jack (Dis (P pA) (P pB)))))

myLookup :: Eq a => a -> [(a,b)] -> Maybe b
myLookup _ []       = Nothing
myLookup x (y:rest) = if x == fst y then Just (snd y) else myLookup x rest

unsafeLookup :: Eq a => a -> [(a,b)] -> b
unsafeLookup x list = fromMaybe undefined (lookup x list)

worldsOf :: Model -> [Int]
worldsOf (Mo val _rel) = map fst val

(|=) :: (Model,Int) -> Formula -> Bool
(|=) = isTrue

isTrue :: (Model,Int) -> Formula -> Bool
isTrue _  Top       = True
isTrue _  Bot       = False
isTrue (Mo val _,w) (P p) = p `elem` unsafeLookup w val
isTrue a (Neg f)    = not $ isTrue a f
isTrue a (Con f g)  = isTrue a f && isTrue a g
isTrue a (Dis f g)  = isTrue a f || isTrue a g
isTrue a (Imp f g)  = not (isTrue a f) || isTrue a g
isTrue a (Bim f g)  = isTrue a f == isTrue a g
isTrue (m@(Mo _ rel),w) (Kno i f) =
  all (\w' -> isTrue (m,w') f) (head $ filter (w `elem`) (unsafeLookup i rel))
isTrue (m, w) (Ann f g)  = if isTrue (m,w) f then isTrue (m ! f, w) g else True

(!) :: Model -> Formula -> Model
(!) =  publicAnnounce

-- NOTE: forgot what exactly the idea with fst and snd here was.
publicAnnounce :: Model -> Formula -> Model
publicAnnounce m@(Mo val rel) f = Mo newVal newRel where
  newVal = [ (w,v) | (w,v) <- val, (m,w) |= f ] -- exercise: write with filter using fst or snd
  newRel = [ (i, filter (/= []) $ prune parts) | (i,parts) <- rel ]
  prune :: [[Int]] -> [[Int]]
  prune [] = []
  prune (ws:rest) = [ w | w <- ws, w `elem` map fst newVal ] : prune rest



-- Muddy Children
muddyModel :: Model
muddyModel =  Mo worldSpace childrenRelations

-- all possible combinations of children being muddy or not.
-- NOTE: should empty set be there? is the first announcement a given?
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
childrenRelations :: [(Agent,[[Int]])]
childrenRelations = [ (muddyChild0, [[0, 1], [2, 4], [3, 5], [6, 7]]),
                      (muddyChild1, [[0, 2], [1, 4], [3, 6], [5, 7]]),
                      (muddyChild2, [[0, 3], [1, 5], [2, 6], [4, 7]])]

-- the children, with the names of donald duck's nephews for no good reason
muddyChild0, muddyChild1, muddyChild2 :: Agent
muddyChild0 = "kwik"
muddyChild1 = "kwek"
muddyChild2 = "kwak"

-- whether a child is muddy or not
isMuddy0, isMuddy1, isMuddy2 :: Proposition
isMuddy0 = 0
isMuddy1 = 1
isMuddy2 = 2

-- returns the model in which a announcements have been made
-- NOTE: I forgot "Ann" was a thing in isTrue and i instead used the
--       publicAnnounceme function directly (via the "!" infix shortcut I made)
-- NOTE: Though it passes the tests, I think I'm still taking shortcuts here:
--         1) I simply assume that at every step, the children don't know their
--            state yet. I think there should be a check for whether this is
--            actually the case, and something else should happen if so.
--         2) I'm only covering the positive isMuddyX and not their negations
announce :: Int -> Model -> Model
announce a m = if a > 0
  then announce (a - 1) m ! Con (Dis (P isMuddy0) (Dis (P isMuddy1) (P isMuddy2)))
                           (Con (Neg (Kno muddyChild0 (P isMuddy0)))
                           (Con (Neg (Kno muddyChild1 (P isMuddy1)))
                                (Neg (Kno muddyChild2 (P isMuddy2)))))
  else m

-- testing muddy children
test1, test2, test3, test4, test5, test6 :: Bool
-- child 2 is muddy. child 0 should know.
test1 = (muddyModel, 3) |= Kno muddyChild0 (P isMuddy2)

-- child 2 is muddy. child 2 should not know.
test2 = (muddyModel, 3) |= Neg (Kno muddyChild2 (P isMuddy2))

-- child 2 is muddy. 1 announcement is done. child 2 should know.
test3 = (announce 1 muddyModel, 3)
        |= Kno muddyChild2 (P isMuddy2)

-- all children are muddy. no child should know their own muddiness.
test4 = (muddyModel, 7) |= Con (Neg (Kno muddyChild0 (P isMuddy0)))
                          (Con (Neg (Kno muddyChild1 (P isMuddy1)))
                               (Neg (Kno muddyChild2 (P isMuddy2))))

-- all children are muddy. child 0 should know child 1 and 2 are muddy.
test5 = (muddyModel, 7) |= Kno muddyChild0 (Con (P isMuddy1) (P isMuddy2))

-- all children are muddy. 3 announcements are done. all children should know their own muddiness.
test6 = (announce 3 muddyModel, 7) |= Con (Kno muddyChild0 (P isMuddy0))
                                     (Con (Kno muddyChild1 (P isMuddy1))
                                          (Kno muddyChild2 (P isMuddy2)))

-- this will run all tests and write whether they passed or failed
test :: IO ()
test = putStr (unlines [s1, s2, s3, s4, s5, s6]) where
  s1 = "test1 " ++ (if test1 then "passed" else "failed")
  s2 = "test2 " ++ (if test2 then "passed" else "failed")
  s3 = "test3 " ++ (if test3 then "passed" else "failed")
  s4 = "test4 " ++ (if test4 then "passed" else "failed")
  s5 = "test5 " ++ (if test5 then "passed" else "failed")
  s6 = "test6 " ++ (if test6 then "passed" else "failed")
