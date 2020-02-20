-- i ordered the code linearly, which i now realize is a mistake 

module Main where

main :: IO ()
main = putStrLn "hallo"

type Agent = (String, [Proposition])

type Proposition = (String, Bool)

data Formula = Top                     -- True
             | Bot                     -- False
             | P Proposition           -- proposition
             | Con Formula Formula     -- conjunction
             | Dis Formula Formula     -- disjunction
             | Imp Formula Formula     -- implication
             | Bim Formula Formula     -- bi-implication
             | Uni Formula             -- universal quantifier
             | Exi Formula             -- existential quantifier 
             | Kno Agent Proposition   -- knowing (should this be only applicable to a Proposition)
             | Com [Agent] Proposition -- common knowledge
             deriving (Show,Eq,Ord)
--    \phi  ::= \top | \bot | p | \phi ^ \phi


type Assignment = [Proposition] -- doesn't take agents yet


-- data Model = Mo [Int] [(Int,Assignment)] [(Agent,[[Int]])]

isTrue :: Assignment -> Formula -> Bool
isTrue _ Top           = True
isTrue _ Bot           = False
isTrue a (P p)         = p `elem` a
isTrue a (Con f g)     = isTrue a f && isTrue a g
isTrue a (Dis f g)     = isTrue a f || isTrue a g
isTrue a (Imp f g)     = not (isTrue a f) || isTrue a g
isTrue a (Bim f g)     = (isTrue a f && isTrue a g) 
                      || (not (isTrue a f) && not (isTrue a g))
isTrue a (Uni f)       = all (\x -> isTrue [x] f) a -- probably wrong!
isTrue a (Exi f)       = any (\x -> isTrue [x] f) a -- also probably wrong!
isTrue _ (Kno m i)     = i `elem` snd m
isTrue _ (Com m i)     = all (\x -> i `elem` snd x) m

(|=) :: Assignment -> Formula -> Bool
(|=) = isTrue

pA, pB, pNotC :: Proposition
pA = ("a", True)
pB = ("b", True)
pNotC = ("c", False)

ass :: Assignment
ass = [pA, pB, pNotC]

form :: Formula
form = Con (P pA) (P ("a", False))

me, herb, jack, supervisor :: Agent
me = ("Maickel", [pA])
herb = ("Herb", [pB])
jack = ("Jack", [])
supervisor = ("Malvin", [pA, pB, pNotC])