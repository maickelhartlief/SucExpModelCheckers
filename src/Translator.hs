module Translator where

import ExpModelChecker
import SucModelChecker
import NMuddyChildren (powerList)

import SMCDEL.Language hiding(isTrue, (|=))
import Data.List ((\\), sort, nub, delete, elem, notElem)


-- translates from a succinct model to an explicit model
-- NOTE: only works for initial models since it does not take announcements into account
suc2exp :: (SuccinctModel, State) -> (Model, World)
suc2exp (SMo v f _ sucRel, s) = (Mo worldspace rel, w) where
  worldspace = makeWorlds v f -- zip [0..] (statesOf sm)
  rel = makeExpRelations v sucRel worldspace
  w = getCurWorld worldspace s

makeWorlds :: [Prp] -> Form -> [(World, Assignment)]
makeWorlds vocab form = zip [0..] [w | w <- powerList vocab,  boolIsTrue w form]
-- use statesOf to also do non-initial models.

makeExpRelations :: [Prp] -> [(Agent, MenProg)] -> [(World, Assignment)] -> [(Agent, [[World]])]
makeExpRelations vocab relations worlds = [ (fst r, ass r worlds) | r <- relations ] where
  ass :: (Agent, MenProg) -> [(World, Assignment)] -> [[World]]
  ass _ []     = []
  ass (a,mp) (w:ws) = (fst w : map fst vs) : ass (a,mp) rest where
    vsStates = reachableFromHere vocab mp (snd w)
    vs   = filter (\wa -> snd wa `elem`    vsStates) ws
    rest = filter (\wa -> snd wa `notElem` vsStates) ws

getCurWorld :: [(World, Assignment)] -> State -> World
getCurWorld [] _ = error "actual world not found"
getCurWorld (world:rest) state = if snd world == state
                                  then fst world
                                  else getCurWorld rest state
-- getCurWorld worlds state = unsafeLookup state $ map swap worlds

-- for identical worlds, add a new proposition to make them unique
-- definition 10 in short paper. bruteforcing this by just adding a proposition for every (non-unique) world
-- definition for every world, but this will increase size of model for every translation. so do only for identical worlds
-- NOTE: assumes that worlds are ordered by valuation!
ensureUniqueValuations :: [Prp] -> [(World, Assignment)] -> ([Prp], [(World, Assignment)])
ensureUniqueValuations vocab [] = (vocab, [])
ensureUniqueValuations vocab [w] = (vocab, [w])
ensureUniqueValuations vocab (w:v:rest) = if snd w == snd v
                          then (fst x , newWorld w ++ snd x)
                          else (fst ensureRest, w : snd ensureRest) where
                            ensureRest = ensureUniqueValuations vocab (v:rest)
                            newProp = P ((number (last vocab)) + 1)
                            number  :: Prp -> Int
                            number (P n) = n
                            newWorld :: (World, Assignment) -> [(World, Assignment)]
                            newWorld world = [(fst world, snd world ++ [newProp])]
                            x = ensureUniqueValuations (vocab ++ [newProp]) (v:rest)

-- the next 2 functions are used to test ensureUniqueValuations.
uniqueTestVocabulary :: [Prp]
uniqueTestVocabulary = [P 0, P 1, P 2, P 3, P 4]

uniqueTestWorldspace :: [(World, Assignment)]
uniqueTestWorldspace = [ (0, [P 0, P 1, P 2])
                       , (1, [P 0, P 1, P 2])
                       , (2, [P 3, P 4])
                       , (3, [P 4])
                       , (4, [P 4]) ]

-- translates from a explicit model to a succinct model
-- precondition: the given model has unique valuations, i.e. no two worlds satisfy the same atoms.
exp2suc :: (Model, World) -> (SuccinctModel, State)
exp2suc (Mo worlds rel, world) = (SMo v f [] sucRel, s) where
  v = fst space
  f = makeFormula space
  sucRel = makeSucRelations v (snd space) rel
  s = getCurState worlds world
  space :: ([Prp], [(World, Assignment)])
  space = ensureUniqueValuations (makeVocabulary worlds) worlds

getCurState :: [(World, Assignment)] -> World -> State
getCurState worlds world = unsafeLookup world worlds

makeVocabulary :: [(World, Assignment)] -> [Prp]
makeVocabulary worlds = sort $ nub $ concatMap snd worlds

-- make sure to apply addAtomsToEnsureUniqueValuations before this.
-- use simplify function on this (can be taken from SMCDEL)
makeFormula :: ([Prp], [(World,Assignment)]) -> Form
makeFormula (vocabulary, worlds) = Disj [ Conj $ map PrpF a ++ map (Neg . PrpF) (vocabulary \\ a) | (_,a) <- worlds ]


-- for every agent, goes through all of
-- the lists of indistinguishable worlds and extract unknown propositions from them,
-- turning those into the mental program like so: Cap [Cup [Ass p0 Top, Ass P0 Bot], ...]
makeSucRelations :: [Prp] -> [(World, Assignment)] -> [(Agent,[[World]])] -> [(Agent, MenProg)]
makeSucRelations _ _ [] = []
makeSucRelations vocab worldspace ((ag, rel):restA) = (ag, Cup (Tst Top : makeMenProgs rel)) : makeSucRelations vocab worldspace restA where
  makeMenProgs :: [[World]] -> [MenProg]
  makeMenProgs [] = []
  makeMenProgs ([_]:rest) = makeMenProgs rest
  makeMenProgs (ws:rest) = Seq [ Tst magicFormula , changeAll , Tst magicFormula ] : makeMenProgs rest where
    relevantVocab = sort $ nub [ p | w <- ws, v <- delete w ws, p <- unsafeLookup w worldspace, p `notElem` unsafeLookup v worldspace ]
    changeAll = Seq [ Cup [ Ass p Top , Ass p Bot ] | p <- relevantVocab ]
    magicFormula = Disj (map (assignment2form vocab) (map (\w -> unsafeLookup w worldspace) ws))
    --  map (\w -> unsafeLookup w worldspace) ws == [ a | (w,a) <- worldspace, w `elem` ws]

assignment2form :: [Prp] -> Assignment -> Form
assignment2form ps a = Conj $ map PrpF a ++ map (Neg . PrpF) (ps \\ a)
