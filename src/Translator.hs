module Translator where

import ModelChecker
import Succinct
import NMuddyChildren (powerList)
import Data.List ((\\), sort, nub)


-- translates from a succinct model to an explicit model
-- NOTE: only works for initial models since it does not take announcements into account
suc2exp :: (SuccinctModel, State) -> (Model, World)
suc2exp (SMo v f _ sucRel, s) = (Mo worldspace rel, w) where
  worldspace = makeWorlds v f -- zip [0..] (statesOf sm)
  rel = makeExpRelations v sucRel worldspace
  w = getCurWorld worldspace s

makeWorlds :: [Proposition] -> Formula -> [(World, Assignment)]
makeWorlds vocab form = zip [0..] [w | w <- powerList vocab,  boolIsTrue w form]
-- use statesOf to also do non-initial models.

makeExpRelations :: [Proposition] -> [(Agent, MenProg)] -> [(World, Assignment)] -> [(Agent, [[World]])]
makeExpRelations vocab relations worlds = [ (fst r, ass r worlds) | r <- relations ] where
  ass :: (Agent, MenProg) -> [(World, Assignment)] -> [[World]]
  ass (a,mp) []     = []
  ass (a,mp) (w:ws) = [ fst w : map fst vs ] ++ ass (a,mp) rest where
    vsStates = reachableFromHere vocab mp (snd w)
    vs   = filter (\wa -> snd wa `elem`    vsStates) ws
    rest = filter (\wa -> snd wa `notElem` vsStates) ws

getCurWorld :: [(World, Assignment)] -> State -> World
getCurWorld [] _ = error "actual world not found"
getCurWorld (world:rest) state = if snd world == state
                                  then fst world
                                  else getCurWorld rest state
-- getCurWorld worlds state = unsafeLookup state $ map swap worlds

-- checks whether model has only worlds with unique valuations
hasUniqueValuations :: Model -> Bool
hasUniqueValuations = undefined

-- for identical worlds, add a new proposition to make them unique
-- definition 10 in short paper. bruteforcing this by just adding a proposition for every (non-unique) world
-- definition for every world, but this will increase size of model for every translation. so do only for identical worlds
addAtomsToEnsureUniqueValuations :: Model -> Model
addAtomsToEnsureUniqueValuations = undefined

-- translates from a explicit model to a succinct model
-- precondition: the given model has unique valuations, i.e. no two worlds satisfy the same atoms.
exp2suc :: (Model, World) -> (SuccinctModel, State)
exp2suc (Mo worlds expRel, world) = (SMo v f [] sucRel, s) where
  v = makeVocabulary worlds
  f = makeFormula v worlds
  sucRel = makeSucRelations
  s = getCurState worlds world

getCurState :: [(World, Assignment)] -> World -> State
getCurState worlds world = unsafeLookup world worlds

makeVocabulary :: [(World, Assignment)] -> [Proposition]
makeVocabulary worlds = sort $ nub $ concatMap snd worlds

-- make sure to apply addAtomsToEnsureUniqueValuations before this.
-- use simplify function on this (can be taken from SMCDEL)
makeFormula :: [Proposition] -> [(World,Assignment)] -> Formula
makeFormula vocabulary worlds = Dis [ Con $ (map P a) ++ (map (Neg . P) (vocabulary \\ a)) | (w,a) <- worlds ]

makeSucRelations :: [(Agent, MenProg)]
makeSucRelations = undefined

-- NOTE: AT LEAST AS MANY LATEXLINES AS CODELINES :C
