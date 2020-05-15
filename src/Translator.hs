module Translator where

import ModelChecker
import Succinct
import NMuddyChildren (powerList)
import Data.List (sort, nub)


-- translates from a succinct model to an explicit model
-- NOTE: only works for initial models since it does not take announcements into account
suc2exp :: (SuccinctModel, State) -> (Model, World)
suc2exp (SMo v f _ sucRel, s) = (Mo worldspace rel, w) where
  worldspace = makeWorlds v f -- zip [0..] (statesOf sm)
  rel = makeExpRelations sucRel worldspace
  w = getCurWorld worldspace s

makeWorlds :: [Proposition] -> Formula -> [(World, Assignment)]
makeWorlds vocab form = zip [0..] [w | w <- powerList vocab,  boolIsTrue w form]

makeExpRelations :: [(Agent, MenProg)] -> [(World, Assignment)] -> [(Agent, [[World]])]
makeExpRelations ags ws = undefined

getCurWorld :: [(World, Assignment)] -> State -> World
getCurWorld (world:rest) state = if snd world == state
                                  then fst world
                                  else getCurWorld rest state


-- translates from a explicit model to a succinct model
exp2suc :: (Model, World) -> (SuccinctModel, State)
exp2suc (Mo worlds expRel, world) = (SMo v f [] sucRel, s) where
  v = makeVocabulary worlds
  f = makeFormula
  sucRel = makeSucRelations
  s = getCurState

getCurState :: State
getCurState = undefined

makeVocabulary :: [(World, Assignment)] -> [Proposition]
makeVocabulary worlds = sort $ nub $ concat (map snd worlds)

makeFormula :: Formula
makeFormula = undefined

makeSucRelations :: [(Agent, MenProg)]
makeSucRelations = undefined
