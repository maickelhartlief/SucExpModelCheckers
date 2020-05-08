module Translator where

import ModelChecker
import Succinct


suc2exp :: (SuccinctModel, State) -> (Model, World)
suc2exp (sm@(SMo v f sucRel), s) = (Mo worldspace rel, w) where
  worldspace = makeWorlds v f
  rel = makeRelations sucRel worldspace
  w = getCurWorld worldspace s

makeWorlds :: [Proposition] -> Formula -> [(World, Assignment)]
makeWorlds v f = undefined

makeRelations :: [(Agent, MenProg)] -> [(World, Assignment)] -> [(Agent, [[World]])]
makeRelations ags ws = undefined

getCurWorld :: [(World, Assignment)] -> State -> World
getCurWorld = undefined


exp2suc :: (Model, World) -> (SuccinctModel, State)
exp2suc = undefined
