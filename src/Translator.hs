module Translator where

import ModelChecker
import Succinct


suc2exp :: (SuccinctModel, State) -> (Model, World)
suc2exp = undefined

exp2suc :: (Model, World) -> (SuccinctModel, State)
exp2suc = undefined
-- suc2exp :: (SuccinctModel,State) -> (Model,World) -- 3.2.2 in 2017 paper
-- exp2suc :: ... -- 3.2.3 in 2017 paper
