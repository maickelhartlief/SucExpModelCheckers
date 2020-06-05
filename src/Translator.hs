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

-- by symposium: preliminary results (sucinct vs. symbolic&explicit) not entire thesis yet :)
-- week after symposium: full thesis draft!
-- final version whenever-ish (month later?)
-- system: translator implement todo's. undefinfed. make faster!! (allstatesfor and other things) (using data.map instead of lists of tuples) (maybe do intermediate checks to prune earlier. probably wouldn't work) (make know whether primitive)
-- run profiler to see what functions need speeding up. ^
-- system optional after deadline: compatible with SMCDEL
-- benchmark changes from now on. "this change changed speed from X to Y."
-- make benchmark automatic. (as far as possible) results should be (easily) reproducable (SMCDEL has example)
-- benchmark SMCDEL to get an idea (and a graph)

-- fix all warnings

--   hlint --report src/ && firefox report.html

--   stack test --profile --test-arguments "--match sucFindMuddyNumber"
{-
Fri Jun  5 14:56 2020 Time and Allocation Profiling Report  (Final)

   my-project-test +RTS -N -p -RTS --match sucFindMuddyNumber

total time  =        2.76 secs   (11041 ticks @ 1000 us, 4 processors)
total alloc = 7,458,474,144 bytes  (excludes profiling overheads)

COST CENTRE       MODULE       SRC                                 %time %alloc

reachableFromHere Succinct     src/Succinct.hs:(77,1)-(88,93)       50.9   88.3
sucIsTrue         Succinct     src/Succinct.hs:(92,1)-(108,41)      25.5    0.0
unsafeLookup      ModelChecker src/ModelChecker.hs:(53,1)-(55,22)   16.1    0.8
isStateOf         Succinct     src/Succinct.hs:(37,1)-(39,35)        5.6    9.0
sucIsTrue.\       Succinct     src/Succinct.hs:105:15-32             0.8    1.8
-}
