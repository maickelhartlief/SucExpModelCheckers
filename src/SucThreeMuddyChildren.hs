module SucThreeMuddyChildren  where

import Succinct
import ModelChecker
import ThreeMuddyChildren

-- Muddy Children
sucMuddyModel :: SuccinctModel
sucMuddyModel =  SMo vocabulary muddyForm agentProg

-- all probabilities
vocabulary :: [Proposition]
vocabulary = [isMuddy0, isMuddy1, isMuddy2]

-- formula to generate worldspace
muddyForm :: Formula
-- muddyForm = Dis [P isMuddy0, P isMuddy1, P isMuddy2]
muddyForm = Top

-- all children and what they know represented by a mental program
agentProg :: [(Agent, MenProg)]
agentProg = [ (muddyChild0, Cup [Ass isMuddy0 Top, Ass isMuddy0 Bot])
            , (muddyChild1, Cup [Ass isMuddy1 Top, Ass isMuddy1 Bot])
            , (muddyChild2, Cup [Ass isMuddy2 Top, Ass isMuddy2 Bot]) ]

-- NOTE: suc! is a placeholder for now. public announcements return a Model,
--       and there is no version yet that returns a SuccinctModel

-- returns the model in which a announcements have been made
sucMuddyAfter :: Int -> SuccinctModel
sucMuddyAfter 0 = sucMuddyModel
sucMuddyAfter 1 = sucMuddyModel ! atLeastOneMuddy
sucMuddyAfter k = sucMuddyAfter (k - 1) ! nobodyKnows

-- finds amount of muddy children in a pointed succinct model
findMuddyNumber :: (SuccinctModel,State) -> Int
findMuddyNumber (m,w) = if (m,w) |= somebodyKnows then 0 else loop (m ! atLeastOneMuddy, w) + 1 where
           loop (m,w) = if (m,w) |= somebodyKnows then 0 else loop (m ! nobodyKnows, w) + 1
