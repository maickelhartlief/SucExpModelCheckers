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

-- returns the model in which a announcements have been made
sucMuddyAfter :: Int -> SuccinctModel
sucMuddyAfter 0 = sucMuddyModel
sucMuddyAfter 1 = sucPublicAnnounce sucMuddyModel atLeastOneMuddy
sucMuddyAfter k = sucPublicAnnounce (sucMuddyAfter (k - 1)) nobodyKnows

-- finds amount of muddy children in a pointed succinct model
-- NOTE: currently always 1
sucFindMuddyNumber :: (SuccinctModel,State) -> Int
sucFindMuddyNumber (m, s) = if sucIsTrue (m, s) somebodyKnows
                          then 0
                          else loop (sucPublicAnnounce m atLeastOneMuddy, s) + 1 where
           loop (m, s) = if sucIsTrue (m, s) somebodyKnows
                          then 0
                          else loop (sucPublicAnnounce m nobodyKnows, s) + 1
