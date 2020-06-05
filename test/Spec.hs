--module Spec where

import Test.Hspec
--import Test.QuickCheck
--import Main
import ModelChecker
import ThreeMuddyChildren
import SucNMuddyChildren
--import NMuddyChildren
import Succinct

main :: IO ()
main = hspec $ do
  describe "sucFindMuddyNumber n (sucMuddyModelFor n n) == n -1" $ do
    it "n = 4" $
      (\n -> sucFindMuddyNumber n (sucMuddyModelFor n n)) 4 == 4
    it "n = 5" $
      (\n -> sucFindMuddyNumber n (sucMuddyModelFor n n)) 5 == 5
    it "n = 6" $
      (\n -> sucFindMuddyNumber n (sucMuddyModelFor n n)) 6 == 6

  -- tests isTrue
  describe "isTrue" $ do
    it "random testformula  and model 1" $
      (mod1, 0) |= form1 `shouldBe` True

    it "random testformula  and model 2" $
      (mod2, 0) |= form2 `shouldBe` True

    it "random testformula  and model 3" $
      (mod3, 0) |= form3 `shouldBe` True
  -- tests the threeMuddyChildren model with isTrue
  describe "muddyModel" $ do
    context "when child 2 is muddy" $ do
      it "child 0 knows" $
        (muddyModel, 3) |= Con [ P isMuddy2, Kno muddyChild0 (P isMuddy2) ]
        `shouldBe` True
      it "child 0 does not know" $
        (muddyModel, 3) |= Con [ P isMuddy2, Neg (Kno muddyChild2 (P isMuddy2)) ]
        `shouldBe` True
      it "child 2 should know after 1 announcement" $
        (muddyModel, 3) |= ann atLeastOneMuddy (Kno muddyChild2 (P isMuddy2))
        `shouldBe` True
    context "when all children are muddy" $ do
      it "no child knows their own muddiness" $
        (muddyModel, 7) |= Con [ P isMuddy0, P isMuddy1, P isMuddy2, nobodyKnows ]
        `shouldBe` True
      it "child 0 should know child 1 and 2 are muddy" $
        (muddyModel, 7) |= Con [ P isMuddy0, P isMuddy1, P isMuddy2
                               , Kno muddyChild0 (Con [P isMuddy1, P isMuddy2])]
        `shouldBe` True
      it "all children should know their own muddiness after 3 announcements" $
        (muddyModel, 7) |= ann atLeastOneMuddy (ann nobodyKnows (ann nobodyKnows
                                    (Con [ P isMuddy0, P isMuddy1, P isMuddy2
                                         , Kno muddyChild0 (P isMuddy0)
                                         , Kno muddyChild1 (P isMuddy1)
                                         , Kno muddyChild2 (P isMuddy2) ])))
    -- tests areConnected with boolIsTrue
    describe "areConnected" $ do
      context "connected" $ do
        it "example1" $
          areConnected [1,3,9] (Ass 9 Top) [1,3] [1,3,9]
          `shouldBe` True
        it "example2" $
          areConnected [1,3,9] (Seq [Ass 9 Top, Ass 1 Bot]) [1,3] [3,9]
          `shouldBe` True
        it "example3" $
          areConnected [1,3,9] (Cup [Ass 9 Top, Ass 1 Bot]) [1,3] [1,3,9]
          `shouldBe` True
        it "example4" $
          areConnected [1,3,9] (Cup [Ass 9 Top, Ass 1 Bot]) [1,3] [3]
          `shouldBe` True

-- some random test formulas
form1, form2, form3 :: Formula
form1 = Con [P pA, Neg (Kno me (P pA))]
form2 = Neg (Kno me (Kno jack $ Dis [P pA, P pB]))
form3 = Con [ Kno jack (Dis [P pA, P pB])
             , Neg $ Kno me (Kno jack (Dis [P pA, P pB])) ]

-- some random test models
mod1, mod2, mod3 :: Model
mod1 = Mo [(0, [pA]), (1, [])] [(me, [[0, 1]])]
mod2 = Mo [(0, [pA]), (1, [pA, pB]), (2, [])]
          [(me, [[0, 1, 2]]), (jack, [[0], [1], [2]])]
mod3 = Mo [(0, [pA]), (1, [])] [(me, [[0, 1]]), (jack, [[0], [1]])]

-- some random propositions
pA, pB, pC :: Proposition
pA = 0
pB = 1
pC = 2

-- some random agents
me, herb, jack, supervisor :: Agent
me = "Maickel"
herb = "Herb"
jack = "Jack"
supervisor = "Malvin"
