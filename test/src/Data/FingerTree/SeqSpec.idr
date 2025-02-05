import Control.App
import Control.App.Spec
import Data.Fingertree.Seq


l0 : Seq Int
l0 = fromList []

l1 : Seq Int
l1 = fromList [1]

l2 : Seq Int
l2 = fromList [1,2]

l5 : Seq Int
l5 = fromList [1,2,3,4,5]

l10 : Seq Int
l10 = fromList [1,2,3,4,5,6,7,8,9,10]


export
spec : Spec e => App e ()
spec = describe "Data.Fingertree.Seq" $ do
  context "concatenation" $ do
    it "0 vs 0" $ toList (l0 <+> l0) `shouldBe` (toList l0 <+> toList l0)
    it "0 vs 5" $ toList (l0 <+> l5) `shouldBe` (toList l0 <+> toList l5)
    it "5 vs 0" $ toList (l5 <+> l0) `shouldBe` (toList l5 <+> toList l0)
    it "1 vs 1" $ toList (l1 <+> l1) `shouldBe` (toList l1 <+> toList l1)
    it "1 vs 5" $ toList (l1 <+> l5) `shouldBe` (toList l1 <+> toList l5)
    it "5 vs 1" $ toList (l5 <+> l1) `shouldBe` (toList l5 <+> toList l1)
    it "10 vs 10" $ toList (l10 <+> l10) `shouldBe` (toList l10 <+> toList l10)
