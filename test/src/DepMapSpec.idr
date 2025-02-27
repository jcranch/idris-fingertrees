import Control.App
import Control.App.Spec
import Data.Fingertree.DepMap
import Data.Vect


v2 : Vect 2 String
v2 = ["Pinky", "Perky"]
l2 : DPair Nat (flip Vect String)
l2 = MkDPair 2 v2

v3 : Vect 3 String
v3 = ["Curly", "Larry", "Moe"]
l3 : DPair Nat (flip Vect String)
l3 = MkDPair 3 v3

v3' : Vect 3 String
v3' = ["Athos", "Porthos", "Aramis"]
l3' : DPair Nat (flip Vect String)
l3' = MkDPair 3 v3'

v5 : Vect 5 String
v5 = ["Scary", "Sporty", "Posh", "Ginger", "Baby"]
l5 : DPair Nat (flip Vect String)
l5 = MkDPair 5 v5

m1 : DepMap Nat (flip Vect String)
m1 = makeDepMap a where
  a : List (DPair Nat (flip Vect String))
  a = [l2, l3, l5]

m2 : DepMap Nat (flip Vect String)
m2 = makeDepMap a where
  a : List (DPair Nat (flip Vect String))
  a = [l2, l3', l5]


-- Even though the whole chain of implementations is in scope, Idris
-- gets confused somewhere along the way. There may be syntax to
-- specify the correct implementation all in one go, but I haven't
-- worked it out.
Eq (DPair Nat (flip Vect String)) where
  p == q = (==) @{eqDPairFromDec} p q


export
spec : Spec e => App e ()
spec = describe "Data.Fingertree.DepMap" $ do
  context "lookup" $ do
    it "lookup" $ lookup 3 m1 `shouldBe` Just v3
  context "insert, Eq" $ do
    it "test equality after insert" shouldBe @{(eqDepMap @{eqKeyVal}, showDepMap)} (insert 3 v3' m1) m2
