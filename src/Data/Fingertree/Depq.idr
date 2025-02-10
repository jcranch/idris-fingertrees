||| Double-ended priority queues using fingertrees
|||
||| The element ordering is arbitrary, so can be used for some other
||| purpose.
module Data.Fingertree.Depq

import Data.Fingertree


record MinMax a where
  constructor MkMinMax
  maybeMin : Maybe a
  maybeMax : Maybe a

Ord a => Semigroup (MinMax a) where
  MkMinMax u1 v1 <+> MkMinMax u2 v2 = let
    u = case (u1, u2) of
      (Nothing, x) => x
      (x, Nothing) => x
      (Just x, Just y) => Just (min x y)
    v = case (v1, v2) of
      (Nothing, x) => x
      (x, Nothing) => x
      (Just x, Just y) => Just (max x y)
    in MkMinMax u v

Ord a => Monoid (MinMax a) where
  neutral = MkMinMax Nothing Nothing

Ord a => Cache (MinMax a) a where
  mval x = MkMinMax (Just x) (Just x)

export
data Depq : Type -> Type where
  MkDepq : FingerTree (MinMax x) x -> Depq x

export infixr 6 <+
export
(<+) : Ord a => a -> Depq a -> Depq a
x <+ MkDepq t = MkDepq (x <+ t)

export infixl 6 +>
export
(+>) : Ord a => Depq a -> a -> Depq a
MkDepq t +> x = MkDepq (t +> x)
