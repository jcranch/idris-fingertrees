module Data.Fingertree.RealIntervals

import Data.Fingertree


||| Intervals
public export
data Ival : Type -> Type where
  MkIval : a -> a -> Ival a

export
Ord a => Semigroup (Ival a) where
  MkIval a1 b1 <+> MkIval a2 b2 = MkIval (min a1 a2) (max b1 b2)

||| Intervals, wrapped to provide the "union" monoid structure (where
||| i <+> j is the smallest interval containing i and j).
public export
data Span : Type -> Type where
  MkSpan : Maybe (Ival a) -> Span a

export
Ord a => Semigroup (Span a) where
  MkSpan (Just i) <+> MkSpan (Just j) = MkSpan (Just (i <+> j))
  MkSpan Nothing <+> s = s
  s <+> MkSpan Nothing = s

export
Ord a => Monoid (Span a) where
  neutral = MkSpan Nothing


||| Endpoint types
public export
data Closure = Open | Closed


data RealIvals : Closure -> Closure -> Type -> Type where
  MkRealIvals : FingerTree (Ival a) (Span a, a) -> RealIvals l r a
