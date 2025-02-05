module Data.Fingertree.IntIntervals

import Data.Fingertree


||| Intervals of integers
|||
||| MkIval 0 10 represents 0,..,9
public export
record Interval where
  constructor MkIval
  start : Int
  end : Int

export
length : Interval -> Int
length (MkIval m n) = n-m

export
Semigroup Interval where
  MkIval a1 b1 <+> MkIval a2 b2 = MkIval (min a1 a2) (max b1 b2)

public export
record Span where
  constructor MkSpan
  spanIval : Maybe Interval
  spanSize : Int

export
Semigroup Span where
  MkSpan (Just i) u <+> MkSpan (Just j) v = MkSpan (Just (i <+> j)) (u+v)
  MkSpan Nothing _ <+> s = s
  s <+> MkSpan Nothing _ = s

export
Monoid Span where
  neutral = MkSpan Nothing 0

export
Cache Span Interval where
  mval i = MkSpan (Just i) (length i)

export
data IntervalTree : Type where
  MkITree : FingerTree Interval Span -> IntervalTree


{-
export
mergePieces : List (FTPiece Interval Span) -> List (FTPiece Interval Span) -> List (FTPiece Interval Span)
mergePieces [] n = n
mergePieces m [] = m
mergePieces a@(ah::at) b@(bh::bt) = case (spanIval (mval ah), spanIval (mval bh)) of
  (Nothing, _) => mergePieces at b
  (_, Nothing) => mergePieces a bt
  (Just ai, Just bi) => case compare (start ai) (start bi) of
    LT => ah::mergePieces at b
    GT => bh::mergePieces a bt
    EQ => ?what
union : IntervalTree -> IntervalTree -> IntervalTree
union (MkITree t1) (MkITree t2) = MkITree . putBackTogether $ mergePieces [TreePiece t1] [TreePiece t2]
-}
