module Data.Fingertree.Seq

import Data.Filterable
import Data.Filterable.Indexed
import Data.Functor.Indexed
import Data.Witherable.Indexed

import Data.Fingertree


public export
Semigroup Nat where
  x <+> y = x + y

public export
Monoid Nat where
  neutral = 0

public export
data Counted : Type -> Type where
  Count : a -> Counted a

public export
Cache Nat (Counted a) where
  mval _ = 1

public export
Functor Counted where
  map f (Count x) = Count (f x)

public export
Foldable Counted where
  foldl f z (Count x) = f z x
  foldr f z (Count x) = f x z

public export
Traversable Counted where
  traverse f (Count x) = Count <$> f x


public export
data Seq : Type -> Type where
  MkSeq : FingerTree Nat (Counted a) -> Seq a

public export
Semigroup (Seq a) where
  MkSeq u <+> MkSeq v = MkSeq (u <+> v)

export
Monoid (Seq a) where
  neutral = MkSeq neutral

public export
fromList : List a -> Seq a
fromList = MkSeq . listToTree . map Count

public export
Functor Seq where
  map f (MkSeq t) = MkSeq (tmap (convert id) (map f) t)

-- Defined early so that we can use it for <*> as well as for =<<.

public export
Foldable Seq where
  foldl f i (MkSeq t) = foldl' (\x, (Count a) => f x a) i t
  foldr f i (MkSeq t) = foldr' (\(Count a), x => f a x) i t

monadBind : Seq a -> (a -> Seq b) -> Seq b
monadBind l f = concatMap f l

public export
Applicative Seq where
  pure x = MkSeq . single $ Count x
  a <*> b = monadBind a (\f => map f b)

public export
Monad Seq where
  (>>=) = monadBind

-- Would probably rather have a streaming process
public export
Filterable Seq where
  mapMaybe f = fromList . Prelude.List.mapMaybe f . toList

public export
Traversable Seq where
  traverse f (MkSeq s) = MkSeq <$> ttraverse (convert id) (traverse f) s

public export
IndFunctor Nat Seq where
  imap f (MkSeq t) = MkSeq $ treeLAccumMap (convert id) (map . f) 0 t


{-
public export
IndFoldable Nat Seq where

public export
IndTraversable Nat Seq where
-}


-- It's not IndFilterable (or IndWitherable) as filtering changes the
-- indices, but we supply the analogous functionality anyway.

public export
seqFilter : (Nat -> a -> Maybe b) -> Seq a -> Seq b
seqFilter g = fromList . enumFilter g . toList

public export
seqWither : Applicative f => (Nat -> a -> f (Maybe b)) -> Seq a -> f (Seq b)
seqWither g = map fromList . enumWither g . toList
