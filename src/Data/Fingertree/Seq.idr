module Data.Fingertree.Seq

import Data.Filterable
import Data.Filterable.Indexed
import Data.Functor.Indexed
import Data.Witherable.Indexed

import Data.Fingertree


Semigroup Nat where
    x <+> y = x + y

Monoid Nat where
    neutral = 0

data Counted : Type -> Type where
    Count : a -> Counted a

Cache Nat (Counted a) where
    mval _ = 1

Functor Counted where
    map f (Count x) = Count (f x)

Foldable Counted where
  foldl f z (Count x) = f z x
  foldr f z (Count x) = f x z

Traversable Counted where
    traverse f (Count x) = Count <$> f x


data Seq : Type -> Type where
    MkSeq : FingerTree Nat (Counted a) -> Seq a

Semigroup (Seq a) where
    MkSeq u <+> MkSeq v = MkSeq (u <+> v)

export
Monoid (Seq a) where
    neutral = MkSeq neutral

fromList : List a -> Seq a
fromList = MkSeq . listToTree . map Count

export
Functor Seq where
    map f (MkSeq t) = MkSeq (tmap (convert id) (map f) t)

-- Defined early so that we can use it for <*> as well as for =<<.

export
Foldable Seq where
    foldl f i (MkSeq t) = foldl' (\x, (Count a) => f x a) i t
    foldr f i (MkSeq t) = foldr' (\(Count a), x => f a x) i t

monadBind : Seq a -> (a -> Seq b) -> Seq b
monadBind l f = concatMap f l

export
Applicative Seq where
    pure x = MkSeq . single $ Count x
    a <*> b = monadBind a (\f => map f b)

export
Monad Seq where
    (>>=) = monadBind

-- Would probably rather have a streaming process
export
Filterable Seq where
    mapMaybe f = fromList . Prelude.List.mapMaybe f . toList

export
Traversable Seq where
  traverse f (MkSeq s) = MkSeq <$> ttraverse (convert id) (traverse f) s

export
IndFunctor Nat Seq where
    imap f (MkSeq t) = MkSeq $ treeLAccumMap (convert id) (map . f) 0 t

{-
export
IndFoldable Nat Seq where

export
IndTraversable Nat Seq where
-}

-- It's not IndFilterable (or IndWitherable) as filtering changes the
-- indices, but we supply the analogous functionality anyway.

enumFilter : (Nat -> a -> Maybe b) -> Seq a -> Seq b
enumFilter g = fromList . enumFilter g . toList

enumWither : Applicative f => (Nat -> a -> f (Maybe b)) -> Seq a -> f (Seq b)
enumWither g = map fromList . enumWither g . toList


{-
namespace Tests

  export
  testConcat : IO ()
  testConcat = foldlM (const t) () [| MkPair l l |] where

    l : Seq (Seq Int)
    l = fromList [fromList [],
                  fromList [1],
                  fromList [1,2],
                  fromList [1,2,3,4,5],
                  fromList [1,2,3,4,5,6,7,8,9,10]]

    t : (Seq Int, Seq Int) -> IO ()
    t (a,b) = toList (a <+> b) `shouldBe` (toList a <+> toList b)
-}
