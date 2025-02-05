module Data.Fingertree.DepMap

import Decidable.Equality

import Data.Functor.Dependent

import Data.Fingertree
import Data.Vect

-- TODO Should probably cache sizes as well as intervals covered.

export
subst : {v : k -> Type} -> x = y -> v x -> v y
subst Refl u = u

export
[eqDPairFromDec] {v : k -> Type} -> (DecEq k, {x : k} -> Eq (v x)) => Eq (DPair k v) where
  MkDPair k1 v1 == MkDPair k2 v2 = case decEq k1 k2 of
    Yes p => subst {v = v} p v1 == v2
    No _ => False

export
Show Ordering where
  show EQ = "EQ"
  show LT = "LT"
  show GT = "GT"

{-
[decDPairFromDec] {v : k -> Type} -> (DecEq k, {x : k} -> DecEq (v x)) => DecEq (DPair k v) where
  decEq (MkDPair k1 v1) (MkDPair k2 v2) = case decEq k1 k2 of
    Yes r => case r of
      Refl => case decEq v1 v2 of
        Yes s => case s of
          Refl => Yes Refl
        No s => No (s . ?wtf)
    No r => No (r . cong fst)
-}

data Interval : Type -> Type where
    MkInterval : Maybe (k, k) -> Interval k

interval : k -> k -> Interval k
interval a b = MkInterval (Just (a, b))

Eq k => Eq (Interval k) where
    MkInterval a == MkInterval b = a == b

Semigroup (Interval k) where
    MkInterval (Just (a,_)) <+> MkInterval (Just (_,d)) = MkInterval (Just (a,d))
    MkInterval x <+> MkInterval Nothing = MkInterval x
    MkInterval Nothing <+> MkInterval x = MkInterval x

Monoid (Interval k) where
    neutral = MkInterval Nothing

rangeFind : Ord k => k -> Interval k -> Interval k -> Ordering
rangeFind a (MkInterval Nothing) (MkInterval (Just (_,y))) = if y < a then GT else EQ
rangeFind a (MkInterval (Just (_,x))) (MkInterval (Just (_,y))) = if y < a then GT else if x < a then EQ else LT
rangeFind _ _ _ = EQ -- Unlikely to be used


record KeyVal (k : Type) (v : k -> Type) where
  constructor MkKeyVal
  toDPair : DPair k v

DepFunctor k (KeyVal k) where
  dmap f (MkKeyVal p) = MkKeyVal $ dmap f p

Cache (Interval k) (KeyVal k v) where
    mval (MkKeyVal p) = MkInterval (Just (fst p,fst p))

[eqKeyVal] Eq (DPair k v) => Eq (KeyVal k v) where
    MkKeyVal p1 == MkKeyVal p2 = p1 == p2

Show (DPair k v) => Show (KeyVal k v) where
    show (MkKeyVal p) = "(MkKeyVal " <+> show p <+> ")"


export
data DepMap : (k : Type) -> (k -> Type) -> Type where
    MkDepMap : FingerTree (Interval k) (KeyVal k v) -> DepMap k v

extract : DecEq k => {v : k -> Type} -> (x : k) -> KeyVal k v -> Maybe (v x)
extract x (MkKeyVal (MkDPair y a)) = case decEq y x of
    Yes p => Just (subst {v = v} p a)
    No _  => Nothing

export
splitAt : (DecEq k, Ord k) => {v : k -> Type} -> (x : k) -> DepMap k v -> (DepMap k v, Maybe (v x), DepMap k v)
splitAt x (MkDepMap t) = let
    (l, a, r) = splitBy (rangeFind x) t
    a' = case a of
        Nothing => Nothing
        Just p  => extract x p
    in (MkDepMap l, a', MkDepMap r)

export
lookup : (DecEq k, Ord k) => {v : k -> Type} -> (x : k) -> DepMap k v -> Maybe (v x)
lookup x (MkDepMap t) = case lookupBy (rangeFind x) t of
    (_, Nothing) => Nothing
    (_, Just p)  => extract x p

export
empty : DepMap k v
empty = MkDepMap neutral

export
insert : Ord k => (x : k) -> v x -> DepMap k v -> DepMap k v
insert x v (MkDepMap t) = let (l,_,r) = splitBy (rangeFind x) t
    in MkDepMap (l <+> (MkKeyVal (x ** v) <+ r))

export
makeDepMap : (Ord k, Foldable t) => t (DPair k v) -> DepMap k v
makeDepMap = foldl (\m, (MkDPair x y) => insert x y m) empty

export
{0 k : Type} -> DepFunctor k (DepMap k) where
  dmap f (MkDepMap t) = MkDepMap $ tmap (convert id) (dmap f) t

export
elems : DepMap k v -> List (DPair k v)
elems (MkDepMap t) = map toDPair (treeToList t)

export
[showDepMap] Show (DPair k v) => Show (DepMap k v) where
  show m = "makeDepMap " <+> show (elems m)

export
[eqDepMap] Eq (KeyVal k v) => Eq (DepMap k v) where
  MkDepMap t1 == MkDepMap t2 = (==) @{eqFingerTree} t1 t2
