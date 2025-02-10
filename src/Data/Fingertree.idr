module Data.Fingertree

-- TODO Write a more general-purpose tree splitters
-- Can want something which may return a split (like lookup), or something that will definitely return a split
-- Might want to pass the valuations through monoid homomorphisms (in case they're expensive, and not being scrutinised)


||| A Cache is something which stores data of type a, which has a
||| monoidal valuation of type m.
public export
interface Monoid m => Cache m a | a where
    mval : a -> m

||| An "Uncached a" stores type a, with trivial monoidal valuation
public export
data Uncached : Type -> Type where
    MkUncached : a -> Uncached a

export
Eq a => Eq (Uncached a) where
  MkUncached x == MkUncached y = x == y

export
Show a => Show (Uncached a) where
  show (MkUncached x) = "(MkUncached " <+> show x <+> ")"

export
Cache () (Uncached a) where
    mval _ = ()


||| Foldable objects can be used as Caches. We use this below for List
(Cache m a, Foldable f) => Cache m (f a) where
  mval = concatMap mval


data Node : Type -> Type -> Type where
    Node2 : a -> a -> m -> Node m a
    Node3 : a -> a -> a -> m -> Node m a

node2 : Cache m a => a -> a -> Node m a
node2 x y = Node2 x y $ mval [x, y]

node3 : Cache m a => a -> a -> a -> Node m a
node3 x y z = Node3 x y z $ mval [x, y, z]

Cache m a => Cache m (Node m a) where
    mval (Node2 _ _ m) = m
    mval (Node3 _ _ _ m) = m


nodeToList : Node m a -> List a
nodeToList (Node2 x y _) = [x, y]
nodeToList (Node3 x y z _) = [x, y, z]


data Digit : Type -> Type -> Type where
    Digit1 : a -> Digit m a
    Digit2 : a -> a -> m -> Digit m a
    Digit3 : a -> a -> a -> m -> Digit m a
    Digit4 : a -> a -> a -> a -> m -> Digit m a

Cache m a => Cache m (Digit m a) where
    mval (Digit1 w) = mval w
    mval (Digit2 _ _ c) = c
    mval (Digit3 _ _ _ c) = c
    mval (Digit4 _ _ _ _ c) = c

digit2 : Cache m a => a -> a -> Digit m a
digit2 y z = Digit2 y z $ mval [y, z]

digit3 : Cache m a => a -> a -> a -> Digit m a
digit3 x y z = Digit3 x y z $ mval [x, y, z]

digit4 : Cache m a => a -> a -> a -> a -> Digit m a
digit4 w x y z = Digit4 w x y z $ mval [w, x, y, z]

nodeToDigit : Node m a -> Digit m a
nodeToDigit (Node2 x y c) = Digit2 x y c
nodeToDigit (Node3 x y z c) = Digit3 x y z c

digitToList : Digit m a -> List a
digitToList (Digit1 w) = [w]
digitToList (Digit2 w x _) = [w,x]
digitToList (Digit3 w x y _) = [w,x,y]
digitToList (Digit4 w x y z _) = [w,x,y,z]

digitlcut : Cache m a => Digit m a -> (a, Maybe (Digit m a))
digitlcut (Digit1 w) = (w, Nothing)
digitlcut (Digit2 w x _) = (w, Just (Digit1 x))
digitlcut (Digit3 w x y _) = (w, Just (digit2 x y))
digitlcut (Digit4 w x y z _) = (w, Just (digit3 x y z))

digitrcut : Cache m a => Digit m a -> (Maybe (Digit m a), a)
digitrcut (Digit1 z) = (Nothing, z)
digitrcut (Digit2 y z _) = (Just (Digit1 y), z)
digitrcut (Digit3 x y z _) = (Just (digit2 x y), z)
digitrcut (Digit4 w x y z _) = (Just (digit3 w x y), z)

digitToNodes : Cache m a => Digit m a -> Either a (List (Node m a))
digitToNodes (Digit1 w) = Left w
digitToNodes (Digit2 w x c) = Right [Node2 w x c]
digitToNodes (Digit3 w x y c) = Right [Node3 w x y c]
digitToNodes (Digit4 w x y z _) = Right [node2 w x, node2 y z]

twoDigitsToNodes : Cache m a => Digit m a -> Digit m a -> List (Node m a)
twoDigitsToNodes l r = case (l,r) of

    (Digit1 x1, Digit1 y1) => [node2 x1 y1]
    (Digit2 x1 x2 _, Digit1 y1) => [node3 x1 x2 y1]
    (Digit3 x1 x2 x3 _, Digit1 y1) => [node2 x1 x2, node2 x3 y1]
    (Digit4 x1 x2 x3 x4 _, Digit1 y1) => [node2 x1 x2, node3 x3 x4 y1]

    (Digit1 x1, Digit2 y1 y2 _) => [node3 x1 y1 y2]
    (Digit2 x1 x2 c, Digit2 y1 y2 d) => [Node2 x1 x2 c, Node2 y1 y2 d]
    (Digit3 x1 x2 x3 c, Digit2 y1 y2 d) => [Node3 x1 x2 x3 c, Node2 y1 y2 d]
    (Digit4 x1 x2 x3 x4 _, Digit2 y1 y2 d) => [node2 x1 x2, node2 x3 x4, Node2 y1 y2 d]

    (Digit1 x1, Digit3 y1 y2 y3 _) => [node2 x1 y1, node2 y2 y3]
    (Digit2 x1 x2 c, Digit3 y1 y2 y3 d) => [Node2 x1 x2 c, Node3 y1 y2 y3 d]
    (Digit3 x1 x2 x3 c, Digit3 y1 y2 y3 d) => [Node3 x1 x2 x3 c, Node3 y1 y2 y3 d]
    (Digit4 x1 x2 x3 x4 _, Digit3 y1 y2 y3 d) => [node2 x1 x2, node2 x3 x4, Node3 y1 y2 y3 d]

    (Digit1 x1, Digit4 y1 y2 y3 y4 _) => [node3 x1 y1 y2, node2 y3 y4]
    (Digit2 x1 x2 c, Digit4 y1 y2 y3 y4 _) => [Node2 x1 x2 c, node2 y1 y2, node2 y3 y4]
    (Digit3 x1 x2 x3 c, Digit4 y1 y2 y3 y4 _) => [Node3 x1 x2 x3 c, node2 y1 y2, node2 y3 y4]
    (Digit4 x1 x2 x3 x4 _, Digit4 y1 y2 y3 y4 d) => [node3 x1 x2 x3, node2 x4 y1, node3 y2 y3 y4]


export
data FingerTree : Type -> Type -> Type where
    Empty : FingerTree m a
    Single : a -> FingerTree m a
    Deep : Digit m a -> FingerTree m (Node m a) -> Digit m a -> m -> FingerTree m a

export
single : a -> FingerTree m a
single = Single

export
Cache m a => Cache m (FingerTree m a) where
    mval Empty = neutral
    mval (Single x) = mval x
    mval (Deep _ _ _ c) = c


deep : Cache m a => Digit m a -> FingerTree m (Node m a) -> Digit m a -> FingerTree m a
deep l t r = Deep l t r (mval l <+> mval t <+> mval r)

export
listToTree : Cache m a => List a -> FingerTree m a
listToTree [] = Empty
listToTree [x1] = Single x1
listToTree (x1::x2::xs) = let (r,t) = inner x2 xs in deep (Digit1 x1) (listToTree t) r where
  inner : Cache n b => b -> List b -> (Digit n b, List (Node n b))
  inner y1 [] = (Digit1 y1, [])
  inner y1 [y2] = (digit2 y1 y2, [])
  inner y1 [y2,y3] = (digit3 y1 y2 y3, [])
  inner y1 (y2::y3::y4::ys) = map (node3 y1 y2 y3 ::) (inner y4 ys)

digitToTree : Cache m a => Digit m a -> FingerTree m a
digitToTree (Digit1 x) = Single x
digitToTree (Digit2 x y c) = Deep (Digit1 x) Empty (Digit1 y) c
digitToTree (Digit3 x y z c) = Deep (Digit1 x) Empty (digit2 y z) c
digitToTree (Digit4 w x y z c) = Deep (digit2 w x) Empty (digit2 y z) c

nodeToTree : Cache m a => Node m a -> FingerTree m a
nodeToTree (Node2 x y c) = Deep (Digit1 x) Empty (Digit1 y) c
nodeToTree (Node3 x y z c) = Deep (Digit1 x) Empty (digit2 y z) c

||| A FingerTree with two elements only
pair : Cache m a => a -> a -> FingerTree m a
pair x y = deep (Digit1 x) Empty (Digit1 y)

export infixr 6 <+
||| Left append
export
(<+) : Cache m a => a -> FingerTree m a -> FingerTree m a
x <+ Empty = Single x
x <+ Single y = pair x y
x <+ Deep (Digit1 y) t r _ = deep (digit2 x y) t r
x <+ Deep (Digit2 y1 y2 _) t r _ = deep (digit3 x y1 y2) t r
x <+ Deep (Digit3 y1 y2 y3 _) t r _ = deep (digit4 x y1 y2 y3) t r
x <+ Deep (Digit4 y1 y2 y3 y4 _) t r _ = deep (digit2 x y1) (node3 y2 y3 y4 <+ t) r

export infixl 6 +>
||| Right append
export
(+>) : Cache m a => FingerTree m a -> a -> FingerTree m a
Empty +> y = Single y
Single x +> y = deep (Digit1 x) Empty (Digit1 y)
Deep l t (Digit1 x) _ +> y = deep l t (digit2 x y)
Deep l t (Digit2 x1 x2 _) _ +> y = deep l t (digit3 x1 x2 y)
Deep l t (Digit3 x1 x2 x3 _) _ +> y = deep l t (digit4 x1 x2 x3 y)
Deep l t (Digit4 x1 x2 x3 x4 _) _ +> y = deep l (t +> node3 x1 x2 x3) (digit2 x4 y)


export infixl 6 <++
export
(<++) : Cache m a => List a -> FingerTree m a -> FingerTree m a
l <++ t = foldr (<+) t l

export infixl 6 ++>
export
(++>) : Cache m a => FingerTree m a -> List a -> FingerTree m a
t ++> l = foldl (+>) t l


export
Cache m a => Semigroup (FingerTree m a) where
    Empty <+> t = t
    Single x <+> t = x <+ t
    t <+> Empty = t
    t <+> Single x = t +> x
    Deep l1 t1 r1 _ <+> Deep l2 t2 r2 _ = let
        t = (t1 ++> twoDigitsToNodes r1 l2) <+> t2
        in deep l1 t r2

export
Cache m a => Monoid (FingerTree m a) where
    neutral = Empty


export
lview : Cache m a => FingerTree m a -> Maybe (a, FingerTree m a)
lview Empty = Nothing
lview (Single x) = Just (x, Empty)
lview (Deep (Digit1 x) t r _) = Just (x, f (lview t)) where
    f : Maybe (Node m a, FingerTree m (Node m a)) -> FingerTree m a
    f Nothing = case digitlcut r of
         (y, Nothing) => Single y
         (y, Just r') => deep (Digit1 y) Empty r'
    f (Just (n, t')) = deep (nodeToDigit n) t' r
lview (Deep (Digit2 x1 x2 _) t r _) = Just (x1, deep (Digit1 x2) t r)
lview (Deep (Digit3 x1 x2 x3 _) t r _) = Just (x1, deep (digit2 x2 x3) t r)
lview (Deep (Digit4 x1 x2 x3 x4 _) t r _) = Just (x1, deep (digit3 x2 x3 x4) t r)

export
rview : Cache m a => FingerTree m a -> Maybe (FingerTree m a, a)
rview Empty = Nothing
rview (Single x) = Just (Empty, x)
rview (Deep l t (Digit1 x) _) = Just (f (rview t), x) where
    f : Maybe (FingerTree m (Node m a), Node m a) -> FingerTree m a
    f Nothing = case digitrcut l of
        (Nothing, y) => Single y
        (Just l', y) => deep l' Empty (Digit1 y)
    f (Just (t', n)) = deep l t' (nodeToDigit n)
rview (Deep l t (Digit2 y1 y2 _) _) = Just (deep l t (Digit1 y1), y2)
rview (Deep l t (Digit3 y1 y2 y3 _) _) = Just (deep l t (digit2 y1 y2), y3)
rview (Deep l t (Digit4 y1 y2 y3 y4 _) _) = Just (deep l t (digit3 y1 y2 y3), y4)

-- Rebuild a fingertree with a possible non-digit on the left
assemblel : Cache m a => List a -> FingerTree m (Node m a) -> Digit m a -> FingerTree m a
assemblel [] t r = case lview t of
    Nothing => digitToTree r
    Just (n, t') => deep (nodeToDigit n) t' r
assemblel [z] t r = deep (Digit1 z) t r
assemblel [y,z] t r = deep (digit2 y z) t r
assemblel [x,y,z] t r = deep (digit3 x y z) t r
assemblel [w,x,y,z] t r = deep (digit4 w x y z) t r
assemblel (x::xs) t r = x <+ assemblel xs t r

-- Rebuild a fingertree with a possible non-digit on the right
assembler : Cache m a => Digit m a -> FingerTree m (Node m a) -> List a -> FingerTree m a
assembler l t [] = case rview t of
    Nothing => digitToTree l
    Just (t', n) => deep l t' (nodeToDigit n)
assembler l t [z] = deep l t (Digit1 z)
assembler l t [y,z] = deep l t (digit2 y z)
assembler l t [x,y,z] = deep l t (digit3 x y z)
assembler l t (w::x::y::z::xs) = deep l t (digit4 w x y z) ++> xs


parameters (w : m -> m -> Ordering)
  lookupByList : Cache m a => m -> List a -> (m, Maybe a)
  lookupByList a [] = (a, Nothing)
  lookupByList a (x::xs) = let
    a' = a <+> mval x
    in case w a a' of
      LT => (a, Nothing)
      EQ => (a, Just x)
      GT => lookupByList a' xs

  lookupByTree : Cache m a => m -> FingerTree m a -> (m, Maybe a)
  lookupByTree a Empty = (a, Nothing)
  lookupByTree a0 (Single x) = let
    a1 = a0 <+> mval x
    in case w a0 a1 of
      LT => (a0, Nothing)
      EQ => (a0, Just x)
      GT => (a1, Nothing)
  lookupByTree a0 (Deep l t r c) = let
    a1 = a0 <+> mval l
    in case w a0 a1 of
      LT => (a0, Nothing)
      EQ => lookupByList a0 (digitToList l)
      GT => let
        a2 = a1 <+> mval t
        in case w a1 a2 of
          LT => (a1, Nothing)
          EQ => case lookupByTree a1 t of
            (a', Nothing) => (a', Nothing)
            (a', Just n) => lookupByList a' (nodeToList n)
          GT => let
            a3 = a2 <+> mval r
            in case w a2 a3 of
              LT => (a2, Nothing)
              EQ => lookupByList a2 (digitToList r)
              GT => (a3, Nothing)

  export
  lookupBy : Cache m a => FingerTree m a -> (m, Maybe a)
  lookupBy = lookupByTree neutral

  splitByList : Cache m a => m -> List a -> (List a, Maybe a, List a)
  splitByList _ [] = ([], Nothing, [])
  splitByList a (x::xs) = let
    a' = a <+> mval x
    in case w a a' of
      LT => ([], Nothing, x::xs)
      EQ => ([], Just x, xs)
      GT => let (l,m,r) = splitByList a' xs
        in (x::l,m,r)

  splitByTree : Cache m a => m -> FingerTree m a -> (FingerTree m a, Maybe a, FingerTree m a)
  splitByTree _ Empty = (Empty, Nothing, Empty)
  splitByTree a0 (Single x) = let
    a1 = a0 <+> mval x
    in case w a0 a1 of
      LT => (Empty, Nothing, Single x)
      EQ => (Empty, Just x, Empty)
      GT => (Single x, Nothing, Empty)
  splitByTree a0 (Deep l t r c) = let
    a1 = a0 <+> mval l
    in case w a0 a1 of
      LT => (Empty, Nothing, Deep l t r c)
      EQ => let (l',x,r') = splitByList a0 (digitToList l)
        in (listToTree l', x, assemblel r' t r)
      GT => let
        a2 = a1 <+> mval t
        in case w a1 a2 of
          LT => (digitToTree l, Nothing, assemblel [] t r)
          EQ => case splitByTree a1 t of
            (l',Nothing,r') => (assembler l l' [], Nothing, assemblel [] r' r)
            (l',Just n,r') => let (l'',x,r'') = splitByList (a1 <+> mval l') (nodeToList n) in
              (assembler l l' l'', x, assemblel r'' r' r)
          GT => let
            a3 = a2 <+> mval r
            in case w a2 a3 of
              LT => (assembler l t [], Nothing, digitToTree r)
              EQ => let (l',x,r') = splitByList a2 (digitToList r)
                in (assembler l t l', x, listToTree r')
              GT => (Deep l t r c, Nothing, Empty)

  export
  splitBy : Cache m a => FingerTree m a -> (FingerTree m a, Maybe a, FingerTree m a)
  splitBy = splitByTree neutral


{-
data SearchResult : Type -> Type -> Type where
  OnLeft : SearchResult m a
  OnRight : SearchResult m a
  Position : FingerTree m a -> a -> FingerTree m a -> SearchResult m a
  Misbehaviour : SearchResult m a
-}

-- There follows some strategies for rebuilding nodes. This strategy
-- obtains the new cache from the old.
export
convert : (m -> n) -> (m -> List n -> n)
convert a x _ = a x

-- This strategy recomputes the new cache from its contents.
export
recalculate : (Cache n b) => m -> List n -> n
recalculate _ = concat

reDigit2 : Cache n b => (m -> List n -> n) -> b -> b -> m -> Digit n b
reDigit2 a w x c = Digit2 w x (a c [mval w, mval x])

reDigit3 : Cache n b => (m -> List n -> n) -> b -> b -> b -> m -> Digit n b
reDigit3 a w x y c = Digit3 w x y (a c [mval w, mval x, mval y])

reDigit4 : Cache n b => (m -> List n -> n) -> b -> b -> b -> b -> m -> Digit n b
reDigit4 a w x y z c = Digit4 w x y z (a c [mval w, mval x, mval y, mval z])

reNode2 : Cache n b => (m -> List n -> n) -> b -> b -> m -> Node n b
reNode2 a w x c = Node2 w x (a c [mval w, mval x])

reNode3 : Cache n b => (m -> List n -> n) -> b -> b -> b -> m -> Node n b
reNode3 a w x y c = Node3 w x y (a c [mval w, mval x, mval y])

reDeep : Cache n b => (m -> List n -> n) -> Digit n b -> FingerTree n (Node n b) -> Digit n b -> m -> FingerTree n b
reDeep a l m r c = Deep l m r (a c [mval l, mval m, mval r])

export
tmap : Cache n b => (m -> List n -> n) -> (a -> b) -> FingerTree m a -> FingerTree n b
tmap _ _ Empty = Empty
tmap _ f (Single x) = Single (f x)
tmap p f (Deep l u r c) = reDeep p (tmapd l) (tmap p tmapn u) (tmapd r) c where

  tmapd : Digit m a -> Digit n b
  tmapd (Digit1 w) = Digit1 (f w)
  tmapd (Digit2 w x c) = reDigit2 p (f w) (f x) c
  tmapd (Digit3 w x y c) = reDigit3 p (f w) (f x) (f y) c
  tmapd (Digit4 w x y z c) = reDigit4 p (f w) (f x) (f y) (f z) c

  tmapn : Node m a -> Node n b
  tmapn (Node2 w x c) = reNode2 p (f w) (f x) c
  tmapn (Node3 w x y c) = reNode3 p (f w) (f x) (f y) c

export
ttraverse : (Applicative f, Cache n b) => (m -> List n -> n) -> (a -> f b) -> FingerTree m a -> f (FingerTree n b)
ttraverse _ _ Empty = pure Empty
ttraverse _ g (Single x) = Single <$> g x
ttraverse p g (Deep l u r c) = reDeep p <$> ttraversed l <*> ttraverse p ttraversen u <*> ttraversed r <*> pure c where

  ttraversed : Digit m a -> f (Digit n b)
  ttraversed (Digit1 w) = Digit1 <$> g w
  ttraversed (Digit2 w x c) = reDigit2 p <$> g w <*> g x <*> pure c
  ttraversed (Digit3 w x y c) = reDigit3 p <$> g w <*> g x <*> g y <*> pure c
  ttraversed (Digit4 w x y z c) = reDigit4 p <$> g w <*> g x <*> g y <*> g z <*> pure c

  ttraversen : Node m a -> f (Node n b)
  ttraversen (Node2 w x c) = reNode2 p <$> g w <*> g x <*> pure c
  ttraversen (Node3 w x y c) = reNode3 p <$> g w <*> g x <*> g y <*> pure c


export
foldr' : (func : a -> x -> x) -> (init : x) -> (input : FingerTree m a) -> x
foldr' _ i Empty = i
foldr' f i (Single x) = f x i
foldr' f i (Deep l t r _) = d l (foldr' n (d r i) t) where
  d : Digit m a -> x -> x
  d (Digit1 z) j = f z j
  d (Digit2 y z _) j = f y (f z j)
  d (Digit3 x y z _) j = f x (f y (f z j))
  d (Digit4 w x y z _) j = f w (f x (f y (f z j)))
  n : Node m a -> x -> x
  n (Node2 y z _) j = f y (f z j)
  n (Node3 x y z _) j = f x (f y (f z j))

export
foldl' : (func : x -> a -> x) -> (init : x) -> (input : FingerTree m a) -> x
foldl' _ i Empty = i
foldl' f i (Single x) = f i x
foldl' f i (Deep l t r _) = d (foldl' n (d i l) t) r where
  d : x -> Digit m a -> x
  d j (Digit1 w) = f j w
  d j (Digit2 w x _) = f (f j w) x
  d j (Digit3 w x y _) = f (f (f j w) x) y
  d j (Digit4 w x y z _) = f (f (f (f j w) x) y) z
  n : x -> Node m a -> x
  n j (Node2 w x _) = f (f j w) x
  n j (Node3 w x y _) = f (f (f j w) x) y

-- I expect we can do better; a stream-based implementation would save
-- us needing to build the whole list.
export
treeToList : FingerTree m a -> List a
treeToList = foldr' (::) []


-- Map, taking into account the cache up to that point
export
treeLAccumMap : (Cache m a, Cache n b) => (m -> List n -> n) -> (m -> a -> b) -> m -> FingerTree m a -> FingerTree n b
treeLAccumMap _ _ _ Empty = Empty
treeLAccumMap _ g z (Single x) = Single $ g z x
treeLAccumMap p g z (Deep l u r _) = let
  z1 = z <+> mval l
  z2 = z1 <+> mval u
  in deep (dLAccumMap z l) (treeLAccumMap p nLAccumMap z1 u) (dLAccumMap z2 r) where
    dLAccumMap : m -> Digit m a -> Digit n b
    dLAccumMap y (Digit1 a) = Digit1 $ g y a
    dLAccumMap y (Digit2 a b i) = let
      y1 = y <+> mval a
      in reDigit2 p (g y a) (g y1 b) i
    dLAccumMap y (Digit3 a b c i) = let
      y1 = y <+> mval a
      y2 = y1 <+> mval b
      in reDigit3 p (g y a) (g y1 b) (g y2 c) i
    dLAccumMap y (Digit4 a b c d i) = let
      y1 = y <+> mval a
      y2 = y1 <+> mval b
      y3 = y2 <+> mval c
      in reDigit4 p (g y a) (g y1 b) (g y2 c) (g y3 d) i
    nLAccumMap : m -> Node m a -> Node n b
    nLAccumMap y (Node2 a b i) = let
      y1 = y <+> mval a
      in reNode2 p (g y a) (g y1 b) i
    nLAccumMap y (Node3 a b c i) = let
      y1 = y <+> mval a
      y2 = y1 <+> mval b
      in reNode3 p (g y a) (g y1 b) (g y2 c) i


export
[eqFingerTree] Eq a => Eq (FingerTree m a) where
  t1 == t2 = treeToList t1 == treeToList t2

export
debugView : Show a => FingerTree m a -> String
debugView = dvTree show where

  dvNode : (b -> String) -> Node m b -> String
  dvNode f (Node2 x y _) = "(node2 " <+> f x <+> " " <+> f y <+> ")"
  dvNode f (Node3 x y z _) = "(node3 " <+> f x <+> " " <+> f y <+> " " <+> f z <+> ")"

  dvDigit : (b -> String) -> Digit m b -> String
  dvDigit f (Digit1 w) = "(digit1 " <+> f w <+> ")"
  dvDigit f (Digit2 w x _) = "(digit2 " <+> f w <+> " " <+> f x <+> ")"
  dvDigit f (Digit3 w x y _) = "(digit3 " <+> f w <+> " " <+> f x <+> " " <+> f y <+> ")"
  dvDigit f (Digit4 w x y z _) = "(digit4 " <+> f w <+> " " <+> f x <+> " " <+> f y <+> " " <+> f z <+> ")"

  dvTree : (b -> String) -> FingerTree m b -> String
  dvTree _ Empty = "neutral"
  dvTree f (Single x) = "(single " <+> f x <+> ")"
  dvTree f (Deep l t r _) = "(deep " <+> dvDigit f l <+> " " <+> dvTree (dvNode f) t <+> " " <+> dvDigit f r <+> ")"


{-
namespace Tests

  export
  shouldBe : (Eq a, Show a) => a -> a -> IO ()
  shouldBe x y = if x == y then pure () else do
    putStrLn "fail:"
    putStrLn ("  expected: " <+> show y)
    putStrLn ("  actual:   " <+> show x)
    putStrLn ""
    pure ()

  export
  testDigits : IO ()
  testDigits = foldlM (const t) () [| MkPair l l |] where

    l : List (Digit () (Uncached Int))
    l = [Digit1 (MkUncached 1),
         digit2 (MkUncached 1) (MkUncached 2),
         digit3 (MkUncached 1) (MkUncached 2) (MkUncached 3),
         digit4 (MkUncached 1) (MkUncached 2) (MkUncached 3) (MkUncached 4)]

    t : (Digit (Uncached Int) (), Digit (Uncached Int) ()) -> IO ()
    t (a,b) = concatMap nodeToList (twoDigitsToNodes a b) `shouldBe` (digitToList a <+> digitToList b)
-}
