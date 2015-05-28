{-# LANGUAGE ScopedTypeVariables #-}
module Main where

----------------------------------------------------------------------------

import Test.QuickCheck
import Test.QuickCheck.Poly
import Data.Char( ord, chr )

----------------------------------------------------------------------------
-- MY CURRENT IMPLEMENTATION >>>

zipp :: List a -> List b -> List (a,b)
zipp (Unit x) q = Unit (x, hd q)
zipp p (Unit y) = Unit (hd p, y)

zipp p q | len p == 0 || len q ==  0 = Empty

zipp pp@(Rep _ _) qq@(Rep _ _)
  | i == 1    = zipp p qq
  | j == 1    = zipp pp q
  | otherwise = rep ij (repl' b a p `zipp` repl' a b q)
 where
  Rep i p = asRep pp
  Rep j q = asRep qq
 
  repl' a b p | a < b     = Rep b p
              | otherwise = repl b p
 
  n  = len p
  m  = len q
  l  = n `lcm` m
  a  = l `div` n
  b  = l `div` m
  ij = i `div` a -- = j `div` b

zipp (App p1 p2) q =
  (p1 `zipp` q1) `app` (p2 `zipp` q2)
 where
  (q1,q2) = split (len p1) q

zipp p (App q1 q2) =
  (p1 `zipp` q1) `app` (p2 `zipp` q2)
 where
  (p1,p2) = split (len q1) p

asRep :: List a -> List a
asRep (Rep i (Rep j p)) = asRep (Rep (i*j) p)
asRep (Rep i p)         = Rep i p
asRep p                 = Rep 1 p
 
split :: Integer -> List a -> (List a, List a)
split k (App p q)
  | k < n     = let (p1,p2) = split k p     in (p1, p2 `app` q)
  | otherwise = let (q1,q2) = split (k-n) q in (p `app` q1, q2)
 where
  n = len p

split k (Unit x)
  | k <= 0 = (Empty, Unit x)
  | k >= 1 = (Unit x, Empty)

split k pp@(Rep _ _)
  | r == 0         = split k Empty
  | r == 1         = split k p
  | k `mod` n == 0 = (rep i p, rep (r-i) p)
  | otherwise      = ( rep i p `app` p1
                     -- , p2 `app` rep (r-i-1) p
                     , rep (r-i-1) (p2 `app` p1) `app` p2
                     )
 where
  Rep r p = asRep pp
  n       = len p
  i       = k `div` n
  (p1,p2) = split (k `mod` n) p

split _ Empty =
  (Empty, Empty)

rep 0 p = Empty
rep 1 p = p
rep r p = Rep r p

repl 0 p = Empty
repl 1 p = p
repl r p = p `app` rep (r-1) p

Empty `app` q = q
p `app` Empty = p
p `app` q     = p `App` q

hd :: List a -> a
hd (Unit x)              = x
hd (Unit x `App` _)      = x
hd ((p `App` q) `App` r) = hd (p `App` (q `App` r))
hd (Rep 0 p `App` r)     = hd r
hd (Rep _ p `App` r)     = hd (p `App` r)
hd (Rep r p) | r > 0     = hd p

-- <<<
----------------------------------------------------------------------------

prop_Correct (Two p q :: Two A B) =
  flat (zipp p q) === flat p `zip` flat q

prop_Best (Two p0 q0 :: Two A B) =
  whenFail (do putStrLn ("   p = " ++ showLst p)
               putStrLn ("   q = " ++ showLst q)
               putStrLn ("zipp = " ++ showLst (zipp p q))
               putStrLn ("best = " ++ showLst (bzip p q))) $
    size (zipp p q) === size (bzip p q)
 where
  p = uniq 0 p0
  q = uniq 0 q0

bzip :: (Ord a, Ord b) => List a -> List b -> List (a,b)
bzip p q = compress (flat p `zip` flat q)

newtype Sym = Sym Char
  deriving ( Eq, Ord )
  
instance Show Sym where
  show (Sym c) = [c]

uniq :: Int -> List a -> List Sym
uniq i Empty     = Empty
uniq i (Unit _)  = Unit (Sym (chr (ord 'a' + i)))
uniq i (App p q) = App (uniq i p) (uniq (i+size p) q)
uniq i (Rep k p) = Rep k (uniq i p)

----------------------------------------------------------------------------

type Nat = Integer

data List a
  = Empty
  | Unit a
  | App (List a) (List a)
  | Rep Nat (List a)
 deriving ( Eq, Ord, Show )

showLst :: Show a => List a -> String
showLst Empty     = "o"
showLst (Unit x)  = show x
showLst (App p q) = showLst p ++ "+" ++ showLst q
showLst (Rep k p) = showLst1 p ++ "^" ++ show k

showLst1 p@(App _ _) = "(" ++ showLst p ++ ")"
showLst1 p           = showLst p

instance Functor List where
  fmap f Empty     = Empty
  fmap f (Unit x)  = Unit (f x)
  fmap f (App p q) = App (fmap f p) (fmap f q)
  fmap f (Rep k p) = Rep k (fmap f p)

arbList :: Arbitrary a => Integer -> Gen (List a)
arbList l =
  frequency
  [ (l1, do x <- arbitrary
            return (Unit x))
  , (l2, do k <- choose (1,l-1)
            p <- arbList k
            q <- arbList (l-k)
            return (App p q))
  , (l2, do k <- elements (factors l)
            p <- arbList (l `div` k)
            return (Rep k p))
  ]
 where
  l1 = if l == 1 then 1 else 0
  l2 = if l > 1  then 1 else 0

  factors n = [ k | k <- [1..n], n `mod` k == 0 ]

instance Arbitrary a => Arbitrary (List a) where
  arbitrary = sized (arbList . (max 1) . fromIntegral)

  shrink (App p q) =
    [ p, q ] ++
    [ App p' q | p' <- shrink p ] ++
    [ App p q' | q' <- shrink q ] ++
    [ App p1 (App p2 q) | App p1 p2 <- [p] ]

  shrink (Rep k p) =
    [ p ] ++
    [ Rep k' p | k' <- shrink k, k' >= 0 ] ++
    [ Rep k p' | p' <- shrink p ] ++
    [ Rep (k*b) q | Rep b q <- [p] ]

  shrink _ = []

len :: List a -> Integer
len Empty     = 0
len (Unit _)  = 1
len (App p q) = len p + len q
len (Rep k p) = k * len p

size :: List a -> Int
size Empty     = 0
size (Unit _)  = 1
size (App p q) = size p + size q
size (Rep _ p) = size p

flat :: List a -> [a]
flat Empty     = []
flat (Unit x)  = [x]
flat (App p q) = flat p ++ flat q
flat (Rep k p) = concat (replicate (fromInteger k) (flat p))

list :: [a] -> List a
list []     = Empty
list [x]    = Unit x
list (x:xs) = Unit x `App` list xs

data Two a b = Two (List a) (List b)
 deriving ( Eq, Ord, Show )

instance (Eq a, Eq b, Arbitrary a, Arbitrary b) => Arbitrary (Two a b) where
  arbitrary = sized $ \s ->
    let s' = max 1 (fromIntegral s) in
    do p <- arbList s'
       q <- arbList s'
       return (Two p q)
  
  shrink (Two p q) =
    concat
    [ [Two p1 q1, Two p2 q2]
    | i <- [1..len p-1]
    , let (p1,p2) = split i p
    , let (q1,q2) = split i q
    ] ++
    [ Two p' q'
    | p1 <- p : shrink p
    , p' <- p1 : shrink p1
    , q1 <- q : shrink q
    , q' <- q1 : shrink q1
    , p' /= p || q' /= q
    , len p' == len q'
    ]

----------------------------------------------------------------------------

compress :: Ord a => [a] -> List a
compress [] = Empty
compress xs = snd (best 0 n)
 where
  n = length xs

  best i j = (table !! i) !! j
  
  table = [ [ best' i j | j <- [0..n] ]
          | i <- [0..n]
          ]
  
  best' i j
    | i+1 == j = (1, Unit (xs !! i))
    | i+1 <  j = minimum [ app a b p q
                         | k <- [i+1..j-1]
                         , let (a,p) = best i k
                               (b,q) = best k j
                         ]

  app a b p q
    | p' == q'  = (a, Rep (n+m) p')
    | otherwise = (a+b, App p q)
   where
    (n,p') = asRep p
    (m,q') = asRep q
  
    asRep (Rep k r) = (k,r)
    asRep p         = (1,p)

----------------------------------------------------------------------------


