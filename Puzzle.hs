module Puzzle where


data List a
  = Unit a
  | List a :++: List a
  | Rep Nat (List a)
 deriving ( Eq, Ord, Show )

type Nat = Integer


zipp :: List a -> List b -> List (a,b)
zipp = undefined
  -- minimize the *size* of the result
  -- you can assume the *length*s of the arguments are the same


-- length
len :: List a -> Integer
len (Unit _)   = 1
len (p :++: q) = len p + len q
len (Rep n p)  = n * len p


-- size
size :: List a -> Int
size (Unit _)   = 1
size (p :++: q) = size p + size q
size (Rep _ p)  = size p



