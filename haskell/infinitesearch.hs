{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- http://math.andrej.com/2007/09/28/seemingly-impossible-functional-programs/


------------------------------------------------------------------
-- Part 1: Cantor space
------------------------------------------------------------------
-- Booleans and naturals
data Bit = I | O deriving (Eq, Show)
type Nat = Integer

coerce :: Bit -> Nat
coerce I = 1
coerce O = 0

-- Lists of bits
type Cantor = Nat -> Bit

instance Show Cantor where
  show s = show $ map s [1..]

proj :: Nat -> (Cantor -> Nat)
proj n s = coerce (s n)

-- Appending to a list of bits
(#) :: Bit -> Cantor -> Cantor
x # a = \i -> if i == 0 then x else a(i-1)

-- Infinite search on a list of bits
forsome :: (Cantor -> Bool) -> Bool
forsome p = p (find p)

find :: (Cantor -> Bool) -> Cantor
find p = if forsome (\a -> p (O # a))
         then O # find (\a -> p (O # a))
         else I # find (\a -> p (I # a))

-- Corolaries
forevery :: (Cantor -> Bool) -> Bool
forevery p = not (forsome (not . p))

search :: (Cantor -> Bool) -> Maybe Cantor
search p = if forsome p
           then Just (find p)
           else Nothing

-- Decidable equality
equal :: Eq y => (Cantor -> y) -> (Cantor -> y) -> Bool
equal f g = forevery (\a -> f a == g a)


-- Auxiliary functions
-----------------------------------------------------------------------
proptest :: Cantor -> Bool
proptest s = odd (coerce (s 2) + coerce (s 3) + coerce (s 5))

-- Execution example
{- where p = proptest

 find p
 forsome (\a -> p (O # a)) ?
 (\a -> p (O # a)) (find (\a -> p (O # a)))
 forsome (\a -> p (O # O # a))) ?
 forsome (\a -> p (O # O # O # a))) ?
 forsome (\a -> p (O # O # O # O # a))) ?
 forsome (\a -> p (O # O # O # O # O # a)) ?
 (\a -> False) (find \a -> p (O # O # O # O # O # a)) | FALSE!
 O # O # O # O # I # O # O...
-}







------------------------------------------------------------------
-- Part 2: Brower fan functional
------------------------------------------------------------------
-- Mu operator, unbouded recursion, least natural satisfying a
-- condition.
least :: (Nat -> Bool) -> Nat
least p = if p 0 then 0 else 1 + least (\n -> p (n+1))

-- Logical implication
(-->) :: Bool -> Bool -> Bool
p --> q = not p || q

-- Equality on the n-first terms
eq :: Nat -> Cantor -> Cantor -> Bool
eq 0 a b = True
eq n a b = (a n == b n) && eq (n-1) a b

-- Fan functional
modulus :: (Cantor -> Nat) -> Nat
modulus f = least (\n -> forevery (\a -> forevery (\b -> eq n a b --> (f a == f b))))

main :: IO ()
main = putStrLn "hello!"
