{-# LANGUAGE TypeSynonymInstances #-}

data Padic = Padic [Integer]

p :: (Num a) => a
p = 3

normalize :: (Integral a) => [a] -> [a]
normalize = normalize' 0
  where
    normalize' 0     []     = []
    normalize' carry []     = normalize' 0 [carry]
    normalize' carry (x:xs) = (mod (x+carry) p) : (normalize' (div (x+carry) p) xs)

toPadic :: (Integral a) => a -> [a]
toPadic n = normalize [n]

opposite :: (Integral a) => [a] -> [a]
opposite xs = normalize $ map (negate) xs 

ptoInt :: (Num a) => [a] -> a
ptoInt []     = 0
ptoInt (x:xs) = x + p * (ptoInt xs)

plus :: (Integral a) => [a] -> [a] -> [a]
plus xs     []     = normalize $ xs
plus []     ys     = normalize $ ys
plus (x:xs) (y:ys) = normalize $ (x+y) : (plus xs ys)

sum :: (Integral a) => [[a]] -> [a]
sum = foldr plus [0]

prod :: (Integral a) => [a] -> [a] -> [a] 
prod []     ys = [0]
prod (x:xs) ys = plus (map (*x) ys) (prod xs (0:ys))


instance Num Padic where
  (Padic a) + (Padic b) = Padic (plus a b)
  negate (Padic a) = Padic (opposite a)
  (-) a b = (+) a (negate b)
  (Padic a) * (Padic b) = Padic (prod a b)
  abs = id
  signum = (\_ -> 1)
  fromInteger x = Padic (toPadic x)

instance Enum Padic where
  toEnum n = Padic (toPadic (toInteger n))
  fromEnum (Padic xs) = ptoInt (map fromInteger xs) 
