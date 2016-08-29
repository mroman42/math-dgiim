type Padic = [Int]

p = 3

normalize :: [Int] -> Padic
normalize = normalize' 0
  where
    normalize' 0     []     = []
    normalize' carry []     = normalize' 0 [carry]
    normalize' carry (x:xs) = (mod (x+carry) p) : (normalize' (quot (x+carry) p) xs)

toPadic :: Int -> Padic
toPadic n = normalize [n]

toInt :: Padic -> Int
toInt []     = 0
toInt (x:xs) = x + p * (toInt xs)

plus :: Padic -> Padic -> Padic
plus xs     []     = normalize $ xs
plus []     ys     = normalize $ ys
plus (x:xs) (y:ys) = normalize $ (x+y) : (plus xs ys)

sum :: [Padic] -> Padic
sum = foldr plus [0]

prod :: Padic -> Padic -> Padic
prod []     ys = [0]
prod (x:xs) ys = plus (map (*x) ys) (prod xs (0:ys))
