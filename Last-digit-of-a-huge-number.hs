-- https://www.codewars.com/kata/5518a860a73e708c0a000027

module LastDigit (lastDigit) where

isZero :: [Integer] -> Bool
isZero [] = False
isZero (0:xs) = not $ isZero xs
isZero (_:xs) = False

-- mod 4 last digit
f :: [Integer] -> Integer
f [] = 1
f (x:[]) = mod x 4
f (x:y:xs) = if isZero(y:xs) then 1 else
                case (mod x 4) of
                 0 -> 0
                 1 -> 1
                 2 -> if y==1 || isZero(xs) then 2 else 0
                 _ -> if (mod y 2)==1 || isZero(xs) then 3 else 1


lastDigit :: [Integer] -> Integer
lastDigit [] = 1
lastDigit (x:xs) = if isZero(xs) then 1
                    else let r = f xs
                             a = mod x 10 in
                         (a ^ ((r-1) `mod` 4 + 1)) `mod` 10

-- **Note:** This one will result in TLE
-- module LastDigit (lastDigit) where

-- lastDigit :: [Integer] -> Integer
-- lastDigit xs = (foldr (\x n -> 
--                             x ^ (if n<4 then n else (n `mod` 4 + 4 ) ))
--                       1 xs) `mod` 10