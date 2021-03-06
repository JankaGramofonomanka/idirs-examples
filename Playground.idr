module Main

import Data.Vect

%name Vect xs, ys, zs, ws

-------------------------------------------------------------------------------
vectHead : Vect (S k) a -> a
vectHead (x :: xs) = x

headApp : Int
headApp = vectHead [1,2,3]




-------------------------------------------------------------------------------
getVector : IO (n ** Vect n String)
getVector = do
  putStrLn "enter element (q to quit)"
  x <- getLine
  if x == "q" then pure (0 ** []) else do
    (k ** xs) <- getVector
    pure $ (S k ** x :: xs)


main : IO ()
main = do
  (n ** xs) <- getVector
  case n of
    Z   => putStrLn "empty vector"
    S k => putStrLn $ show $ head xs




-------------------------------------------------------------------------------
nonsense : Bool -> Type
nonsense True = List Int
nonsense False = String

nonsenseFunc : (b : Bool) -> nonsense b
nonsenseFunc True = [1,2,3]
nonsenseFunc False = "nonsense"

nonsenseApp : String
nonsenseApp = nonsenseFunc False





-------------------------------------------------------------------------------
paste : List String -> String -> String
paste wrds sep = foldl ?help "" wrds


-------------------------------------------------------------------------------
zipVectWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipVectWith f [] [] = []
zipVectWith f (x :: xs) (y :: ys) = f x y :: zipVectWith f xs ys


zipListWith : (a -> b -> c) -> List a -> List b -> List c
zipListWith f [] ys = []
zipListWith f (x :: xs) ys = zipListWith f (x :: (x :: xs)) ys






-------------------------------------------------------------------------------
--  data Nat = Z | S Nat

--  (+) : Nat -> Nat -> Nat
--  Z     + m = m
--  (S k) + m = S (k + m)

concatOK : Vect n a -> Vect m a -> Vect (n + m) a
concatOK [] ys = ys
concatOK (x :: xs) ys = x :: concatOK xs ys

{-
concatERROR : Vect n a -> Vect m a -> Vect (m + n) a
concatERROR (x :: xs) ys = x :: concatERROR xs ys
concatERROR [] ys = ys
-- -}




-------------------------------------------------------------------------------
--  data Equal : a -> b -> Type where
--    Refl : Equal x x

fact1 : 2 + 2 = 4
fact1 = Refl


fact2 : Int = Int
fact2 = Refl

--lie : 2 + 2 = 5
--lie = Refl


symmetry : x = y -> y = x
symmetry Refl = Refl



-------------------------------------------------------------------------------
plusReduces : (n : Nat) -> plus Z n = n
plusReduces n = Refl


plusReducesZ : (n : Nat) -> plus n Z = n
plusReducesZ Z = Refl
plusReducesZ (S k) = cong S (plusReducesZ k)


plusReducesS : (n : Nat) -> (m : Nat) -> plus n (S m) = S (plus n m)
plusReducesS Z m = Refl
plusReducesS (S k) m = cong S $ plusReducesS k m


concatOK2 : Vect n a -> Vect m a -> Vect (m + n) a
concatOK2 {n = Z}   []        w = rewrite plusReducesZ m in w
concatOK2 {n = S l} (x :: xs) w = rewrite plusReducesS m l in 
  (x :: (concatOK2 xs w))


