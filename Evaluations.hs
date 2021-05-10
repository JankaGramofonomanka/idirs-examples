module Main where



type Unary a    = a -> a
type Binary a   = a -> a -> a
type Ternary a  = a -> a -> a -> a



(==>) :: Bool -> Bool -> Bool
(==>) a b = not a || b


-- Axioms ---------------------------------------------------------------------
a1 :: Binary Bool
a1 phi psi = phi ==> (psi ==> phi)

a2 :: Ternary Bool
a2 phi psi theta = 
  (phi ==> (psi ==> theta)) ==> ((phi ==> psi) ==> (phi ==> theta))

a3 :: Unary Bool
a3 phi = (not (not phi)) ==> phi


-- All evaluations ------------------------------------------------------------
allValues :: [Bool]
allValues = [True, False]

allEvaluations1 :: Unary Bool -> [Bool]
allEvaluations1 op = do
  val <- allValues

  return $ op val

allEvaluations2 :: Binary Bool -> [Bool]
allEvaluations2 op = do
  val1 <- allValues
  val2 <- allValues

  return $ op val1 val2

allEvaluations3 :: Ternary Bool -> [Bool]
allEvaluations3 op = do
  val1 <- allValues
  val2 <- allValues
  val3 <- allValues

  return $ op val1 val2 val3



-- Main program ---------------------------------------------------------------
main :: IO ()
main = do
  putStrLn "All evaluations of (A1):"
  putStrLn $ show $ allEvaluations2 a1

  putStrLn ""
  putStrLn "All evaluations of (A2):"
  putStrLn $ show $ allEvaluations3 a2

  putStrLn ""
  putStrLn "All evaluations of (A3):"
  putStrLn $ show $ allEvaluations1 a3
