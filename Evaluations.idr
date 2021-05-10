module Main



operator : Type -> Nat -> Type
operator a Z = a
operator a (S k) = a -> operator a k


infixr 10 ==>
(==>) : operator Bool 2
(==>) a b = not a || b


-- Axioms ---------------------------------------------------------------------
a1 : operator Bool 2
a1 phi psi = phi ==> (psi ==> phi)

a2 : operator Bool 3
a2 phi psi theta = 
  (phi ==> (psi ==> theta)) ==> ((phi ==> psi) ==> (phi ==> theta))

a3 : operator Bool 1
a3 phi = (not (not phi)) ==> phi


-- All evaluations ------------------------------------------------------------
allValues : List Bool
allValues = [True, False]

allEvaluations : (arity ** operator Bool arity) -> List Bool
allEvaluations (Z ** op) = pure op
allEvaluations (S k ** op) = do
  val <- allValues
  
  allEvaluations $ (k ** op val)



-- Main program ---------------------------------------------------------------
main : IO ()
main = do
  putStrLn "All evaluations of (A1):"
  putStrLn $ show $ allEvaluations (2 ** a1)

  putStrLn ""
  putStrLn "All evaluations of (A2):"
  putStrLn $ show $ allEvaluations (3 ** a2)

  putStrLn ""
  putStrLn "All evaluations of (A3):"
  putStrLn $ show $ allEvaluations (1 ** a3)
