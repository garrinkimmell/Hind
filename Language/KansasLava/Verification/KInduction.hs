module Language.KansasLava.Verification.KInduction
  (checkCircuit) where


import Language.KansasLava
import Language.KansasLava.Verification.SMTLIB
import Language.KansasLava.Verification.Interaction

import Language.SMTLIB
import Control.Exception
import Control.Monad


checkCircuit :: (Ports a) => String -> a -> String -> IO (Maybe Numeral)
checkCircuit proverCmd circuit property =
  bracket (makeProver proverCmd) closeProver $ \p -> do

  -- Create the model for the circuit
  rc <- reifyCircuit circuit
  let Script model = smtCircuit rc
  when debug $ do
    putStrLn "Model"
    print $ Script model

  -- Set up the model
  _ <- mapM (sendCommand p) model

  let loop k
        | k >= maxStep = return Nothing
        | otherwise = do
          when debug $ putStrLn $ "k = " ++ show k

          -- Turn on path compression.
          -- FIXME: This is incorrect. It needs to be moved, and
          -- path compression should be an option.
          when False $ do
               mapM_ (sendCommand p) (pathCompression [] k)



          -- Check the base case
          let baseCmds = base property k
          _ <- mapM (sendCommand p) baseCmds

          when debug $ do
            putStrLn "Base case"
            print baseCmds

          baseSuccess <- isUnsat p
          when debug $ putStrLn $ "Base case UNSAT result is " ++ show baseSuccess

          if baseSuccess
             then do
               -- Check the step case

               let stepCmds = step property k
               results <- mapM (sendCommand p) stepCmds

               when debug $ do
                    putStrLn "Step case"
                    print stepCmds
                    print results

               stepSuccess <- isUnsat p
               when debug $
                    putStrLn $ "Step case UNSAT result is " ++ show stepSuccess

               if stepSuccess
                 then do
                   return (Just k)
                 else loop (k+1)
             else do -- Base failed
               _ <- getModel p []
               loop (k+1)

  result <- loop 1
  when debug $
       case result of
         Just k -> putStrLn $ "Proved at step " ++ show k
         Nothing -> putStrLn $ "Failed to prove"
  return result

  where maxStep = 5
        debug = True



-- | Assertions for the base case
base :: String -> Numeral -> [Command]
base propName k = case ps of
                    [p] -> [Assert p]
                    _ -> [Assert $
                          Term_qual_identifier_ (Qual_identifier (Identifier "or"))
                          ps]

  where prop i =
          Term_qual_identifier_ (Qual_identifier (Identifier "not"))
            [Term_qual_identifier_ (Qual_identifier (Identifier propName))
                    [Term_spec_constant (Spec_constant_numeral i)]]
        ps =  [(prop idx) | idx <- [0..k-1]]


-- | Assertions for the step case
step :: String -> Numeral -> [Command]
step propName k =
  [Assert (prop idx) | idx <- [1..k]] ++ [Assert kstep]
    where prop i = Term_qual_identifier_ (Qual_identifier (Identifier propName))
                   [prev i]
          prev j = Term_qual_identifier_ (Qual_identifier (Identifier "-"))
                    [Term_qual_identifier (Qual_identifier (Identifier nvar)),
                     Term_spec_constant (Spec_constant_numeral j)]
          nvar = "n"
          kstep = Term_qual_identifier_ (Qual_identifier (Identifier "not"))
                    [Term_qual_identifier_ (Qual_identifier (Identifier propName))
                     [Term_qual_identifier (Qual_identifier (Identifier nvar))]]



-- | Given a list of state variables and an induction depth k, pathCompression
-- generates the assertions that the states are distinct
pathCompression :: [Symbol] -> Numeral -> [Command]
pathCompression svars k = distinctState svars (pathIndices [0..k-1])


-- | pathIndices generates the list of time indices within a path
pathIndices :: [Numeral] -> [(Numeral, Numeral)]
pathIndices [] = []
pathIndices (i:is) = [(i,j) | j <- is] ++ pathIndices is

distinct :: Symbol -> Numeral -> Numeral -> Term
distinct svar i j =
  Term_qual_identifier_ (Qual_identifier (Identifier "not"))
    [Term_qual_identifier_ (Qual_identifier (Identifier "=")) [a,b]]
   where a = Term_qual_identifier_ (Qual_identifier (Identifier svar))
                    [Term_spec_constant (Spec_constant_numeral i)]
         b = Term_qual_identifier_ (Qual_identifier (Identifier svar))
                    [Term_spec_constant (Spec_constant_numeral j)]


distincts :: [Symbol] -> Numeral -> Numeral -> Command
distincts svars i j = Assert $
  Term_qual_identifier_ (Qual_identifier (Identifier "or"))
    [distinct s i j | s <- svars]

distinctState :: [Symbol] -> [(Numeral, Numeral)] -> [Command]
distinctState svars indices =
  [distincts svars i j | (i,j) <- indices]




-- Test Cases
{-
c1' a b = (c, output "aprop" (and2 c (bitNot c)))
  where c = c1 a b
c1 :: Seq Bool -> Seq Bool -> Seq Bool
c1 = and2

-- Installation for testing
z3 :: [Char]
z3 = "ssh teme z3/bin/z3 -si -smt2"

-}