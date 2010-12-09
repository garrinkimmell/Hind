module Language.KansasLava.Verification.KInduction
  (checkCircuit, checkCircuitPar, parCheck, seqCheck) where


import Language.KansasLava
import Language.KansasLava.Verification.SMTLIB
import Language.KansasLava.Verification.Interaction
import Language.SMTLIB
import Control.Exception
import Control.Monad
import Control.Concurrent

-- For testing
import Data.Sized.Unsigned


parCheck proverCmd model property = do
    resultChan <- newChan
    baseProc <- baseProcess proverCmd model property resultChan
    stepProc <- stepProcess proverCmd model property resultChan
    let loop basePass = do
          res <- readChan resultChan
          putStrLn $ show res
          case res of
            BasePass k -> loop k
            BaseFail k -> do
                          return False
            StepPass k -> do
                          return True
            StepFail k -> loop basePass

    result <- loop 0
    if result
       then putStrLn "Passed" >> return Nothing
       else putStrLn "Failed" >> return Nothing

    return ()



data ProverResult = BasePass Integer | BaseFail Integer | StepPass Integer | StepFail Integer deriving Show


baseProcess proverCmd model property resultChan = forkIO $
  bracket (makeProver proverCmd) closeProver $ \p -> do
    putStrLn "Base Prover Started"
    _ <- mapM (sendCommand p) model
    let loop k = do
          push 1 p
          let baseCmds = base property k
          _ <- mapM_ (sendCommand p) baseCmds
          res <- isUnsat p
          if res
               then do
                 writeChan resultChan (BasePass k)
                 pop 1 p
                 loop (k+1)
               else do
                 writeChan resultChan (BaseFail k)
    loop 1

stepProcess proverCmd model property resultChan = forkIO $
  bracket (makeProver proverCmd) closeProver $ \p -> do
    putStrLn "Step Prover Started"
    _ <- mapM (sendCommand p) model
    let loop k = do
          push 1 p
          let stepCmds = step property k
          _ <- mapM_ (sendCommand p) stepCmds
          res <- isUnsat p
          if res
               then do
                 writeChan resultChan (StepPass k)
               else do
                 writeChan resultChan (StepFail k)
                 pop 1 p
                 loop (k+1)

    loop 1


-- checkCircuitPar :: (Ports a) => String -> a -> String -> IO (Maybe Numeral)
checkCircuitPar  proverCmd circuit property =do
  rc <- reifyCircuit circuit
  let Script model = smtCircuit rc
  parCheck proverCmd model property


checkCircuit :: (Ports a) => String -> a -> String -> IO (Maybe Numeral)
checkCircuit proverCmd circuit property = do
  rc <- reifyCircuit circuit
  let Script model = smtCircuit rc
  seqCheck proverCmd model property


seqCheck proverCmd model property = do
  bracket (makeProver proverCmd) closeProver $ \p -> do
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
          push 1 p
          _ <- mapM (sendCommand p) baseCmds
          baseSuccess <- isUnsat p
          pop 1 p

          when debug $ do
            putStrLn "Base case"
            print baseCmds


          when debug $ putStrLn $ "Base case UNSAT result is " ++ show baseSuccess

          if baseSuccess
             then do
               -- Check the step case

               let stepCmds = step property k
               push 1 p
               results <- mapM (sendCommand p) stepCmds
               stepSuccess <- isUnsat p
               pop 1 p

               when debug $ do
                    putStrLn "Step case"
                    print stepCmds
                    print results


               when debug $
                    putStrLn $ "Step case UNSAT result is " ++ show stepSuccess

               if stepSuccess
                 then do
                   return (Just k)
                 else loop (k+1)
             else do -- Base failed
               m <- getModel p
               putStrLn $ show m
               return Nothing -- loop (k+1)

  result <- loop 1
  when debug $
       case result of
         Just k -> putStrLn $ "Proved at step " ++ show k
         Nothing -> putStrLn $ "Failed to prove"
  return result

  where maxStep = 10
        debug = True



-- | Assertions for the base case
base :: String -> Numeral -> [Command]
base propName k =
  [Assert $ trans i | i <- [0..k]] ++
  case ps of
    [p] -> [Assert p]
    _ -> [Assert $
          Term_qual_identifier_ (Qual_identifier (Identifier "or"))
          ps]

  where prop i =
          Term_qual_identifier_ (Qual_identifier (Identifier "not"))
            [Term_qual_identifier_ (Qual_identifier (Identifier propName))
                    [Term_spec_constant (Spec_constant_numeral i)]]
        ps =  [(prop idx) | idx <- [0..k-1]]

        trans i = Term_qual_identifier_ (Qual_identifier (Identifier "trans"))
                     [Term_spec_constant (Spec_constant_numeral i)]


-- | Assertions for the step case
step :: String -> Numeral -> [Command]
step propName k =
  [Assert (prop idx) | idx <- [1..k]] ++
  [Assert (trans idx) | idx <- [0..k]] ++
  [Assert kstep]
    where prop i = Term_qual_identifier_ (Qual_identifier (Identifier propName))
                   [prev i]
          trans i = Term_qual_identifier_ (Qual_identifier (Identifier "trans"))
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

c1' a b = (c, output "aprop" (and2 c (bitNot c)))
  where c = c1 a b
c1 :: Seq Bool -> Seq Bool -> Seq Bool
c1 = and2


accum :: Seq U8 -> (Seq U8, Seq Bool)
accum i = (sum, output "aprop" (sum .<. 7))
  where r = register 0 sum
        sum = r + mux2 (i .<. 3) (i,0)

c2 :: Seq U8 -> (Seq U8, Seq Bool)
-- c2 :: Comb U8 -> Comb U8
c2 i = (o, output "aprop" (i .<. 7))
  where o = mux2 low (i,i)


toggle :: Seq Bool -> Seq Bool
toggle change = out
  where out' = register low out
        out = xor2 change out'

delayN 0 init inp = inp
delayN n init inp = out
  where out = register init rest
        rest = delayN (n-1) init inp

puls n = out
  where out = delayN (n-1) low last
        last = register high out

prop_toggle_vs_puls :: Int -> (Seq Bool, Seq Bool, Seq Bool)
prop_toggle_vs_puls n = (out1, out2, output "aprop" ok)
  where
    out1 = toggle high
    out2 = puls n
    ok = (bitNot (out1 .==. out2))
    -- ok = bitNot high

-- Installation for testing
z3 :: [Char]
z3 = "ssh teme z3/bin/z3 -si -smt2 MODEL=true"

cvc3 = "cvc3 -lang smt2"



