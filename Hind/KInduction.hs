module Hind.KInduction
  (parCheck, seqCheck) where


import Hind.Interaction
import Language.SMTLIB
import Control.Exception
import Control.Monad
import Control.Concurrent
import Data.List(sortBy, groupBy)

parCheck :: String -> [Command] -> Symbol -> [String] -> IO ()
parCheck proverCmd model property stateVars = do
    resultChan <- newChan

    -- Inferred invariants will show up on the invChan
    invChan <- newChan
    invGenProc <- invGenProcess proverCmd model property stateVars invChan
    let invChanBase = invChan
    invChanBase <- dupChan invChan
    invChanStep <- dupChan invChan

    -- baseProc <- forkIO $ return ()
    -- stepProc <- forkIO $ return ()
    baseProc <- baseProcess proverCmd model property resultChan invChanBase
    stepProc <- stepProcess proverCmd model property resultChan invChanStep
    let loop basePass = do
          res <- readChan resultChan
          -- putStrLn $ show res
          case res of
            BasePass k -> loop k
            BaseFail k -> return False
            StepPass k -> return True
            StepFail k -> loop basePass

    result <- loop 1
    if result
       then putStrLn "Passed" >> return Nothing
       else putStrLn "Failed" >> return Nothing

    -- Clean up all the threads
    mapM_ killThread [invGenProc,baseProc,stepProc]
    return ()



data ProverResult = BasePass Integer | BaseFail Integer | StepPass Integer | StepFail Integer deriving Show

baseProcess proverCmd model property resultChan invChan = forkIO $
  bracket (makeProver proverCmd) closeProver $ \p -> do
    putStrLn "Base Prover Started"
    _ <- mapM (sendCommand p) model
    putStrLn "System Defined"
    let loop k = do
          -- checkInvariant p invChan

          -- send (trans (k - 1)
          sendCommand p (Assert (trans (k - 1)))
          -- send (not (p (k))
          sendCommand p (Assert (prop (k - 1)))
          res <- isUnsat p
          if res
             then do
               writeChan resultChan (BasePass k)
               loop (k+1)
             else do
               writeChan resultChan (BaseFail k)
    loop 1
  where trans i = Term_qual_identifier_ (Qual_identifier (Identifier "trans"))
                    [Term_spec_constant (Spec_constant_numeral i)]

        prop i =
          Term_qual_identifier_ (Qual_identifier (Identifier "not"))
            [Term_qual_identifier_ (Qual_identifier (Identifier property))
                    [Term_spec_constant (Spec_constant_numeral i)]]


stepProcess proverCmd model property resultChan invChan = forkIO $
  bracket (makeProver proverCmd) closeProver $ \p -> do
    putStrLn "Step Prover Started"
    _ <- mapM (sendCommand p) model
    putStrLn "System Defined"

    -- Send '(not (prop n))'
    sendCommand p (Assert kstep)

    let loop k = do
          -- Send '(trans (n-k+1)'
          sendCommand p (Assert (trans (k - 1)))
          -- Send '(prop (n-k))'
          sendCommand p (Assert (prop k))
          res <- isUnsat p
          if res
               then do
                 writeChan resultChan (StepPass k)
               else do
                 writeChan resultChan (StepFail k)
                 loop (k+1)

    loop 1

    where prop i = Term_qual_identifier_ (Qual_identifier (Identifier property))
                   [prev i]
          trans i = Term_qual_identifier_ (Qual_identifier (Identifier "trans"))
                     [prev i]
          prev j = Term_qual_identifier_ (Qual_identifier (Identifier "-"))
                    [Term_qual_identifier (Qual_identifier (Identifier nvar)),
                     Term_spec_constant (Spec_constant_numeral j)]
          nvar = "n"
          kstep = Term_qual_identifier_ (Qual_identifier (Identifier "not"))
                    [Term_qual_identifier_ (Qual_identifier (Identifier property))
                     [Term_qual_identifier (Qual_identifier (Identifier nvar))]]




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
  when True $
       case result of
         Just k -> putStrLn $ "Proved at step " ++ show k
         Nothing -> putStrLn $ "Failed to prove"
  return result

  where maxStep = 10
        debug = False



-- | Assertions for the base case
base :: String -> Numeral -> [Command]
base propName k =
  [Assert $ trans i | i <- [0..k-1]] ++
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
  [Assert (prop idx) | idx <- [1..k-1]] ++
  [Assert (trans idx) | idx <- [0..k-1]] ++
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


-- Invariant Generation
invGenProcess proverCmd model property stateVars invChan = forkIO $ do
  basePassed <- newChan
  baseProc <- invGenBaseProcess proverCmd model stateVars basePassed
  stepProc <- invGenStepProcess proverCmd model stateVars basePassed invChan
  return ()

assertTrue = Assert (Term_qual_identifier (Qual_identifier (Identifier "true")))

invGenBaseProcess proverCmd transitionSystem stateVars sink = forkIO $
  {-# SCC "invGenBaseProcess" #-}
  bracket (makeProverNamed proverCmd "invGenBase") closeProver $ \p -> do
    mapM_ (sendCommand p) transitionSystem
    sendCommand p (Assert
                   (Term_qual_identifier_ (Qual_identifier (Identifier "trans"))
                        [Term_spec_constant (Spec_constant_numeral 0)]))

    -- send the initial candidate set

    let refinement classes = do
          -- putStrLn "Start refinement iteration"
          let cs = [candidate classes "<=" 1]
          putStrLn $ "Checking invariant candidate " ++ show cs
          push 1 p
          sendCommand p
            (Assert (Term_qual_identifier_ (Qual_identifier (Identifier "not")) cs))
          -- putStrLn "Checking for UNSAT"
          valid <- isUnsat p
          if valid
               then do
                 putStrLn "(Base Valid) Invariant:"
                 print classes
                 pop 1 p
                 return ()
               else do
                 putStrLn "Invariant Candidate Not Valid"
                 next <- valuation p stateVars 1
                 pop 1 p
                 unless (next == classes) $ refinement next

    refinement [stateVars]


    -- Generate the initial candidates

    let loop = do
          writeChan sink assertTrue
          threadDelay 10000000 -- Sleep 100 milliseconds
          loop
    loop
    return ()

invGenStepProcess proverCmd model property source sink = forkIO $
  {-# SCC "invGenStepProcess" #-}
  bracket (makeProver proverCmd) closeProver $ \p -> do
    let loop = do
          c <- readChan source
          threadDelay 10000000 -- Sleep 100 milliseconds
          writeChan sink c
          loop

    loop
    return ()


checkInvariant prover invChan = do
  empty <- isEmptyChan invChan
  unless empty $ do
    inv <- readChan invChan
    putStrLn "Got an invariant"
    _ <- sendCommand prover inv
    return ()

-- | Given an equivalence, (over a partial order) generate a candidate invariant.
candidate equivClasses rel k =
  Term_qual_identifier_ (Qual_identifier (Identifier "and"))
                        (concatMap equiv equivClasses ++
                               ineq (map head equivClasses))
  where equiv (c:cs) =
          -- Generate "c(k) = c'(k) for each c in cs
          [Term_qual_identifier_ (Qual_identifier (Identifier "="))
                                  [Term_qual_identifier_
                                   (Qual_identifier (Identifier c))
                                   [time],
                                   Term_qual_identifier_
                                   (Qual_identifier (Identifier c'))
                                   [time]]
                                   | c' <- cs]
        equivalences = concatMap equiv equivClasses
        ineq [] = []
        ineq [t] = []
        ineq (r:s:ts) =
          (Term_qual_identifier_ (Qual_identifier (Identifier rel))
                                  [Term_qual_identifier_
                                   (Qual_identifier (Identifier r))
                                   [time],
                                   Term_qual_identifier_
                                   (Qual_identifier (Identifier s))
                                   [time]]):ineq (s:ts)

        time = Term_spec_constant (Spec_constant_numeral (k-1))

valuation p stateVars k = do
    Ga_response vals <- sendCommand p (Get_value terms)

    let res = zip stateVars vals
        sorted = sortBy (\(_,l) (_,r) -> compare l r) res
        grouped = groupBy (\(_,l) (_,r) -> l == r) sorted
        equiv = map (map fst) grouped
    putStrLn "Valuation: "
    print  res
    putStrLn "Refinement:"
    print equiv
    putStrLn "Done with the refinement"
    return equiv


  where terms = [Term_qual_identifier_ (Qual_identifier (Identifier sv)) [time]
                | sv <- stateVars]
        time = Term_spec_constant (Spec_constant_numeral (k-1))

-- Installation for testing
z3 :: [Char]
z3 = "ssh teme z3/bin/z3 -si -smt2 MODEL=true"

cvc3 = "cvc3 -lang smt2"




instance Eq Term where
   (Term_qual_identifier (Qual_identifier (Identifier t1))) ==
    (Term_qual_identifier (Qual_identifier (Identifier t2))) = t1 == t2

   (Term_spec_constant (Spec_constant_numeral t1)) == (Term_spec_constant (Spec_constant_numeral t2)) = t1 == t2


instance Ord Term where
   (Term_qual_identifier (Qual_identifier (Identifier "true"))) `compare`
    (Term_qual_identifier (Qual_identifier (Identifier "false"))) = LT

   (Term_qual_identifier (Qual_identifier (Identifier "false"))) `compare`
    (Term_qual_identifier (Qual_identifier (Identifier "true"))) = GT

   (Term_qual_identifier (Qual_identifier (Identifier "true"))) `compare`
    (Term_qual_identifier (Qual_identifier (Identifier "true"))) = EQ

   (Term_qual_identifier (Qual_identifier (Identifier "false"))) `compare`
    (Term_qual_identifier (Qual_identifier (Identifier "false"))) = EQ

   (Term_spec_constant (Spec_constant_numeral t1)) `compare`
    (Term_spec_constant (Spec_constant_numeral t2)) = t1 `compare` t2


   compare t1 t2 = error $ show t1 ++ show t2