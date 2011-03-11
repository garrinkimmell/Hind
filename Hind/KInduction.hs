module Hind.KInduction
  (parCheck) where

import Hind.Parser(HindFile(..))
import Hind.PathCompression
import Hind.Interaction
import Hind.InvGen
import Language.SMTLIB
import Control.Exception
import Control.Monad
import Control.Concurrent
import Data.List(sortBy, groupBy)
import System.Log.Logger

parCheck :: String -> HindFile -> IO ()
parCheck proverCmd hindFile = do
    -- Add in path compression
    let hindFile' = addPathCompression hindFile

    resultChan <- newChan

    -- Inferred invariants will show up on the invChan
    invChan <- newChan
    (invGenBase,invGenStep) <- invGenProcess proverCmd hindFile' invChan
    let invChanBase = invChan
    invChanBase <- dupChan invChan
    invChanStep <- dupChan invChan

    baseProc <- baseProcess proverCmd hindFile' resultChan invChanBase
    stepProc <- stepProcess proverCmd hindFile' resultChan invChanStep
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
       then noticeM "Hind" "Passed" >> return Nothing
       else noticeM "Hind" "Failed" >> return Nothing

    -- Delay, just so that we can let invariant generation catch up.
    -- threadDelay 10000000

    -- Clean up all the threads
    mapM_ killThread [invGenBase,invGenStep,baseProc,stepProc]
    return ()


data ProverResult = BasePass Integer | BaseFail Integer | StepPass Integer | StepFail Integer
  deriving Show

-- baseProcess proverCmd model property resultChan invChan = forkIO $
baseProcess
  :: String -> HindFile -> Chan ProverResult -> Chan POVal -> IO ThreadId
baseProcess proverCmd hindFile resultChan invChan = forkIO $
  bracket (makeProverNamed proverCmd "baseProcess") closeProver $ \p -> do
    infoM "Hind.baseProcess" "Base Prover Started"
    _ <- mapM (sendCommand p) model
    infoM "Hind.baseProcess" "System Defined"
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
  where trans i = Term_qual_identifier_ (Qual_identifier transition)
                    [Term_spec_constant (Spec_constant_numeral i)]

        prop i =
          Term_qual_identifier_ (Qual_identifier (Identifier "not"))
            [Term_qual_identifier_ (Qual_identifier property)
                    [Term_spec_constant (Spec_constant_numeral i)]]
        Script model = hindScript hindFile
        [property] = hindProperties hindFile
        transition = hindTransition hindFile

stepProcess :: String -> HindFile -> Chan ProverResult -> Chan POVal -> IO ThreadId
stepProcess proverCmd hindFile resultChan invChan = forkIO $
  bracket (makeProverNamed proverCmd "stepProcess") closeProver $ \p -> do
    infoM "Hind.stepProcess" "Step Prover Started"
    _ <- mapM (sendCommand p) model
    infoM "Hind.stepProcess" "System Defined"

    -- Send '(not (prop n))'
    sendCommand p (Assert kstep)

    let loop k = do
          -- Send '(trans (n-k+1)'
          sendCommand p (Assert (trans (k - 1)))


          -- Send '(prop (n-k))'
          sendCommand p (Assert (prop k))

          -- Assert path compression
          sendCommand p (stateCharacterisic k)

          res <- isUnsat p
          if res
               then do
                 writeChan resultChan (StepPass k)
               else do
                 writeChan resultChan (StepFail k)
                 loop (k+1)
    loop 1

    where prop i = Term_qual_identifier_ (Qual_identifier  property)
                   [prev i]
          trans i = Term_qual_identifier_ (Qual_identifier transition)
                     [prev i]
          prev j = Term_qual_identifier_ (Qual_identifier (Identifier "-"))
                    [Term_qual_identifier (Qual_identifier (Identifier nvar)),
                     Term_spec_constant (Spec_constant_numeral j)]
          nvar = "n"
          kstep = Term_qual_identifier_ (Qual_identifier (Identifier "not"))
                    [Term_qual_identifier_ (Qual_identifier  property)
                     [Term_qual_identifier (Qual_identifier (Identifier nvar))]]
          Script model = hindScript hindFile
          [property] = hindProperties hindFile
          transition = hindTransition hindFile




checkInvariant prover invChan = do
  empty <- isEmptyChan invChan
  unless empty $ do
    inv <- readChan invChan
    putStrLn "Got an invariant"
    _ <- sendCommand prover inv
    return ()


-- Installation for testing
z3 :: [Char]
z3 = "ssh teme z3/bin/z3 -si -smt2 MODEL=true"

cvc3 = "cvc3 -lang smt2"




