module Hind.KInduction
  (parCheck) where

import Hind.Parser(HindFile(..))
import Hind.Options as Opts
import Hind.PathCompression
import Hind.Interaction
import Hind.InvGen
import Hind.Chan

import Language.SMTLIB
import Control.Exception
import Control.Monad

import Control.Concurrent(ThreadId,forkIO,killThread,threadDelay,newMVar, modifyMVar_,readMVar)
import Data.List(sortBy, groupBy)
import System.Log.Logger


parCheck :: HindOpts -> HindFile -> IO Bool
parCheck opts hindFile = do
    let proverCmd = getSMTCmd opts
    -- Add in path compression and step vars.
    let hindFile' = addStepVars $ addPathCompression hindFile


    -- We track the fork  threads, so we can kill them.
    children <- newMVar []

    resultChan <- newChan
    -- Inferred invariants will show up on the invChan.
    invChan <- newChan

    -- FIXME: This will space leak, because it leaves an invChan that's not
    -- drained. It may be better to pass 'invChan' directly to the base or step
    -- process.
    invChanBase <- dupChan invChan
    invChanStep <- dupChan invChan


    -- First start the main proof process
    baseProc <- baseProcess proverCmd hindFile' resultChan invChanBase
    stepProc <- stepProcess proverCmd hindFile' resultChan invChanStep
    modifyMVar_ children (\tids -> return $ tids ++ [baseProc,stepProc])



    when (Opts.invGen opts) $ do
      -- Now kick off the invariant generation process
      (invGenBase,invGenStep) <- invGenProcess proverCmd hindFile' invChan
      modifyMVar_ children (\tids -> return $ tids ++ [invGenBase,invGenStep])


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
       then noticeM "Hind" (file opts ++ " Passed") >> return Nothing
       else noticeM "Hind" (file opts ++ " Failed") >> return Nothing

    -- Clean up all the threads
    tids <- readMVar children
    mapM_ killThread tids
    return result


data ProverResult = BasePass Integer | BaseFail Integer | StepPass Integer | StepFail Integer
  deriving Show

-- baseProcess proverCmd model property resultChan invChan = forkIO $
baseProcess
  :: String -> HindFile -> Chan ProverResult -> Chan POVal -> IO ThreadId
baseProcess proverCmd hindFile resultChan invChan = forkIO $
  bracket (makeProverNamed proverCmd "Hind.baseProcess") closeProver $ \p -> do
    infoM "Hind.baseProcess" "Base Prover Started"
    _ <- mapM (sendCommand p) model
    infoM "Hind.baseProcess" "System Defined"
    let loop k invId = do
          -- checkInvariant p invChan
          invId' <- getAndProcessInv p invChan invId
                    (assertBaseInvState p k)
                    (assertBaseInv p k)

          -- send (trans (k - 1)
          sendCommand p (Assert (trans (k - 1)))
          -- send (not (p (k))
          sendCommand p (Assert (prop (k - 1)))
          res <- isUnsat p
          if res
             then do
               writeChan resultChan (BasePass k)
               loop (k+1) invId'
             else do
               writeChan resultChan (BaseFail k)
    loop 1 NoInv
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
  bracket (makeProverNamed proverCmd "Hind.stepProcess") closeProver $ \p -> do
    infoM "Hind.stepProcess" "Step Prover Started"
    _ <- mapM (sendCommand p) model
    infoM "Hind.stepProcess" "System Defined"

    -- Send '(not (prop n))'
    sendCommand p (Assert kstep)

    -- Send path compression
    sendCommand p (stateCharacterisic 0)

    let loop k invId = do
          -- Add any additional invariants.
          invId' <- getAndProcessInv p invChan invId
                    (assertStepInvState p k)
                    (assertStepInv p k)


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
                 loop (k+1) invId'
    loop 1 NoInv

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


addStepVars hf = hf { hindScript = Script (stepCmds ++ scr) }
  where Script scr = hindScript hf
        stepCmds = [Declare_fun "_base" [] (Sort_identifier (Identifier "Int")),
                    Assert (Term_qual_identifier_ (Qual_identifier (Identifier "="))
                            [Term_qual_identifier (Qual_identifier (Identifier "_base")),
                             Term_spec_constant (Spec_constant_numeral 0)]),
                    Declare_fun "n" [] (Sort_identifier (Identifier "Int")),
                    Assert (Term_qual_identifier_ (Qual_identifier (Identifier ">="))
                            [Term_qual_identifier (Qual_identifier (Identifier "n")),
                             Term_spec_constant (Spec_constant_numeral 0)])
                   ]




-- Installation for testing
z3 :: [Char]
z3 = "ssh teme z3/bin/z3 -si -smt2 MODEL=true"

cvc3 = "cvc3 -lang smt2"




