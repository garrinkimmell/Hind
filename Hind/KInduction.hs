module Hind.KInduction
  (parCheck, Result(..)) where

import Hind.Constants
import Hind.Parser(HindFile(..))
import Hind.Options as Opts
import Hind.PathCompression
import Hind.Interaction
import Hind.InvGen
import Hind.Chan
import Hind.ConnectionPool

import Language.SMTLIB hiding (Error,Timeout)
import Control.Exception
import Control.Monad

import Control.Concurrent
  (ThreadId,forkIO,killThread,threadDelay,newMVar, modifyMVar_,readMVar,
   newEmptyMVar, putMVar, takeMVar,swapMVar,myThreadId)
import Data.List(sortBy, groupBy)
import System.Log.Logger
import qualified System.Timeout as TO
import Prelude hiding (catch)

data Result = Pass Integer
            | Fail Integer
            | Error ProverException
            | Timeout deriving (Show)

parCheck :: ConnectionPool -> HindOpts -> HindFile -> IO Result
parCheck pool opts hindFile = withTimeout $ do

    -- Add in path compression and step vars.
    -- let hindFile' = addStepVars $ addPathCompression hindFile
    let hindFile' = addPathCompression hindFile


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


    -- Set up what to do if the prover raises an exception
    tid <- myThreadId
    let errAction :: ProverException -> IO ()
        errAction = \e -> throwTo tid e

    -- First start the main proof process
    baseProc <- baseProcess pool hindFile' resultChan invChanBase errAction
    stepProc <- stepProcess pool hindFile' resultChan invChanStep errAction
    modifyMVar_ children (\tids -> return $ tids ++ [("base",baseProc),("step",stepProc)])

    when (Opts.invGen opts) $ do
      -- Now kick off the invariant generation process
      (invGenBase,invGenStep) <- invGenProcess pool hindFile' invChan errAction
      modifyMVar_ children
         (\tids -> return $ tids ++ [("invGenBase",invGenBase),("invGenStep",invGenStep)])

    let loop basePass = do
          res <- readChan resultChan
          case res of
            BasePass k -> loop k
            BaseFail k -> return (Fail k)
            StepPass k -> return (Pass k)
            StepFail k -> loop basePass

    let cleanup = do
          tids <- readMVar children
          infoM "Hind" "Killing threads in cleanup"
          forM_  tids (\(n,(tid,final)) -> do
                   debugM "Hind" $ "Closing " ++ n
                   killThread tid
                   final)



    -- If your timeout is so short that you can't even get to this point, then
    -- you're pretty screwed. Sorry.
    let errHandler e@(ProverException n errs) = do
          let shown = concatMap show errs
          mapM_ (errorM n) $ lines shown
          return (Error e)

    flip finally cleanup $ handle errHandler  $ do
       result <- loop 1
       case result of
         Pass _ -> noticeM "Hind" (file opts ++ " Passed")
         Fail _ -> noticeM "Hind" (file opts ++ " Failed")
         _ -> return ()
       return result


  where withTimeout m
          | Nothing <- timeout opts = m `catch` handler
          | Just secs <- timeout opts = do
             result <- newEmptyMVar
             workerTid <- forkIO $ do
                        res <- m `catch` handler
                        putMVar result (Just res)
             timeoutTid <- forkIO $ do
                               -- Multiply by a million to get microseconds.
                               threadDelay (round (secs * 1000000.0))
                               putMVar result Nothing
             r <- takeMVar result
             debugM "Hind" "Killing threads in timeout"
             mapM_ killThread [workerTid,timeoutTid]
             case r of
               Just val -> return val
               Nothing -> do
                 noticeM "Hind"
                          (file opts ++ " Timeout (" ++ show secs ++ " seconds)")
                 return Timeout
        -- The hander is goofy, but we want it to continue to catch the (unknown)
        -- number of exceptions that may be thrown.
        handler :: ProverException -> IO Result
        handler e@(ProverException _ _) = return (Error e) `catch` handler



data ProverResult = BasePass Integer | BaseFail Integer | StepPass Integer | StepFail Integer
  deriving Show

-- baseProcess proverCmd model property resultChan invChan = forkIO $
baseProcess
  :: ConnectionPool -> HindFile -> Chan ProverResult -> Chan POVal ->
     (ProverException -> IO ()) ->
     IO (ThreadId, IO ())
baseProcess pool hindFile resultChan invChan onError =
  withProverException pool "Hind.baseProcess" onError $  \p -> do
    -- infoM "Hind.baseProcess" "Base Prover Started"
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

stepProcess ::
  ConnectionPool -> HindFile -> Chan ProverResult -> Chan POVal ->
  (ProverException -> IO ()) ->
  IO (ThreadId,IO ())
stepProcess pool hindFile resultChan invChan onError =
  withProverException pool "Hind.stepProcess" onError $  \p -> do
    -- infoM "Hind.stepProcess" "Step Prover Started"
    _ <- mapM (sendCommand p) model
    infoM "Hind.stepProcess" "System Defined"

    -- Send '(not (prop n))'
    sendCommand p (Assert kstep)

    -- Send path compression
    sendCommand p (stateCharacteristic 0)

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
          sendCommand p (stateCharacteristic k)

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
                    [Term_qual_identifier (Qual_identifier (Identifier indVar)),
                     Term_spec_constant (Spec_constant_numeral j)]
          kstep = Term_qual_identifier_ (Qual_identifier (Identifier "not"))
                    [Term_qual_identifier_ (Qual_identifier  property)
                     [Term_qual_identifier (Qual_identifier (Identifier indVar))]]
          Script model = hindScript hindFile
          [property] = hindProperties hindFile
          transition = hindTransition hindFile


addStepVars hf = hf { hindScript = Script (stepCmds ++ scr) }
  where Script scr = hindScript hf
        stepCmds = [Declare_fun baseVar [] (Sort_identifier (Identifier "Int")),
                    Assert (Term_qual_identifier_ (Qual_identifier (Identifier "="))
                            [Term_qual_identifier (Qual_identifier (Identifier baseVar)),
                             Term_spec_constant (Spec_constant_numeral 0)]),
                    Declare_fun indVar [] (Sort_identifier (Identifier "Int")),
                    Assert (Term_qual_identifier_ (Qual_identifier (Identifier ">="))
                            [Term_qual_identifier (Qual_identifier (Identifier indVar)),
                             Term_spec_constant (Spec_constant_numeral 0)])
                   ]





-- Installation for testing
z3 :: [Char]
z3 = "ssh teme z3/bin/z3 -si -smt2 MODEL=true"

cvc3 = "cvc3 -lang smt2"




