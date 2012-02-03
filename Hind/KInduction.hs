{-# LANGUAGE PatternGuards, ScopedTypeVariables  #-}
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
import Hind.Utils

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
    let withPrelude = if enablePrelude opts then addStepVars hindFile else hindFile
    let withPathCompression = if pathCompression opts then addPathCompression withPrelude else withPrelude


    let hindFile' = withPathCompression
    -- let hindFile' = addPathCompression hindFile

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
    stepProc <- stepProcess pool hindFile' (pathCompression opts) resultChan invChanStep errAction
    modifyMVar_ children (\tids -> return $ tids ++ [("base",baseProc),("step",stepProc)])

    when (Opts.invGen opts) $ do
      -- Now kick off the invariant generation process
      invGenTID <- invGenProcess pool hindFile' invChan errAction
      modifyMVar_ children
         (\tids -> return $ tids ++ [("invGen",invGenTID)])

    let loop basePass stepPass = do
          res <- readChan resultChan
          case res of
            BasePass k
              | Just sp <- stepPass,
                k >= sp -> return (Pass sp)
              | otherwise -> loop (Just k) stepPass
            BaseFail k -> return (Fail k)
            StepPass k
              | Just bp <- basePass,
                k <= bp -> return (Pass k)
              | otherwise -> loop basePass (Just k)
            StepFail k -> loop basePass stepPass

    let cleanup = do
          tids <- readMVar children
          infoM "Hind" ("Killing threads in cleanup" ++ (unwords (map fst tids)))

          forM_  tids (\(n,(tid,final)) -> do
                   debugM "Hind" $ "Closing " ++ n
                   killThread tid
                   final
                   )




    -- If your timeout is so short that you can't even get to this point, then
    -- you're pretty much screwed. Sorry.
    let errHandler e@(ProverException n errs) = do
          let shown = concatMap show errs
          mapM_ (errorM n) $ lines shown
          return (Error e)

    flip finally cleanup $ handle errHandler  $ do
       result <- loop Nothing Nothing
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


baseProcess
  :: ConnectionPool -> HindFile -> Chan ProverResult -> Chan POVal ->
     (ProverException -> IO ()) ->
     IO (ThreadId, IO ())
baseProcess pool hindFile resultChan invChan onError =
  withProverException pool "Hind.baseProcess" onError $  \p -> do
    -- infoM "Hind.baseProcess" "Base Prover Started"
    -- _ <- mapM (sendCommand p) model
    defineSystem hindFile p
    infoM "Hind.baseProcess" "System Defined"

    let trans' x = trans hindFile (int 0  `minusTerm` int x)
        prop' = prop hindFile
        assert = assertTerm p

    let loop k invId = do
          -- checkInvariant p invChan
          invId' <- getAndProcessInv p invChan invId
                    (assertBaseInvState p k)
                    (assertBaseInv p k)

          -- send (trans (+ _base k)
          assert (trans' (k-1))

          -- send (not (p (k)), check for unsat
          push 1 p
          -- (not (implies (= _base k-1) (P 0)))
          assert (notTerm (impliesTerm
                           (equalTerm base (int 0 `minusTerm` (int (k-1))))
                           (prop' (int 0))))

          -- assert (notTerm (prop' (k-1)))
          ok <- isUnsat p
          pop 1 p
          if ok
            then do
            -- assert the property for the current k
               when (k > 1) $
                 assert (prop' (int 0 `minusTerm` int (k-1))) >> return ()
               infoM "Hind.baseProcess" $ "Passed for step " ++ show k
               writeChan resultChan (BasePass k)
               loop (k+1) invId'
            else do
               infoM "Hind.baseProcess" $ "Passed for step " ++ show k
               writeChan resultChan (BaseFail k)
    _ <- isUnsat p
    loop 1 NoInv

stepProcess ::
  ConnectionPool -> HindFile -> Bool -> Chan ProverResult -> Chan POVal ->
  (ProverException -> IO ()) ->
  IO (ThreadId,IO ())
stepProcess pool hindFile pathCompress resultChan invChan onError =
  withProverException pool "Hind.stepProcess" onError $  \p -> do
    when pathCompress $ do
      sendCommand p (Set_option (Produce_unsat_cores True)) >> return ()


    -- infoM "Hind.stepProcess" "Step Prover Started"
    defineSystem hindFile p
    infoM "Hind.stepProcess" "System Defined"


    let trans' = trans hindFile . stepTime
        prop' = prop hindFile . stepTime
        assert = assertTerm p


    -- Send '(not (prop (- _n 0))'
    assert (notTerm (prop' 0))
    assert (trans' 0)


    -- Send path compression
    when pathCompress $ sendCommand p (stateCharacteristic 0) >> return ()

    let loop k invId = do
          -- Add any additional invariants.
          invId' <- getAndProcessInv p invChan invId
                    (assertStepInvState p k)
                    (assertStepInv p k)


          -- Send '(trans (n-k+1)'
          assert (trans' k)

          -- Send '(prop (n-k))'
          assert (prop' k)

          -- Assert path compression
          when pathCompress $ do
            -- sendCommand p (Set_option (Produce_unsat_cores True))
            sendCommand p (stateCharacteristic k)
            ok <- isUnsat p
            when ok $ do
              debugM "Hind.stepProcess" "Path compression causes unsat."
              rsp <- sendCommand p Get_unsat_core
              debugM "Hind.stepProcess" ("Unsat core" ++ show rsp)


          res <- isUnsat p
          if res
            then do
              infoM "Hind.stepProcess" $ "Passed for step " ++ show k
              writeChan resultChan (StepPass k)
            else do
                 infoM "Hind.stepProcess" $ "Failed for step " ++ show k
                 writeChan resultChan (StepFail k)
                 loop (k+1) invId'
    loop 1 NoInv




addStepVars hf = hf { hindScript = Script (stepCmds ++ scr) }
  where Script scr = hindScript hf
        stepCmds = [Declare_fun baseVar [] (Sort_identifier (Identifier "Int")),
                    -- Assert (Term_qual_identifier_ (Qual_identifier (Identifier "="))
                    --         [Term_qual_identifier (Qual_identifier (Identifier baseVar)),
                    --          Term_spec_constant (Spec_constant_numeral 0)]),

                    Assert (Term_qual_identifier_ (Qual_identifier (Identifier "<="))
                            [Term_qual_identifier (Qual_identifier (Identifier baseVar)),
                             Term_spec_constant (Spec_constant_numeral 0)]),

                    Declare_fun indVar [] (Sort_identifier (Identifier "Int")),
                    Assert (Term_qual_identifier_ (Qual_identifier (Identifier ">="))
                            [Term_qual_identifier (Qual_identifier (Identifier indVar)),
                             Term_qual_identifier (Qual_identifier (Identifier baseVar))])
                   ]




-- Installation for testing
z3 :: [Char]
z3 = "ssh teme z3/bin/z3 -si -smt2 MODEL=true"

cvc3 = "cvc3 -lang smt2"
