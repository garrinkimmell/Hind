{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving #-}
module Hind.Interaction
  (Prover,
   makeProver, makeProverNamed, closeProver,name,responses,
   sendCommand, sendScript,
   checkSat,isSat,isUnsat,
   push,pop,reset,
   getModel,
   ) where

import Hind.Chan

import Language.SMTLIB
import qualified Language.SMTLIB as SMT
import System.Process
import System.IO
import Control.Concurrent hiding (Chan,readChan,writeChan,newChan,isEmptyChan)
import Control.Exception
import Control.Monad
import Text.ParserCombinators.Poly
import System.Log.Logger



data Prover = Prover { requests :: Chan Command
                     , responses :: Chan Command_response
                     , threads :: [ThreadId]
                     , pid :: ProcessHandle
                     , name :: String
                     , depth :: MVar Int
                     }

-- Create a prover connection
makeProverNamed :: String -> String -> IO Prover
makeProverNamed cmd nm = do

  (pipe_in,pipe_out,pipe_err,ph) <-
    {-# SCC "runInteractiveCommand" #-} runInteractiveCommand cmd
  hSetBinaryMode pipe_in False
  hSetBinaryMode pipe_out False
  hSetBinaryMode pipe_err False
  -- hSetBuffering pipe_in NoBuffering
  -- hSetBuffering pipe_out NoBuffering
  -- hSetBuffering pipe_err NoBuffering

  -- Create input/output channels
  reqChannel <- {-# SCC "newChanReq" #-} newChan
  rspChannel <- {-# SCC "newChanRsp" #-} newChan


  -- Fork off processes for interaction
  let writer = do
          cmdReq <- readChan reqChannel
          hPutStrLn pipe_in (show cmdReq)
          hPutStrLn pipe_in ";req"
          hFlush pipe_in
          writer

  writerThd <-   {-# SCC "forkWriter" #-}
    forkIO $ bracket_ (return ())
             (hClose pipe_in)
             writer

  let reader = {-# SCC "reader" #-} do
        SMT.commandResponseSource pipe_out (\cmd -> writeChan rspChannel cmd)

  readerThd <-   {-# SCC "forkReader" #-}
    forkIO $ bracket_ (return ())
             (hClose pipe_out)
             reader

  depth <- newMVar 0
  return $ Prover reqChannel rspChannel [readerThd,writerThd] ph nm depth

makeProver :: String -> IO Prover
makeProver cmd = do
  makeProverNamed cmd "unknown"





closeProver :: Prover -> IO ()
closeProver prover = do
  mapM_ killThread (threads prover)
  terminateProcess (pid prover)

sendCommand :: Prover -> Command -> IO Command_response
sendCommand prover cmd = mask_ $ do
  debugM ((name prover) ++ ".interaction") ("req:" ++ show cmd)
  writeChan (requests prover) cmd
  rsp <- readChan (responses prover)
  debugM ((name prover) ++ ".interaction") ("rsp:" ++ show rsp)
  return rsp


sendScript :: Prover -> Script -> IO [Command_response]
sendScript prover (Script cmds) = mapM (sendCommand prover) cmds



-- | Check satisfiability
checkSat :: Prover -> IO (Maybe Status)
checkSat prover = do
  res <- sendCommand prover Check_sat
  case res of
    (Cs_response status) -> return (Just status)
    _ -> do -- errorM (name prover) $ "checkSat: " ++ show res
            return Nothing


isSat, isUnsat :: Prover -> IO Bool
isSat p = do status <- checkSat p
             return $ maybe False sat status
  where sat Sat = True
        sat _ = False
isUnsat p = do status <- checkSat p
               return $ maybe False unsat status
  where unsat Unsat = True
        unsat _ = False

-- deriving instance Eq Status


-- | Manipulate prover state stack
push,pop :: Int -> Prover -> IO Command_response
push i p = do
     cur <- takeMVar (depth p)
     putMVar (depth p) (cur + i)
     sendCommand p (Push i)

pop i p = do
    cur <- takeMVar (depth p)
    putMVar (depth p) (cur - i)
    sendCommand p (Pop i)

reset p = do
   rsp <- sendCommand p (Get_info Name)
   if isNameInfo rsp
      then debugM (name p) "Drained channel"
      else drainChan
   -- case rsp of
   --   Gen_response r ->  debugM (name p) $ "Gen_response" ++ show r
   --   Info_response r -> debugM (name p) $ "Channel is drained"
   --   Cs_response r -> debugM (name p) $ "Cs_response" ++ show r
   --   Gi_response r -> debugM (name p) $ "Gi_response" ++ show r
   --   Gv_response r -> debugM (name p) $ "Gv_response" ++ show r
   --   Gta_response r -> debugM (name p) $ "Gta_response" ++ show r
   --   Gp_response r -> debugM (name p) $ "Gp_response" ++ show r
   --   Gv_response r -> debugM (name p) $ "Gv_response" ++ show r
   --   _ -> debugM (name p) "Didn't drain channel" -- drainChan
   cur <- readMVar (depth p)
   when (cur > 0) $ pop cur p >> return ()
   return ()
   where drainChan = do
                 rsp <- readChan (responses p)
                 if isNameInfo rsp
                    then debugM (name p) "Drained channel"
                    else drainChan
         -- Z3 doesn't reply correctly
         isNameInfo
           (Gp_response
            (S_exprs
             [S_exprs [S_expr_constant (Spec_constant_string "name"),
                       S_expr_constant (Spec_constant_string "Z3")]])) =
           True
         isNameInfo _ = False


-- | Get the current model
getModel :: Prover -> IO Command_response
getModel prover= do
  let model_cmd = (Get_info (Info_flag "model"))
  res <- sendCommand prover model_cmd
  print res
  return res


{-

Test Cases

t1 = do
  p <- makeProver z3 -- "tee /tmp/test-z3"
  sendCommand p assertTrue
  closeProver p

assertTrue = Assert $ Term_qual_identifier $ Qual_identifier $ Identifier "true"

-}
