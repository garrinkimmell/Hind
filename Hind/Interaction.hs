{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, DeriveDataTypeable, PackageImports #-}
module Hind.Interaction
  (Prover,ProverException(..),
   makeProver, makeProverNamed, closeProver,name,responses,
   sendCommand, sendScript,
   checkSat,isSat,isUnsat,
   push,pop,reset,
   getModel,
   ) where

-- import Hind.Chan

import Language.SMTLIB
import Data.Enumerator hiding (Error,mapM)
import Data.Enumerator.Binary(enumHandle)
import qualified Data.Enumerator.Binary as EB
import Data.Attoparsec.Enumerator(iterParser)

import qualified Language.SMTLIB as SMT
import System.Process
import System.IO
import Control.Concurrent hiding (Chan,readChan,writeChan,newChan,isEmptyChan)
import Control.Exception
import Control.Monad
import "mtl" Control.Monad.Trans(liftIO)
import Data.Typeable
import System.Log.Logger



data Prover = Prover { requests :: MVar Command
                     , responses :: MVar Command_response
                     , threads :: [ThreadId]
                     , pid :: ProcessHandle
                     , name :: String
                     , depth :: MVar Int
                     }

data ProverException = ProverException String [Command_response] deriving (Show,Typeable)
instance Exception ProverException

-- Create a prover connection
makeProverNamed :: String -> String -> IO Prover
makeProverNamed cmd nm = do

  (pipe_in,pipe_out,pipe_err,ph) <-
    {-# SCC "runInteractiveCommand" #-} runInteractiveCommand cmd
  -- hSetBinaryMode pipe_in False
  hSetBinaryMode pipe_out False
  -- hSetBinaryMode pipe_err False
  hSetBuffering pipe_in NoBuffering
  hSetBuffering pipe_out NoBuffering
  -- hSetBuffering pipe_err NoBuffering


  -- reqChannel <- {-# SCC "newChanReq" #-} newChan
  -- rspChannel <- {-# SCC "newChanRsp" #-} newChan


  -- Create input/output MVars
  reqMVar <- newEmptyMVar
  rspMVar <- newEmptyMVar

  -- Fork off process for interaction
  let reqRspLoop  = do
       req <- liftIO $ takeMVar reqMVar
       liftIO $ hPutStrLn pipe_in (show req)
       liftIO $ hPutStrLn pipe_in ";req"
       rsp <- iterParser command_response
       liftIO $ putMVar rspMVar rsp
       reqRspLoop

  reqRspThd <-
    forkIO $ bracket_ (return ()) (hClose pipe_in >> hClose pipe_out) $ do
           debugM "Hind" "Forking req/rsp thread"
           (run_ $ enumHandle 10 pipe_out $$ reqRspLoop)

  depth <- newMVar 0
  let prover = Prover reqMVar rspMVar [reqRspThd] ph nm depth
  -- Make sure that it always prints success.
  sendCommand prover (Set_option (Print_success True))
  return prover

makeProver :: String -> IO Prover
makeProver cmd = do
  makeProverNamed cmd "unknown"


closeProver :: Prover -> IO ()
closeProver prover = do
  debugM "Hind" "closeProver"
  mapM_ killThread (threads prover)
  -- mapM_ killThread (threads prover)
  terminateProcess (pid prover)

sendCommand :: Prover -> Command -> IO Command_response
sendCommand prover cmd = do
  debugM ((name prover) ++ ".interaction") ("req:" ++ show cmd)
  -- We set the uninterruptable mask here, so that we always get a
  -- request/response pair. Otherwise, the system will possibly kill the thread
  -- executing sendcommand somewhere between putting the request and taking the
  -- response.
  rsp' <- uninterruptibleMask_ $ do
    putMVar (requests prover) cmd
    rsp <- takeMVar (responses prover)
    rsp' <- reportErrors prover rsp []
    return rsp'
  debugM ((name prover) ++ ".interaction") ("rsp:" ++ show rsp')
  return rsp'

-- FIXME: This needs to be improved.
reportErrors p rsp@(Gen_response (Error str)) acc = do
  throw $ ProverException (name p) (reverse (rsp:acc))
  -- empty <- isEmptyChan (responses p)
  -- if empty
  --    then throw $ ProverException (name p) (reverse (rsp:acc))
  --    else do
  --      rsp' <- readChan (responses p)
  --      reportErrors p rsp' (rsp:acc)
reportErrors p rsp [] = return rsp
reportErrors p rsp acc = throw $ ProverException (name p) (reverse (rsp:acc))


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
   cur <- readMVar (depth p)
   when (cur > 0) $ pop cur p >> return ()
   return ()
  where
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
