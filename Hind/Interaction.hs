{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving #-}
module Hind.Interaction
  (Prover,
   makeProver, closeProver,
   sendCommand,
   checkSat,isSat,isUnsat,
   push,pop,
   getModel
   ) where

import Language.SMTLIB
import System.Process
import System.IO
import Control.Concurrent
import Control.Exception
import Control.Monad


data Prover = Prover { requests :: Chan Command
                     , responses :: Chan Command_response
                     , threads :: [ThreadId]
                     , pid :: ProcessHandle
                     }

-- Create a prover connection
makeProver :: String -> IO Prover
makeProver cmd = do
  (pipe_in,pipe_out,pipe_err,ph) <- runInteractiveCommand cmd
  hSetBinaryMode pipe_in False

  hSetBinaryMode pipe_out False
  hSetBinaryMode pipe_err False

  -- Create input/output channels
  reqChannel <- newChan
  rspChannel <- newChan

  -- Fork off processes for interaction
  let writer = do
        cmdReq <- readChan reqChannel
        hPutStrLn pipe_in (show cmdReq)
        hFlush pipe_in
        writer

  writerThd <- forkIO $ bracket_ (return ())
                                 (hClose pipe_in)
                                 writer


  let readLines = do
        rdy <- hWaitForInput pipe_out 50
        if rdy
          then do
            cur <- hGetLine pipe_out
            rest <- readLines
            return (cur ++ rest)
          else return []
  let reader = do
        -- cnts <- hGetLine pipe_out
        cnts <- readLines
        unless (null cnts) $ do
                 putStrLn $ "Got Response " ++ cnts
                 let parsedResponses = parseResponses cnts

                 mapM_ (writeChan rspChannel) parsedResponses
        reader
  readerThd <- forkIO $ bracket_ (return ())
                                 (hClose pipe_out)
                                 reader

  return $ Prover reqChannel rspChannel [readerThd,writerThd] ph



closeProver :: Prover -> IO ()
closeProver prover = do
  mapM_ killThread (threads prover)
  terminateProcess (pid prover)

sendCommand :: Prover -> Command -> IO Command_response
sendCommand prover cmd = do
  putStrLn $ "Req: " ++ show cmd
  writeChan (requests prover) cmd
  rsp <- readChan (responses prover)
  putStrLn $ "Rsp: " ++ show rsp
  return rsp

-- | Check satisfiability
checkSat :: Prover -> IO Status
checkSat prover = do
  (Cs_response status) <- sendCommand prover Check_sat
  return status

isSat, isUnsat :: Prover -> IO Bool
isSat = fmap sat . checkSat
  where sat Sat = True
        sat _ = False
isUnsat = fmap unsat . checkSat
  where unsat Unsat = True
        unsat _ = False

-- deriving instance Eq Status


-- | Manipulate prover state stack
push,pop :: Int -> Prover -> IO Command_response
push i = flip sendCommand (Push i)
pop i = flip sendCommand $ (Pop i)

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
