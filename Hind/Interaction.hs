{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving #-}
module Hind.Interaction
  (Prover,
   makeProver, makeProverNamed, closeProver,
   sendCommand,
   checkSat,isSat,isUnsat,
   push,pop,
   getModel
   ) where

import Language.SMTLIB hiding (responses)
import qualified Language.SMTLIB as SMT
import System.Process
import System.IO
import Control.Concurrent
import Control.Exception
import Control.Monad
import Text.ParserCombinators.Poly
import System.Log.Logger



data Prover = Prover { requests :: Chan Command
                     , responses :: Chan Command_response
                     , threads :: [ThreadId]
                     , pid :: ProcessHandle
                     , name :: String
                     }

-- Create a prover connection
makeProverNamed :: String -> String -> IO Prover
makeProverNamed cmd nm = do

  (pipe_in,pipe_out,pipe_err,ph) <-   {-# SCC "runInteractiveCommand" #-} runInteractiveCommand cmd
  hSetBinaryMode pipe_in False

  hSetBinaryMode pipe_out False
  hSetBinaryMode pipe_err False

  -- Create input/output channels
  reqChannel <- {-# SCC "newChanReq" #-} newChan
  rspChannel <- {-# SCC "newChanRsp" #-} newChan


  -- Fork off processes for interaction
  let writer = do
        cmdReq <- readChan reqChannel
        hPutStrLn pipe_in (show cmdReq)
        hFlush pipe_in
        writer

  writerThd <-   {-# SCC "forkWriter" #-}
    forkIO $ bracket_ (return ())
             (hClose pipe_in)
             writer

  let reader rest = {-# SCC "reader" #-} do
        cnts <- hGetLine pipe_out
        -- putStrLn $ nm ++ " got a line " ++ cnts
        let (res,rem) = {-# SCC "parser" #-} runParser SMT.responses $ rest ++ (lexSMTLIB cnts)
        case res of
          Left err -> do
            -- putStrLn $ "Parse Error: " ++ show err
            -- putStrLn "with input "
            -- print $ rest ++ (lexSMTLIB  cnts)
            return ()

          Right val -> do
            mapM_ (writeChan rspChannel) val
        reader rem

  readerThd <-   {-# SCC "forkReader" #-}
    forkIO $ bracket_ (return ())
             (hClose pipe_out)
             (reader [])

  return $ Prover reqChannel rspChannel [readerThd,writerThd] ph nm

makeProver :: String -> IO Prover
makeProver cmd = do
  makeProverNamed cmd "unknown"





closeProver :: Prover -> IO ()
closeProver prover = do
  mapM_ killThread (threads prover)
  terminateProcess (pid prover)

sendCommand :: Prover -> Command -> IO Command_response
sendCommand prover cmd = do
  debugM ("Hind." ++ (name prover)) ("req:" ++ show cmd)
  writeChan (requests prover) cmd
  rsp <- readChan (responses prover)
  debugM ("Hind." ++ (name prover)) ("rsp:" ++ show rsp)
  return rsp




-- | Check satisfiability
checkSat :: Prover -> IO Status
checkSat prover = do
  res <- sendCommand prover Check_sat
  case res of
    (Cs_response status) -> return status
    _ -> fail $ show res


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
pop i = flip sendCommand (Pop i)



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
