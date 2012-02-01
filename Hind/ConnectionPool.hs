module Hind.ConnectionPool
  (ConnectionPool, newConnectionPool, closePool, withProver, withProverException) where

import Hind.Interaction
import Hind.Options
import Hind.Logging
import Hind.Chan

import Language.SMTLIB(Command(..))
import Control.Concurrent hiding (isEmptyChan,readChan)
import Control.Exception(finally,mask,throw,catch,onException,mask_)
import Control.Monad(unless)
import Prelude hiding (catch)


data ConnectionPool = ConnectionPool String (MVar [Prover])

-- Create a new connection pool
newConnectionPool :: String -> Int -> IO ConnectionPool
newConnectionPool proverCmd num = do
  provers <- sequence $ replicate num (makeProverNamed proverCmd "Hind.pool")
  mv <- newEmptyMVar
  putMVar mv provers
  return (ConnectionPool proverCmd mv)

closePool :: ConnectionPool -> IO ()
closePool (ConnectionPool _ pool) = do
  debugM "Hind" "closePool"
  provers <- takeMVar pool
  mapM_ closeProver provers

withProver :: ConnectionPool -> String -> (Prover -> IO ()) -> IO (ThreadId, IO ())
withProver pool name comp =
    withProverException pool name handler comp
  where handler e = throw e

withProverException :: ConnectionPool ->
                       String ->
                       (ProverException -> IO ()) ->  -- On Error
                       (Prover -> IO ()) ->
                       IO (ThreadId, IO ())
withProverException pool name onError comp = do
     prover <- getProver pool name
     tid <- forkIO $ (comp prover `catch` onError)
     let release = releaseProver pool prover
     return (tid,release)


getProver :: ConnectionPool -> String -> IO Prover
getProver (ConnectionPool proverCmd pool) name = do
  infoM name "Acquiring prover."
  provers <- takeMVar pool
  case provers of
    [] ->  do debugM name "Creating new prover."
              p <- makeProverNamed proverCmd name
              putMVar pool [p]
              -- push 1 p
              return (p { name = name})
    (p:ps) -> do
      putMVar pool ps
      let p' = p {name=name}
      -- push 1 p'
      return p'

releaseProver :: ConnectionPool -> Prover -> IO ()
releaseProver (ConnectionPool proverCmd pool) prover = do
  infoM (name prover) "Releasing prover."
  reset prover
  let prover' = prover { name = "Hind.pool" }
  ps <- takeMVar pool
  putMVar pool (prover':ps)
  return ()
