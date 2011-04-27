module Hind.ConnectionPool
  (ConnectionPool, newConnectionPool, withProver) where

import Hind.Interaction
import Hind.Options
import Hind.Logging

import Language.SMTLIB(Command(..))
import Control.Concurrent
import Control.Exception(finally)

data ConnectionPool = ConnectionPool String (MVar [Prover])

-- Create a new connection pool
newConnectionPool :: String -> Int -> IO ConnectionPool
newConnectionPool proverCmd num = do
  provers <- sequence $ replicate num (makeProverNamed proverCmd "Hind.pool")
  mv <- newEmptyMVar
  putMVar mv provers
  return (ConnectionPool proverCmd mv)

withProver :: ConnectionPool -> String -> (Prover -> IO ()) -> IO ThreadId
withProver pool name comp = do

   prover <- getProver pool name
   forkIO $ comp prover >> return () `finally` releaseProver pool prover


getProver :: ConnectionPool -> String -> IO Prover
getProver (ConnectionPool proverCmd pool) name = do
  debugM name "Aquiring prover."
  provers <- takeMVar pool
  case provers of
    [] ->  makeProverNamed proverCmd name
    (p:ps) -> do
      putMVar pool ps
      push 1 p
      return (p {name=name})

releaseProver :: ConnectionPool -> Prover -> IO ()
releaseProver (ConnectionPool proverCmd pool) prover = do
  debugM (name prover) "Releasing prover."
  let prover' = prover { name = "Hind.pool" }
  -- This is intended to do a reset. There doesn't seem to be a 'reset' command,
  -- so we are assuming that the stack is cleaned up by whatever uses the
  -- prover. This isn't safe, and we really should either keep the stack size in
  -- the Prover (TODO) or else figure out how to get the stack depth.
  reset prover'
  ps <- takeMVar pool
  putMVar pool (prover':ps)
  return ()


