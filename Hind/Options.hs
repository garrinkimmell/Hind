{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}
-- | Options for Hind, including command line argument parsing.
module Hind.Options(

   getOptions,
   getSMTCmd,
   getLogFile,
   HindOpts(..)

 ) where

import System.Console.CmdArgs
import System.Log.Logger
import Data.Maybe
import System.FilePath

-- | Get and parse the command line arguments
getOptions :: IO HindOpts
getOptions = cmdArgs hindArgs


-- | Construct a command line for starting a prover process.
getSMTCmd :: HindOpts -> String
getSMTCmd opts = remote ++ " " ++ smtCmd opts ++ " " ++ smtOpts opts
  where remote = maybe "" ("ssh "++) (sshRemote opts)

-- | Get the log file. If a specific file is not defined, then default to adding
-- '.log' to the basename of the input file.
getLogFile :: HindOpts -> String
getLogFile opts = fromMaybe def (logFile opts)
  where def = replaceExtension (file opts) ".log"

data HindOpts =  HindOpts {
  -- Input file (transition system)
    file :: String
   -- Logging
  , logLevel :: String -- The output log level
  , logFile :: Maybe String
  -- SMT Solver
  , smtCmd :: String -- The Solver
  , smtOpts :: String -- Solver options
  , sshRemote :: Maybe String -- Remote host to execute on

  -- Hind Options
  , invGen :: Bool
  , timeout :: Maybe Float -- timeout, expressed in seconds

  } deriving (Show,Data,Typeable)


hindArgs = HindOpts {
         file = def &= help "Transition File" &= typFile
           &= groupname "Main"
       , smtCmd = "z3" &= help "SMT Prover" &= opt "z3"
           &= groupname "SMT Solver"
       , smtOpts =  "-smt2 -si MODEL=true" &= help "SMT Options"
           &= groupname "SMT Solver"
       , sshRemote = Nothing &= help "Remote Host"
           &= name "remote"
           &= groupname "SMT Solver"
       , invGen = False &= help "Enable Invariant Generation" &= typ "Boolean"
                  &= groupname "Model Checking Options"
       , timeout = Nothing
             &= help "Timeout for model checking"
             &= groupname "Model Checking Options"
       , logLevel = "Hind=NOTICE" &= help "Logging Level (DEBUG,INFO,NOTICE)"
           &= groupname "Logging"
       , logFile = Nothing &= help "Log File"
           &= groupname "Logging"


       } &=
  program "hind" &=
  help "Prove safety properties using k-induction" &=
  summary "hind v0.3, (C) Garrin Kimmell 2011"

