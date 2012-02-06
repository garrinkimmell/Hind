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
  , summaryFile :: Maybe String
  -- SMT Solver
  , smtCmd :: String -- The Solver
  , smtOpts :: String -- Solver options
  , sshRemote :: Maybe String -- Remote host to execute on
  , enablePrelude :: Bool -- Whether the logic should be set and
                     -- base/step declarations should be added.
  , pathCompression :: Bool

  -- Hind Options
  , intInvGen, boolInvGen :: Bool
  , timeout :: Maybe Float -- timeout, expressed in seconds
  , delayFinish :: Maybe Float -- amount of time to delay, expressed in seconds,
                   -- used for debugging


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
       , intInvGen = False &= help "Enable Integer Invariant Generation" &= typ "Boolean"
                     &= groupname "Model Checking Options"
       , boolInvGen = False &= help "Enable Boolean Invariant Generation" &= typ "Boolean"
                      &= groupname "Model Checking Options"

       , timeout = Nothing
             &= help "Timeout for model checking"
             &= groupname "Model Checking Options"
       , delayFinish = Nothing &=
                       help "Delay finishing model checking for given number of seconds"
                       &= groupname "Debugging"
       , pathCompression = False &= help "Enable path compression" &= groupname "Model Checking Options"
       , logLevel = "Hind=NOTICE" &= help "Logging Level (DEBUG,INFO,NOTICE)"
           &= groupname "Logging"
       , logFile = Nothing &= help "Log File"
           &= groupname "Logging"
       , summaryFile = Nothing &=
                       help "File to summarize results of checking a directory of files."
                       &= groupname "Logging"
       , enablePrelude = False &= help "Enable the insertion of base and step declarations."
                         &= groupname "SMT Solver"

       } &=
  program "hind" &=
  help "Prove safety properties using k-induction" &=
  summary "hind v0.3, (C) Garrin Kimmell 2011"
