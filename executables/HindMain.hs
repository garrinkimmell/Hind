module Main where

import Hind(
       getOptions,file, getSMTCmd, -- options
       hindFile, -- parser
       setupLogger, getLogFile, logLevel, -- logging
       parCheck -- K-induction
       )
-- import Hind.KInduction
-- import Hind.Parser
-- import Hind.Chan
-- import Hind.Logging
-- import Hind.Options

import Text.Printf
import Control.Exception
import System.CPUTime
import Data.Time
import System.Environment

import Language.SMTLIB
import System.Log.Logger
import System.Log.Handler(setFormatter,close)
import System.Log.Handler.Simple
import System.Log.Formatter
import System.IO

import Control.Concurrent(forkIO)



{-
import Criterion.Main (defaultMain, bench)
import Criterion.Config
-}
time :: IO t -> IO t
time a = do
    wallStart <- getCurrentTime
    start <- getCPUTime
    v <- a
    end   <- getCPUTime
    wallEnd <- getCurrentTime
    let diff = (fromIntegral (end - start)) / (10^12)
    printf "Computation time: %0.6f sec\n" (diff :: Double)
    printf "Wall time: %0.6f sec\n"
             ((fromRational $toRational $ diffUTCTime wallEnd wallStart) :: Double)
    return v

main = do
  options <- getOptions
  setupLogger (getLogFile options) (logLevel options)
  infoM "Hind" ("Checking file " ++ (file options))
  debugM "Hind" $ "Using smt command " ++ (getSMTCmd options)

  parsed <- hindFile (file options)
  time $ parCheck options parsed



z3 :: [Char]
z3 = "ssh teme z3/bin/z3 -si -smt2 MODEL=true"

