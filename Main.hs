module Main where

import Hind.KInduction
import Hind.Parser
import Hind.Chan
import Hind.Logging

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

{-
main' = do
  args <- getArgs
  case args of
    (proverCmd:modelFile:property:rest) ->
      do cnts <- readFile modelFile
         putStrLn "Working..."
         let scr@(Script model) = parseScript cnts
         withArgs rest $
	          defaultMain [bench "parallel" $ parCheck proverCmd model property
                              ,bench "sequential" $ seqCheck proverCmd model property]

-}
main = do

  args <- getArgs
  case args of
    [proverCmd, fname, level] -> do
      -- Set up the logger
      setupLogger fname level

      infoM "Hind" ("Checking file " ++ fname)

      res <- hindFile fname

      time $ parCheck proverCmd res
      -- close h
      return ()

    _ -> putStrLn "usage: hind <prover command> <hind file> <LOGLEVEL>"


z3 :: [Char]
z3 = "ssh teme z3/bin/z3 -si -smt2 MODEL=true"

