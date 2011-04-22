module Main where

import Hind(
       HindOpts,getOptions,file, getSMTCmd, -- options
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
import System.Directory(doesDirectoryExist,getDirectoryContents)
import System.FilePath(takeExtension)

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
    noticeM "Hind" $ printf "Computation time: %0.6f sec" (diff :: Double)
    noticeM "Hind" $ printf "Wall time: %0.6f sec"
                 ((fromRational $toRational $ diffUTCTime wallEnd wallStart) :: Double)
    return v

main = do
  options <- getOptions
  setupLogger (getLogFile options) (logLevel options)
  debugM "Hind" $ "Using smt command " ++ (getSMTCmd options)
  files <- getFiles options
  mapM_ checkFile files


checkFile :: HindOpts -> IO Bool
checkFile options = handle handler $ do
    noticeM "Hind" ("Checking file " ++ (file options))
    parsed <- hindFile (file options)
    time $ parCheck options parsed
  where handler :: SomeException -> IO Bool
        handler e = do
          noticeM "Hind" $
            printf "%s failed with error:%s\n" (file options) (show e)
          return False

getFiles :: HindOpts -> IO [HindOpts]
getFiles opts = do
  isDirectory <- doesDirectoryExist (file opts)
  if isDirectory
    then do
      infoM "Hind" $ printf "Checking directory %s" (file opts)
      contents <- getDirectoryContents (file opts)
      return [opts { file = f } | f <- contents, takeExtension f == ".smt2"]
    else return [opts]



z3 :: [Char]
z3 = "ssh teme z3/bin/z3 -si -smt2 MODEL=true"

