module Main where

import Hind(
       HindOpts,getOptions,file, getSMTCmd, -- options
       hindFile, -- parser
       setupLogger, getLogFile, logLevel, -- logging
       parCheck,Result, -- K-induction
       ConnectionPool, newConnectionPool, closePool
       )

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
import System.FilePath(takeExtension, (</>))

import Control.Concurrent(forkIO)



{-
import Criterion.Main (defaultMain, bench)
import Criterion.Config
-}
time :: IO t -> IO (Double,Double,t) -- cpu time, wall time, result
time a = do
    wallStart <- getCurrentTime
    start <- getCPUTime
    v <- a
    end   <- getCPUTime
    wallEnd <- getCurrentTime
    let diff = (fromIntegral (end - start)) / (10^12)
        wallDiff = ((fromRational $toRational $ diffUTCTime wallEnd wallStart) :: Double)
    -- Note: The CPUTime is meaningless if we're running on a remote server.
    noticeM "Hind" $ printf "Computation time: %0.6f sec" (diff :: Double)
    noticeM "Hind" $ printf "Wall time: %0.6f sec" wallDiff

    return (diff,wallDiff,v)

main = do
  options <- getOptions
  setupLogger (getLogFile options)  options
  let cmd = (getSMTCmd options)
  debugM "Hind" $ "Using smt command " ++ cmd
  pool <- newConnectionPool (getSMTCmd options) 5
  files <- getFiles options
  mapM_ (checkFile pool) files


checkFile :: ConnectionPool -> HindOpts -> IO (Maybe Result)
checkFile pool options = handle handler $ do
    noticeM "Hind" ("Checking file " ++ (file options))
    parsed <- hindFile (file options)
    noticeM "Hind" "Parsed file successfully"
    -- pool <- newConnectionPool (getSMTCmd options) 5
    (cpu,wall,res) <- time $ parCheck pool options parsed
    noticeM "Hind.summary" $ printf "%s,%s,%0.6f,%0.6f" (show res) (file options) cpu wall
    -- closePool pool
    return (Just res)
  where handler :: SomeException -> IO (Maybe Result)
        handler e = do
          noticeM "Hind.summary" $
            printf "%s failed with error:%s\n" (file options) (show e)
          return Nothing

getFiles :: HindOpts -> IO [HindOpts]
getFiles opts = do
  isDirectory <- doesDirectoryExist (file opts)
  if isDirectory
    then do
      infoM "Hind" $ printf "Checking directory %s" (file opts)
      contents <- getDirectoryContents (file opts)
      return [opts { file = file opts </> f } | f <- contents, takeExtension f == ".smt2"]
    else return [opts]



z3 :: [Char]
z3 = "ssh teme z3/bin/z3 -si -smt2 MODEL=true"

