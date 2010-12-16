module Main where

import Hind.KInduction

import Text.Printf
import Control.Exception
import System.CPUTime
import System.Environment
import Language.SMTLIB

time :: IO t -> IO t
time a = do
    start <- getCPUTime
    v <- a
    end   <- getCPUTime
    let diff = (fromIntegral (end - start)) / (10^12)
    printf "Computation time: %0.6f sec\n" (diff :: Double)
    return v

main = do
  args <- getArgs
  case args of
    [proverCmd, modelFile, property] ->
      do cnts <- readFile modelFile
         putStrLn "Working..."
         let scr@(Script model) = parseScript cnts
         putStrLn $ show scr
         putStrLn "Parallel Check"
         time $ sequence_ $ replicate 1 $ parCheck proverCmd model property
         putStrLn "Sequential Check"
         time $ sequence_ $ replicate 1 $ seqCheck proverCmd model property

         return ()

    _ -> putStrLn "usage: hind <prover command> <model file> <property>"


z3 :: [Char]
z3 = "ssh teme z3/bin/z3 -si -smt2 MODEL=true"

