module Main where

import Language.KansasLava.Verification.KInduction
import Language.KansasLava

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

    _ -> putStrLn "usage: a.out <prover command> <model file> <property>"

{-

    putStrLn "Starting Parallel..."
    time $ (checkCircuitPar z3 (prop_toggle_vs_puls 2)  "aprop")
    putStrLn "Done."
    putStrLn "Starting Sequential..."
    time $ (checkCircuit z3 (prop_toggle_vs_puls 2)  "aprop")
    putStrLn "Done."
-}


z3 :: [Char]
z3 = "ssh teme z3/bin/z3 -si -smt2 MODEL=true"
toggle :: Seq Bool -> Seq Bool
toggle change = out
  where out' = register low out
        out = xor2 change out'

delayN 0 init inp = inp
delayN n init inp = out
  where out = register init rest
        rest = delayN (n-1) init inp

puls n = out
  where out = delayN (n-1) low last
        last = register high out

prop_toggle_vs_puls :: Int -> (Seq Bool, Seq Bool, Seq Bool)
prop_toggle_vs_puls n = (out1, out2, output "aprop" ok)
  where
    out1 = toggle high
    out2 = puls n
    ok = (bitNot (out1 .==. out2))
    -- ok = bitNot high
