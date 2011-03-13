module Main where


import Hind.Parser
import Hind.Interaction
import Hind.Logging

import Language.SMTLIB

import System.Environment
import System.IO
import Control.Exception
import Data.Either

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fname,level] -> do
      setupLogger fname level
      res <- hindFile fname
      vecHandle <- openFile (fname ++ ".vectors") WriteMode
      coverage res vecHandle

    _ -> putStrLn "usage: covgen <fname>"



coverage file vecFile = do
  bracket (makeProverNamed proverCmd "Hind.Coverage") closeProver $ \prover -> do
    sendScript prover (hindScript file)

    let loop k [] = do
          noticeM "Hind.Coverage" "No branches left to check"

        loop k active
          | k > 100 =
            errorM "Hind.Coverage" "Exceeded trace depth"
          | otherwise = do
             sendCommand prover (Assert (trans k))
             res <- mapM (checkCov file prover k) active
             let (failed,passed) = partitionEithers res
             -- noticeM "Hind.coverage" "Passed"
             mapM (hPutStrLn vecFile . show) passed

             loop  (k+1) failed

    loop 0 [(c,b) | c <- hindCoverage file, b <- [True,False]]
    return ()
  where trans k =
          Term_qual_identifier_
          (Qual_identifier (hindTransition file))
           [Term_spec_constant (Spec_constant_numeral k)]


checkCov :: HindFile -> Prover -> Integer -> (Identifier,Bool) ->
            IO (Either (Identifier,Bool) TestVector)
checkCov file prover k cp@((Identifier id),b) = do
  push 1 prover
  sendCommand prover (Assert covDis)
  res <- isSat prover
  if res
     then do
       m <- fetchTrace file prover k
       pop 1 prover
       return (Right (TestVector id b m))
     else pop 1 prover >> return (Left cp)

  where covDis = Term_qual_identifier_
                 (Qual_identifier (Identifier "or"))
                  [neg $ Term_qual_identifier_
                         (Qual_identifier (Identifier id))
                         [(Term_spec_constant (Spec_constant_numeral i))]
                   | i <- [0..k]]

        -- negate the term
        neg t
            | b = t
            | otherwise =
              Term_qual_identifier_ (Qual_identifier (Identifier "not")) [t]



fetchTrace file prover k = do
    mapM inpTrace (hindInputs file)
  where inpExprs inp = [Term_qual_identifier_ (Qual_identifier inp)
                        [Term_spec_constant (Spec_constant_numeral i)]
                        | i <- [0..k]]
        inpTrace inp = do
          vals <- sendCommand prover (Get_value (inpExprs inp))
          case vals of
            Ga_response vec -> return (Trace inp vec)
            r -> fail $ show r



proverCmd  = "ssh teme z3/bin/z3 -si -smt2 MODEL=true"

data Trace = Trace Identifier [Term] deriving Show
--type Trace = (Identifier,[Term])
data TestVector = TestVector String Bool [Trace] deriving Show
