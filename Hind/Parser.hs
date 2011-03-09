module Hind.Parser where

import Text.ParserCombinators.Poly
import Language.SMTLIB



data HindFile = HindFile { hindProperties :: [Identifier]
                         , hindStates :: [Identifier]
                         , hindTransition :: Identifier
                         , hindScript :: Script
                         } deriving Show

hindFile f = do
  str <- readFile f
  case runParser hind (lexSMTLIB str) of
    (Left err, _) -> do
               putStrLn $ "Parse Error"
               fail err
    (Right res, []) -> do
               return res
    (Right res, _) -> do
               fail $ "Parse Error: Didn't consume all input"


hind = do
  left
  tok $ Symbol "properties"
  ps <- many1 identifier
  right

  left
  tok $ Symbol "state"
  states <- many1 identifier
  right

  left
  tok $ Symbol "transition"
  trans <- identifier
  right

  def <- script

  return $ HindFile { hindProperties = ps
                    , hindStates = states
                    , hindTransition = trans
                    , hindScript = def
                    }