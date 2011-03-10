{-# LANGUAGE TransformListComp, StandaloneDeriving #-}
module Hind.Parser where

import Text.ParserCombinators.Poly
import Language.SMTLIB



data HindFile = HindFile { hindProperties :: [Identifier]
                         , hindStates :: [(Sort,[Identifier])]
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
  tok $ Symbol "transition"
  trans <- identifier
  right

  def <- script


  return $ HindFile { hindProperties = ps
                    , hindStates = genStates def
                    , hindTransition = trans
                    , hindScript = def
                    }




-- | Extract the state variables from the model. This is a placeholder, and eventually this
-- should perhaps use attributes.
genStates :: Script -> [(Sort, [Identifier])]
genStates (Script scr)
  = [(head res,map Identifier n) |
      Declare_fun n [_] res <- scr,
      then group by res]


deriving instance Eq Identifier
deriving instance Ord Identifier
deriving instance Eq Sort
deriving instance Ord Sort