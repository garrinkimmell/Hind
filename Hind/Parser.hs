{-# LANGUAGE TransformListComp, StandaloneDeriving, FlexibleContexts, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Hind.Parser where

import Text.ParserCombinators.Poly
import Language.SMTLIB
import Data.List(find)
import Data.Maybe
import Control.Monad.Error


data HindFile = HindFile { hindProperties :: [Identifier]
                         , hindInputs :: [Identifier]
                         , hindOutputs :: [Identifier]
                         , hindStates :: [(Sort,[Identifier])]
                         , hindTransition :: Identifier
                         , hindScript :: Script
                         } deriving Show

hindFile f = do
  str <- readFile f
  case runParser' hind (lexSMTLIB str) >>= processScript of
    (Left err) -> do
               fail err
    (Right res) -> do
               return res

hind :: Parser Token  Script
hind = script


runParser' p inp = case runParser p inp of
                    (Left err, _) -> throwError err
                    (Right res,[]) -> return res
                    (Right _,_) ->
                      throwError "Parse Error: Didn't consume all input"

deriving instance Eq Identifier
deriving instance Ord Identifier
deriving instance Eq Sort
deriving instance Ord Sort


-- Convert a smt script to a HindFile
processScript :: MonadError String m => Script -> m HindFile
processScript scr@(Script cmds) = do
  trans <- getTransition cmds
  states <- getStates cmds
  properties <- getProperties cmds
  inputs <- getInputs cmds
  outputs <- getOutputs cmds
  let groupedStates = [(head ty,n)  | (ty,n) <- states,
                        then group by ty]
  return $
         HindFile properties inputs outputs groupedStates trans
                    (Script (filterInfos cmds))


getTransition cmds = do
   (Set_info (Attribute_s_expr _ (S_expr_symbol s))) <- getInfo ":transition" cmds
   return (Identifier s)

getStates cmds = do
  (Set_info (Attribute_s_expr _ (S_exprs ss))) <- getInfo ":states" cmds
  return $ getTypes cmds [s | S_expr_symbol s <- ss]

getProperties cmds = do
   (Set_info (Attribute_s_expr _ (S_exprs ss))) <- getInfo ":properties" cmds
   return [Identifier s | S_expr_symbol s <- ss]

getInputs cmds = do
   (Set_info (Attribute_s_expr _ (S_exprs ss))) <- getInfo ":inputs" cmds
   return [Identifier s | S_expr_symbol s <- ss]

getOutputs cmds = do
   (Set_info (Attribute_s_expr _ (S_exprs ss))) <- getInfo ":outputs" cmds
   return [Identifier s | S_expr_symbol s <- ss]




getInfo nm cmds = maybe err return (find isInfo cmds)
  where isInfo (Set_info (Attribute_s_expr attr  _)) =  nm == attr
        isInfo _ = False
        err = throwError $  "Could not find info  " ++ nm



getTypes cmds ids = catMaybes $ map idRange cmds
  where idRange (Declare_fun nm _ ran)
          | nm `elem` ids = Just (ran, Identifier nm)
          | otherwise = Nothing
        idRange _ = Nothing


filterInfos = filter (not . hindInfo)
  where hindInfo (Set_info (Attribute_s_expr attr  _)) =
          attr `elem` [":states",":transition",":properties", ":inputs", ":outputs"]
        hindInfo _ = False


toScript :: HindFile -> Script
toScript hf = Script $ [transInfo,statesInfo,propInfo,inputInfo,outputInfo] ++ cmds
  where Script cmds = hindScript hf
        transInfo =
           Set_info (Attribute_s_expr ":transition"
                     (S_expr_symbol trans))
        Identifier trans = hindTransition hf
        statesInfo =
           Set_info (Attribute_s_expr ":states"
                     (S_exprs
                      [S_expr_symbol nm | (_,ss) <- (hindStates hf),
                       Identifier nm <- ss]))
        propInfo =
           Set_info (Attribute_s_expr ":properties"
                     (S_exprs
                      [S_expr_symbol nm | Identifier nm <- (hindProperties hf)]))

        inputInfo =
           Set_info (Attribute_s_expr ":inputs"
                     (S_exprs
                      [S_expr_symbol nm | Identifier nm <- (hindInputs hf)]))

        outputInfo =
           Set_info (Attribute_s_expr ":outputs"
                     (S_exprs
                      [S_expr_symbol nm | Identifier nm <- (hindOutputs hf)]))



