{-# LANGUAGE TransformListComp, StandaloneDeriving, FlexibleContexts, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses,DeriveDataTypeable, PackageImports #-}
module Hind.Parser where

import Language.SMTLIB
import Data.List(find)
import Data.Maybe
import "monads-fd" Control.Monad.Error
import Control.Exception
import Data.Typeable
import GHC.Exts(the,groupWith)


data HindFile = HindFile { hindProperties :: [Identifier]
                         , hindInputs :: [Identifier]
                         , hindOutputs :: [Identifier]
                         , hindStates :: [(Sort,[Identifier])]
                         , hindLocals :: [(Sort,[Identifier])]
                         , hindTransition :: Identifier
                         , hindCoverage :: [Identifier]
                         , hindScript :: Script
                         } deriving Show

hindFile f = do
  scr <- parseScriptFile f
  case scr >>= processScript of
    (Left err) -> do
               fail err
    (Right res) -> do
               return res

data ParseException = ParseException String deriving (Eq,Typeable)
instance Show ParseException where
  show (ParseException str) = str



deriving instance Eq Identifier
deriving instance Ord Identifier
deriving instance Eq Sort
deriving instance Ord Sort


-- Convert a smt script to a HindFile
processScript :: MonadError String m => Script -> m HindFile
processScript scr@(Script cmds) = do
  trans <- getTransition cmds
  states <- getStates cmds
  locals <- getLocals cmds
  properties <- getProperties cmds
  inputs <- getInputs cmds
  outputs <- getOutputs cmds
  coverage <- getCoverage cmds
  let groupedStates = [(head ty,n)  | (ty,n) <- states, then group by ty using groupWith ]
  let groupedLocals = [(head ty,n)  | (ty,n) <- locals, then group by ty using groupWith ]


  return $
         HindFile properties inputs outputs groupedStates groupedLocals trans coverage
                    (Script (filterInfos cmds))


getTransition cmds = do
   (Set_info (Attribute_s_expr _ (S_expr_symbol s))) <- getInfo ":transition" cmds
   return (Identifier s)

getStates cmds = do
  (Set_info (Attribute_s_expr _ (S_exprs ss))) <- getInfo ":states" cmds
  return $ getTypes cmds [s | S_expr_symbol s <- ss]

getLocals cmds = do
  (Set_info (Attribute_s_expr _ (S_exprs ss))) <- getInfo ":locals" cmds
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

getCoverage cmds = do
   (Set_info (Attribute_s_expr _ (S_exprs ss))) <- getInfo ":coverage" cmds
   return [Identifier s | S_expr_symbol s <- ss]
  `catchError` (\_ -> return [])



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
          attr `elem` [":states",":transition",":properties", ":inputs", ":outputs",":coverage",":locals"]
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
