module Language.KansasLava.Verification.YicesConvert where



import Text.Regex
import Data.List
import Control.Applicative



convertFile fname = do
   f <- readFile fname
   let matches = map matchLine $ lines f


   let states = [declareState name ty | Just (State [name,ty]) <- matches]
   let steps = [declareStep name var body | Just (Step [name,var,body]) <- matches]
   let trans = "(define-fun trans (step Int) (and " ++
               unwords ["(" ++ name ++ " step)" | Just (Step [name,_,_]) <- matches]
               ++ ")"
   putStrLn $ unlines $ states ++ steps ++ [trans]
   return ()


declareState name ty =
  "(declare-fun " ++ name ++ " (Int) " ++ toType ty ++ ")"
  where toType "bool" = "Bool"
        toType "int" = "Int"

declareStep name svar body =
  "(define-fun " ++ name ++ " (" ++ svar ++ " Int) Bool " ++
  body ++ ")"


data Value = Step [String]
           | State [String]
           deriving Show



matchLine l =
  (State <$> matchRegex defineRegex l) <|>
  (Step <$> matchRegex stepRegex l)

defineRegex = mkRegex "\\(define ([_a-z0-9]+)::\\(-> _nat ([a-z]+)\\)\\)"

stepRegex = mkRegex $ "\\(define ([_A-Za-z0-9]+)::\\(-> _nat bool\\) " ++
                      "\\(lambda \\( ([_A-Za-z0-9]+)::_nat\\)" ++
                      "(.*)\\)\\)"




testSV = "(define ___z3z___::(-> _nat bool))"
testStep = "(define DEF__103::(-> _nat bool) (lambda ( _M::_nat) (= (___z3z___ _M) (= (___z4z___ _M) (___z5z___ _M)))))"


