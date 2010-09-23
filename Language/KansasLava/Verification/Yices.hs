{-# LANGUAGE PatternGuards #-}
module Language.KansasLava.Verification.Yices where

import Language.KansasLava
import Math.SMT.Yices.Syntax
import Math.SMT.Yices.Pipe

import Data.Graph
import Control.Monad

import Data.Sized.Unsigned

yicesCircuit :: Ports a =>  a -> IO YicesIPC
yicesCircuit circ = do
  ipc <- createYicesPipe "yices" []
  rc <- reifyCircuit circ
  res <- mkDecls "p0" ipc (sortCirc rc)
  status <- runCmdsY ipc [STATUS]
  print status
  return ipc



-- | Generate yices declarations from the reified circuit
mkDecls prefix ipc rc = do
  let inps = map (yPadDecl prefix) (theSrcs rc)
  -- print inps
  let cmds = concatMap (yEntDecl prefix) (theCircuit rc)
  -- print cmds
  let outs = map (yPadOutput prefix) (theSinks rc)
  -- print outs
  runCmdsY ipc $ inps ++ cmds ++ outs


-- | Generate the declarations for the input pads.

yPadDecl prefix (OVar idx name, ty) =
  DEFINE (prefix ++ name ++ "__" ++ show idx, ytyp ty) Nothing
yPadDecl _ n = error $ "ypd" ++ show n


yPadOutput prefix (OVar idx name, ty, driver) =
  DEFINE (prefix ++ name, ytyp ty) (Just (yExpDriver prefix driver))

-- | Generate the declaration for a single entity
yEntDecl prefix  (id,ent@(Entity nm outs ins _)) =
  [DEFINE (prefix ++ port ++ "__" ++ show id,ytyp oty) (Just $ yexp prefix ent)
   | (port, oty) <- outs]
yEntDecl _ (_,ent) = error $ show ent


test :: Comb Int -> Comb Int -> Comb Int
test x y = x + 1 + y

-- | Map Lava types to Yices types
ytyp B = VarT "bool"
-- ytyp CB = VarT "controlbit"
ytyp (S 32) = VarT $ "int"
-- ytyp ClkTy = VarT "bool"
-- ytyp RstTy = VarT "bool"
ytyp (TupleTy tys) = TUP (map ytyp tys)
ytyp ty = error $ "ytyp: Non-handled Lava type " ++ show ty
-- ytyp (U x) = VarT $ "(unsigned" ++ show x ++ ")"
-- ytyp (S x) = VarT $ "(signed" ++ show x ++ ")"



-- | Map Lava expressions (entities, actually) to Yices exprs
yexp prefix (Entity nm [(o,os)] [("i0", ity0, d0), ("i1", ity1, d1)] _)
  | Just op <- lookup nm binOps = yExpDriver prefix d0 `op` yExpDriver prefix  d1
yexp prefix (Entity nm [(o,oty)] [(_, ity, d0)] _)
  | Just op <- lookup nm unOps = op $ yExpDriver prefix d0
yexp prefix (Entity nm [(o,oty)] [(i0,_,d0),(i1,_,d1),(i2,_,d2)] [])
  | Just op <- lookup nm ternOps =
               op (yExpDriver prefix d0) (yExpDriver prefix  d1) (yExpDriver prefix d2)
yexp _  ent@(Entity nm outs ins _) = error $ "yexp:" ++ show ent

binOps = [(Name "Int" "+", (:+:))
         ,(Name "Lava" "and2", (\x y -> AND [x, y]))
         ,(Name "Lava" "or2", (\x y -> OR [x, y]))
         ,(Name "Unsigned" ".>.", (:>))
         ,(Name "Int" ".>.", (:>))
         ,(Name "Lava" "pair", \x y -> MKTUP [x,y])

         ]
unOps = [(Name "Lava" "fst", \t -> SELECT_T t 0)
        ,(Name "Lava" "snd", \t -> SELECT_T t 1)
        ,(Name "Lava" "id", id)
        ,(Name "Bool" "not", NOT)]

ternOps = [(Name "Lava" "mux2", IF)]

-- | Map Lava drivers to yices exprs
yExpDriver prefix (Port n id) = VarE $ prefix ++ n ++ "__" ++ show id
yExpDriver prefix (Pad (OVar idx name)) = VarE $ prefix ++ name ++ "__" ++ show idx
-- yExpDriver (Lit x) = LitI (toInteger x)




-- * We have to generate decls in sorted order for yices.


-- import Data.Graph
drivers (Entity _ _ is _) = [i | (_,_,Port _ i) <- is]
drivers (Table _ _ _) = error "Lava.Yices.drivers: table not handled"


-- | do a topological sort on the circuit, so that declarations can be generated
--  in the correct order for yices.
sortCirc rc = rc { theCircuit = circ }
  where (gr,info,vlookup) = graphFromEdges [(n,id, drivers n) | (id,n) <- theCircuit rc]
        sorted = topSort (transposeG gr)
        circ = [(k,n) | (n,k,_) <- map info sorted]



exclusive ipc a b = do
  runCmdsY' ipc [PUSH,ASSERT (a := b)]
  res <- checkY ipc
  runCmdsY ipc [POP]
  case res of
    UnSat _ -> return Nothing
    InCon _ -> return Nothing
    s -> return $ Just s


equivCheck c1 c2 = do
  ipc <- createYicesPipe "yices" []
  rc1 <- reifyCircuit c1
  rc2 <- reifyCircuit c2

  unless (length (theSinks rc1) == length (theSinks rc2)) $
         fail "Circuits don't have the same number of outputs"

  unless (length (theSrcs rc1) == length (theSrcs rc2)) $
         fail "Circuits don't have the same number of inputs"

  res1 <- mkDecls "c0__" ipc (sortCirc rc1)
  res2 <- mkDecls "c1__" ipc (sortCirc rc2)

  -- For each output, assert that they're different
  let outAssertions = zipWith neqOutput (theSinks rc1) (theSinks rc2)
  -- For each output, assert that they're the same
  let inAssertions = zipWith eqInput (theSrcs rc1) (theSrcs rc2)
  runCmdsY' ipc (inAssertions ++ outAssertions)
  res <- checkY ipc
  case res of
    Sat core -> do
             putStrLn "Not equivalent"
             putStrLn "SAT Core"
             print core
             return False
    UnSat _ -> do
             putStrLn "Equivalent"
             return True

  where neqOutput (o1,_,_) (o2,_,_) =
          ASSERT ((outputName "c0__" o1)  :/= (outputName "c1__") o2)
        outputName prefix  (OVar idx name) =
          VarE $ prefix ++ name

        eqInput (i1,_) (i2,_) =
          ASSERT ((inputName "c0__" i1)  := (inputName "c1__") i2)
        inputName prefix  (OVar idx name) =
          VarE $ prefix ++ name ++ "__" ++ show idx


c1,c2 :: Seq Bool -> Seq Bool -> Seq Bool
c1 = and2
c2 = or2