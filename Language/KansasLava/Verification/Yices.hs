module Language.KansasLava.Verification.Yices where

import Language.KansasLava
import Math.SMT.Yices.Syntax
import Math.SMT.Yices.Pipe

import Data.Graph


import Data.Sized.Unsigned

yicesCircuit :: Ports a => [ReifyOptions] -> a -> IO YicesIPC
yicesCircuit opts circ = do
  ipc <- createYicesPipe "yices" []
  rc <- reifyCircuit opts circ
  res <- mkDecls ipc (sortCirc rc)
  return ipc



-- | Generate yices declarations from the reified circuit
mkDecls ipc rc = do
  let inps = map yPadDecl (theSrcs rc)
  let cmds = concatMap yEntDecl (theCircuit rc)
  mapM print  cmds
  runCmdsY ipc $ inps ++ cmds


-- | Generate the declarations for the input pads.
yPadDecl (PadVar idx name, ty) = DEFINE (name ++ "__" ++ show idx, ytyp ty) Nothing


-- | Generate the declaration for a single entity
yEntDecl (id,ent@(Entity nm outs ins _)) =
  [DEFINE (show port ++ "__" ++ show id,ytyp oty) (Just $ yexp ent)
   | (port, oty) <- outs]
yEntDecl (_,ent) = error $ show ent


test :: Comb Int -> Comb Int -> Comb Int
test x y = x + 1 + y

-- | Map Lava types to Yices types
ytyp B = VarT "bool"
ytyp CB = VarT "controlbit"
ytyp (S 32) = VarT $ "int"
ytyp ClkTy = VarT "bool"
ytyp RstTy = VarT "bool"
ytyp (TupleTy tys) = TUP (map ytyp tys)
ytyp ty = error $ "ytyp: Non-handled Lava type " ++ show ty
-- ytyp (U x) = VarT $ "(unsigned" ++ show x ++ ")"
-- ytyp (S x) = VarT $ "(signed" ++ show x ++ ")"



-- | Map Lava expressions (entities, actually) to Yices exprs
yexp (Entity nm [(o,os)] [(Var "i0", ity0, d0), (Var "i1", ity1, d1)] _)
  | Just op <- lookup nm binOps = yExpDriver d0 `op` yExpDriver d1
yexp (Entity nm [(o,oty)] [(_, ity, d0)] _)
  | Just op <- lookup nm unOps = op $ yExpDriver d0
yexp (Entity nm [(o,oty)] [(i0,_,d0),(i1,_,d1),(i2,_,d2)] [])
  | Just op <- lookup nm ternOps =
               op (yExpDriver d0) (yExpDriver d1) (yExpDriver d2)
yexp ent@(Entity nm outs ins _) = error $ "yexp:" ++ show ent

binOps = [(Name "Int" "+", (:+:))
         ,(Name "Bool" "and2", (\x y -> AND [x, y]))
         ,(Name "Unsigned" ".>.", (:>))
         ,(Name "Int" ".>.", (:>))
         ,(Name "Lava" "pair", \x y -> MKTUP [x,y])

         ]
unOps = [(Name "Lava" "fst", \t -> SELECT_T t 0)
        ,(Name "Lava" "snd", \t -> SELECT_T t 1)
        ,(Name "Lava" "id", id)]

ternOps = [(Name "Lava" "mux2", IF)]

-- | Map Lava drivers to yices exprs
yExpDriver (Port (Var n) id) = VarE $ n ++ "__" ++ show id
yExpDriver (Pad (PadVar idx name)) = VarE $ name ++ "__" ++ show idx
yExpDriver (Lit x) = LitI (toInteger x)




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


