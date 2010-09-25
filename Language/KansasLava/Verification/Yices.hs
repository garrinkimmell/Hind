{-# LANGUAGE PatternGuards #-}
module Language.KansasLava.Verification.Yices where

import Language.KansasLava
import Math.SMT.Yices.Syntax
import Math.SMT.Yices.Pipe

import Data.Graph
import Control.Monad
import Data.List(find)

import Data.Sized.Unsigned

yicesCircuit :: Ports a =>  a -> Int  -> IO YicesIPC
yicesCircuit circ iter = do
  ipc <- createYicesPipe "yices" []
  rc <- reifyCircuit circ
  res <- mapM (\iter -> mkDecls "p0" iter ipc (sortCirc rc)) [0..iter]
  status <- runCmdsY ipc [STATUS]
  print status
  return ipc




-- | Generate yices declarations from the reified circuit
-- mkDecls :: String -> Int -> YicesIPC -> a -> IO ()
mkDecls prefix iter ipc rc = do
  let inps = concatMap (yPadDecl prefix iter) (theSrcs rc)
  putStrLn "Inputs"
  mapM print inps
  let cmds = concatMap (yEntDecl prefix iter) (theCircuit rc)
  putStrLn "Transition"
  mapM print cmds
  let outs = map (yPadOutput prefix iter) (theSinks rc)
  putStrLn "Outputs"
  print outs
  runCmdsY ipc $ inps ++ cmds ++ outs


-- | Create a Yices variable name.
toYicesName :: String -> Int -> String -> Int -> String
toYicesName prefix iter name idx =
  prefix ++ "__" ++ show iter ++ "__" ++ name ++ "__" ++ show idx

-- | Generate the declarations for the input pads.
yPadDecl prefix iter (OVar idx name, ClkTy) = []
yPadDecl prefix iter (OVar idx name, ty) =
  [DEFINE (toYicesName prefix iter name idx, ytyp ty) Nothing]
yPadDecl _ _ n = error $ "ypd" ++ show n


yPadOutput prefix iter (OVar idx name, ty, driver) =
  DEFINE (toYicesName prefix iter name 0, ytyp ty) (Just (yExpDriver prefix iter driver))

-- | Generate the declaration for a single entity
yEntDecl prefix iter  (nodeid,ent@(Entity nm outs ins _)) =
  [DEFINE (toYicesName prefix iter port nodeid,ytyp oty) (Just $ yexp nodeid prefix iter ent)
   | (port, oty) <- outs]
yEntDecl _ _ (_,ent) = error $ show ent


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
yexp nodeid prefix iter (Entity nm [(o,os)] [("i0", ity0, d0), ("i1", ity1, d1)] _)
  | Just op <- lookup nm binOps = yExpDriver prefix iter d0 `op` yExpDriver prefix iter d1
yexp nodeid prefix iter (Entity nm [(o,oty)] [(_, ity, d0)] _)
  | Just op <- lookup nm unOps = op $ yExpDriver prefix iter d0
yexp nodeid prefix iter (Entity nm [(o,oty)] [(i0,_,d0),(i1,_,d1),(i2,_,d2)] [])
  | Just op <- lookup nm ternOps =
               op (yExpDriver prefix iter d0)
                  (yExpDriver prefix iter d1)
                  (yExpDriver prefix iter d2)

yexp nodeid prefix iter (Entity (Name "Memory" "register") [(o,oty)]
                  (("def",dty,ddriver):
                   ("i0",ity, idriver):
                   ("rst",_,rdriver):
                   ("en",enty,edriver):_) _)
    | iter == 0 = rstExp
    | otherwise = IF (yExpDriver prefix iter rdriver)
                    rstExp
                    (IF (yExpDriver prefix iter edriver)
                        nextExp prevExp)
  where rstExp = yExpDriver prefix iter ddriver
        prevExp = yExpDriver prefix (iter-1) (Port o nodeid)
        nextExp = yExpDriver prefix iter idriver


yexp _ _ _ ent@(Entity nm outs ins _) = error $ "yexp:" ++ show ent

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
        ,(Name "Lava" "not", NOT)]

ternOps = [(Name "Lava" "mux2", IF)]

-- | Map Lava drivers to yices exprs
yExpDriver prefix iter (Port n id) = VarE $ toYicesName prefix iter n id
yExpDriver prefix iter (Pad (OVar idx name)) = VarE $ toYicesName prefix iter name idx
yExpDriver prefix iter l@(Lit x) = LitI (read $ show x)




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


-- equivCheck :: (Ports a) => a -> a -> IO Bool
equivCheck c1 c2 = do
  ipc <- createYicesPipe "yices" []
  rc1 <- reifyCircuit c1
  rc2 <- reifyCircuit c2

  putStrLn "Circuit 1:"
  print $ theCircuit rc1

  putStrLn "Circuit 2:"
  print $ theCircuit rc2

  res1 <- mkDecls "c0" 0 ipc (sortCirc rc1)
  res2 <- mkDecls "c1" 0 ipc (sortCirc rc2)


  -- For each output, assert that they're different
  let outAssertions = zipWith neqOutput (theSinks rc1) (theSinks rc2)
  -- For each output, assert that they're the same
  let inAssertions = zipWith eqInput (theSrcs rc1) (theSrcs rc2)
  runCmdsY' ipc (inAssertions ++ outAssertions)
  res <- checkY ipc
  case res of
    Sat core -> do
             putStrLn "Not equivalent"
             putStrLn "SAT Model"
             print core
             return False
    UnSat _ -> do
             putStrLn "Equivalent"
             return True

  where neqOutput (o1,_,_) (o2,_,_) =
          ASSERT ((outputName "c0" o1)  :/= (outputName "c1") o2)
        outputName prefix  (OVar idx name) =
          VarE $ toYicesName prefix 0 name idx

        eqInput (i1,_) (i2,_) =
          ASSERT ((inputName "c0" i1)  := (inputName "c1") i2)
        inputName prefix  (OVar idx name) =
          VarE $ toYicesName prefix 0 name idx


c1,c2 :: Seq Bool -> Seq Bool -> Seq Bool
c1 = and2
c2 = or2


c3 env i  = (output "value" reg,output "property" prop)
  where reg = register env false i
        prop = or2 reg (bitNot reg)


c1' a b = (output "value" c, output "property" (or2 c (bitNot c)))
  where c = c1 a b

bounded circ k = do
  ipc <- createYicesPipe "yices" []
  rc <- reifyCircuit circ
  let sorted = sortCirc rc
  -- putStrLn $ "Circuit: "
  -- print sorted

  -- Generate the transisiton system
  res <- mapM (\iter -> mkDecls "bmc" iter ipc sorted) [0..k]
  status <- runCmdsY ipc [STATUS]
  flushY ipc

  -- Check each base case
  res <- case find (\(OVar _ name,_,_) -> name == "property") (theSinks rc) of
           Nothing -> fail "No property found"
           Just (ovar,_,driver) -> do
                   putStrLn "Asserting Base Cases"
                   let assertions = [ASSERT (NOT (yExpDriver "bmc" i driver)) | i <- [0..k]]
                   mapM print assertions
                   runCmdsY ipc assertions
                   checkY ipc
  baseCheck <- case res of
                 UnSat _ -> return True
                 InCon _ -> return True
                 Sat maxsat -> do
                   putStrLn "Base Case Violating Model"
                   print maxsat
                   return False

  unless baseCheck $ fail "Base step failed"
  putStrLn "Base Step succeeded"


  putStrLn "Checking LoopFree"
  loopFree "bmc" k rc

  exitY ipc
  return ()


loopFree prefix k rc = do
    let asserts = pw chk [0..k]
    print asserts
  where pw f [] = []
        pw f (i:is) = map (f i) is ++ pw f is
        chk i j = sameState prefix i j rc


sameState prefix i j rc =
    [ASSERT (var i idx o  :/= var j idx o) |
     (idx,Entity (Name "Memory" "register") [(o,oty)] _ _) <- theCircuit rc]
  where var iter idx o = VarE $ toYicesName prefix iter o idx


