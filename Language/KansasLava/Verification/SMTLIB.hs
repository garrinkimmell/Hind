{-# LANGUAGE StandaloneDeriving, PatternGuards #-}
-- | Generate smt-lib models for Lava circuits
module Language.KansasLava.Verification.SMTLIB
  (smtCircuit, writeSMTCircuit) where


import Language.KansasLava
import Language.SMTLIB hiding (Name)
-- import qualified Language.SMTLIB as SMT

import Data.Graph
import Data.List(find)

-- | smtCircuit generates an SMT Script that models the transition behavior of
-- the input reified circuit.
smtCircuit :: Circuit -> Script
smtCircuit circ = script
  where stmts = mkDecls sorted
        script = Script (options ++ timeVar ++ stmts ++ trans)
        sorted = sortCirc circ
        options = [] -- [Set_logic "QF_AUFBVNIA"]
                   -- , Set_info (Attribute_s_expr "smt-lib-version"
                   --              (S_expr_constant (Spec_constant_string "2.0")))]
        timeVar = [Declare_fun "n" [] nat,
                   Assert (Term_qual_identifier_ (Qual_identifier (Identifier ">="))
                                                   [Term_qual_identifier (Qual_identifier (Identifier "n"))
                                                   ,Term_spec_constant (Spec_constant_numeral 0)])
                  ]


        trans = mkTrans "v" circ


-- | writeSMTCircuit takes a Lava circuit, reifies it, and writes the SMTLib format to the given file name.
writeSMTCircuit :: (Ports a) => a -> FilePath -> IO ()
writeSMTCircuit circ outFile = do
  rc <- reifyCircuit circ
  let script = smtCircuit rc
  print script
  writeFile outFile (show script)

  return () -- rc

-- | sortCircuit does a topological sort of the circuit, which insures that all
-- driver occur before the driven.
sortCirc :: Circuit -> Circuit
sortCirc rc = rc { theCircuit = circ }
  where (gr,info,_) =
          graphFromEdges [(n,nodeId, drivers n) | (nodeId,n) <- theCircuit rc]
        sorted = topSort (transposeG gr)
        circ = [(k,n) | (n,k,_) <- map info sorted]
        drivers (Entity _ _ is _) = [i | (_,_,Port _ i) <- is]


-- * Translation from Lava to SMTLib

-- mkDecls :: Circuit -> [Command]
mkDecls :: Circuit -> [Command]
mkDecls circ = concatMap (mkInput "v") (theSrcs circ) ++
               concatMap (declareEntity "v") (theCircuit circ) ++
               map (declareOutput "v") (theSinks circ) ++
               concatMap (defineEntity "v") (theCircuit circ) ++
               map (defineOutput "v") (theSinks circ)


mkTrans prefix circ =
  [Define_fun "trans" [Sorted_var "step" nat] Sort_bool
              conjunct]
  where ts =
          [curStep (var ("trans-" ++ (entName prefix nodeid port))) |
           (nodeid,ent@(Entity name ports _ _)) <- theCircuit circ,
          (port,ty) <- ports, okName name]
        os = [curStep (var ("trans-" ++ n)) | (OVar _ n, ty,_) <- theSinks circ]

        conjunct = Term_qual_identifier_ (Qual_identifier (Identifier "and"))
                   (ts ++ os)
        okName (Prim "Env") = False
        okName _ = True


mkInput :: String -> (OVar, Type) -> [Command]
mkInput _ (_,ClkTy) = []
mkInput _ (_,ClkDomTy) = []
mkInput _ (OVar _ n,ty) = [Declare_fun n [nat] (smtType ty)]


declareOutput prefix (OVar _ n, ty, _) =
  Declare_fun n [nat] (smtType ty)

defineOutput :: (Show t) => [Char] -> (OVar, Type, Driver t) -> Command
defineOutput prefix (OVar _ n, ty, driver) =
  Define_fun ("trans-" ++ n) [Sorted_var "step" nat] Sort_bool
               (fn .== curStep (smtDriver prefix ty driver))
    where fn = Term_qual_identifier_ (Qual_identifier (Identifier n))
                  [Term_qual_identifier (Qual_identifier (Identifier "step"))]


declareEntity _ (_,Entity (Prim "Env") _ _ _) = [] -- Filter out 'Envs'
declareEntity prefix (nodeid,ent@(Entity _ outs _ _)) =
  [Declare_fun (entName prefix nodeid port) [nat] (smtType ty) | (port,ty) <- outs]


defineEntity :: (Show t, Show t1, Show t2) =>
     [Char] -> (t, Entity Type t2 t1) -> [Command]
defineEntity _ (_,Entity (Prim "Env") _ _ _) = [] -- Filter out 'Envs'
defineEntity prefix (nodeid, (Entity (Prim "register") [(port,ty)] [("def",defTy,defDriver), ("i0",iTy,idriver), _] [])) =
    [Define_fun ("trans-" ++ (entName prefix nodeid port))
               [(Sorted_var "step" nat)] Sort_bool  (fn .== tm)]
  where fn = Term_qual_identifier_ (Qual_identifier (Identifier (entName prefix nodeid port)))
               [Term_qual_identifier (Qual_identifier (Identifier "step"))]
        tm = (ifThenElse (var "step" .== (num 0)) (smtDriver prefix defTy defDriver) (prevStep (smtDriver prefix iTy idriver)))

  -- [Define_fun (entName prefix nodeid port) [Sorted_var "step" nat] (smtType ty)
  --               (ifThenElse (var "step" .== (num 0)) (smtDriver prefix defTy defDriver) (prevStep (smtDriver prefix iTy idriver)))]


defineEntity prefix (nodeid,ent@(Entity _ outs _ _)) =
  -- [Assert (Term_forall [(Sorted_var "step" nat)] (fn port .== tm))
  --   | (port,ty) <- outs]
  [Define_fun ("trans-" ++ entName prefix nodeid port)
   [Sorted_var "step" nat] Sort_bool
     (fn port .== (smtEnt prefix nodeid ent))  | (port,ty) <- outs]
  where fn port = Term_qual_identifier_ (Qual_identifier (Identifier (entName prefix nodeid port)))
                  [Term_qual_identifier (Qual_identifier (Identifier "step"))]
        tm = (smtEnt prefix nodeid ent)




-- Convert an entity into a name
entName :: (Show a) => [Char] -> a -> [Char] -> [Char]
entName prefix nodeid "o0" =  prefix ++ show nodeid
entName prefix nodeid out =  prefix ++ show nodeid ++"_" ++ out

-- Convert a driver into a term
smtDriver :: (Show t) => [Char] -> Type -> Driver t -> Term
smtDriver prefix _ (Port name d) = var $ entName prefix d name
smtDriver _ _ (Pad (OVar _ n)) = var n
smtDriver _ _ (ClkDom dom) = var dom
smtDriver _ B (Lit (RepValue [WireVal True])) = var "true"
smtDriver _  B (Lit (RepValue [WireVal False])) = var "false"
-- FIXME: This is z3 specific syntax
-- smtDriver _ (U s) (Lit (RepValue vals)) = Term_qual_identifier (Qual_identifier (Identifier vstr))
--   where vstr = "bvbin" ++ (bv vals) ++ "[" ++ show s ++ "]"
-- smtDriver _ (S s) (Lit (RepValue vals)) = Term_qual_identifier (Qual_identifier (Identifier vstr))
--   where vstr = "bvbin" ++ (bv vals) ++ "[" ++ show s ++ "]"

smtDriver _ _ (Lit (RepValue vals)) = Term_spec_constant $ Spec_constant_binary (reverse $ bools vals)
  where bools [] = []
        bools ((WireVal v):vs) = v:(bools vs)
        bools (WireUnknown:_) =
          error "smtDriver: Can't generate a lit with unknown values"

smtDriver _ _ driver = error $ "smtDriver: " ++ show driver

bv [] = []
bv ((WireVal True):ws) = '1':(bv ws)
bv ((WireVal False):ws) = '0':(bv ws)
bv _ = error "Can't print unknown wire value"





smtEnt
  :: (Show t1, Show t2) => [Char] -> t -> Entity Type t2 t1 -> Term
smtEnt prefix _ (Entity nm [(_,os)] [("i0", ity0, d0), ("i1", ity1, d1),("i2",ity2,d2)] _)
  | Just operator <- lookupOp nm [ity0,ity1,ity2,os] ternOps =
           operator (smtDriver prefix ity0 d0) (smtDriver prefix ity1 d1) (smtDriver prefix ity2 d2)

smtEnt prefix _ (Entity nm [(_,os)] [("i0", ity0, d0), ("i1", ity1, d1)] _)
  | Just operator <- lookupOp nm [ity0,ity1,os] binOps =
           (smtDriver prefix ity0 d0) `operator` (smtDriver prefix ity1 d1)
smtEnt prefix _ (Entity nm [(_,os)] [("i0", ity0, d0)] _)
  | Just operator <- lookupOp nm [ity0,os] unOps = operator (smtDriver prefix ity0 d0)



smtEnt prefix _ (Entity (Label _) [(_,_)] [(_, ity, d0)] _) =
   curStep (smtDriver prefix ity d0)

smtEnt _ _ e = error $  "smtEnt: unhandled case" ++ show e


ternOps :: [(Id,[Type]->Bool, Term -> Term -> Term -> Term)]
ternOps = [(Name "Lava" "mux2", muxType, ite)]
  where ite a b c = Term_qual_identifier_
                      (Qual_identifier (Identifier "ite"))
                      [curStep a, curStep b, curStep c]

binOps :: [(Id, [Type] -> Bool, Term -> Term -> Term)]
binOps = [(Name "Lava" "and2", boolBin,bop "and"),
          (Name "Lava" "or2", boolBin, bop "or"),
          (Name "Lava" "xor2", boolBin, bop "xor"),
          (Name "Lava" ".==.", boolBin, bop "="),
          (Name "Lava" "+", signedBin, bop "bvadd"),
          (Name "Lava" "+", unsignedBin, bop "bvadd"),
          (Name "Lava" ".>=.", signedComp, bop "bvsge"),
          (Name "Lava" ".>=.", unsignedComp, bop "bvuge"),
          (Name "Lava" ".<.", signedComp, bop "bvslt"),
          (Name "Lava" ".<.", unsignedComp, bop "bvult")


         ]
  where bop i x y =
          Term_qual_identifier_
            (Qual_identifier (Identifier i))
              [curStep x, curStep y]

unOps :: [(Id, [Type] -> Bool, Term -> Term)]
unOps = [(Name "Lava" "not", boolUnary, uop "not")]
  where uop _ x =
          Term_qual_identifier_ (Qual_identifier (Identifier "not"))
                                  [curStep x]

lookupOp :: Id -> [Type] -> [(Id, [Type] -> Bool, a)] -> Maybe a
lookupOp n ty table =
  maybe Nothing getName (find (\(m,p,_) -> m == n && p ty) table)
  where getName (_,_,name) = Just name


boolUnary :: [Type] -> Bool
boolUnary [B,B] = True
boolUnary _ = False

boolBin :: [Type] -> Bool
boolBin [B,B,B] = True
boolBin _ = False

signedBin :: [Type] -> Bool
signedBin [(S x),(S y),(S z)] = x == y && y == z
signedBin _ = False

unsignedBin :: [Type] -> Bool
unsignedBin [(U x),(U y),(U z)] = x == y && y == z
unsignedBin _ = False

signedComp :: [Type] -> Bool
signedComp [(S x),(S y),B] = x == y
signedComp _ = False

unsignedComp :: [Type] -> Bool
unsignedComp [(U x),(U y),B] = x == y
unsignedComp _ = False


muxType :: [Type] -> Bool
muxType [B,a,b,c] = a == b && b == c
muxType _ = False



-- | Get the driver at the current step
curStep :: Term -> Term
curStep t@(Term_qual_identifier q@(Qual_identifier (Identifier nm)))
         | nm `elem` special = t
         | otherwise = (Term_qual_identifier_ q [var "step"])
   where special = ["true","false"]

curStep t@(Term_spec_constant _) = t
curStep i = error $ "curstep" ++ show i

-- | Get the driver from the previous step
prevStep :: Term -> Term
prevStep  (Term_qual_identifier q) =
  Term_qual_identifier_ q [Term_qual_identifier_ (Qual_identifier (Identifier "-")) [var "step", num 1]]
prevStep i = error $ "prevStep" ++ show i




-- | Map Lava types to SMTLib sorts
smtType :: Type -> Sort
smtType B = Sort_bool

-- Not sure why I can't put an Int there, but the SMTLIB grammar doesn't provide for that.
smtType (S s) =
  (Sort_identifiers (Identifier "_")
   [Sort_identifier (Identifier "BitVec"),
    Sort_identifier (Identifier (show s))])
smtType (U s) =
  (Sort_identifiers (Identifier "_")
   [Sort_identifier (Identifier "BitVec"),
    Sort_identifier (Identifier (show s))])

smtType ClkDomTy = (Sort_identifier (Identifier "ClockDomain"))
smtType ty = error $ "smtType: " ++ show ty



nat :: Sort
nat = Sort_identifier (Identifier "Int")


-- SMTLib utilities are below

(.==) :: Term -> Term -> Term
a .== b = Term_qual_identifier_ (Qual_identifier (Identifier "=")) [a,b]

var :: Symbol -> Term
var = Term_qual_identifier . Qual_identifier . Identifier

num :: Numeral -> Term
num = Term_spec_constant . Spec_constant_numeral

ifThenElse :: Term -> Term -> Term -> Term
ifThenElse p t e = Term_qual_identifier_ (Qual_identifier (Identifier "ite")) [p,t,e]

