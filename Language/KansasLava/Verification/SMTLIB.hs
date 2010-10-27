{-# LANGUAGE StandaloneDeriving, PatternGuards #-}
-- | Generate smt-lib models for Lava circuits
module Language.KansasLava.Verification.SMTLIB
  (smtCircuit, writeSMTCircuit) where


import Language.KansasLava
import Language.SMTLIB hiding (Name)
import qualified Language.SMTLIB as SMT

import Data.Graph
import Data.List(find)

-- For testing
import Data.Sized.Signed

-- | smtCircuit generates an SMT Script that models the transition behavior of
-- the input reified circuit.
smtCircuit :: Circuit -> Script
smtCircuit circ = script
  where stmts = mkDecls sorted
        script = Script (options ++ stmts)
        sorted = sortCirc circ
        options = [Set_logic "QF_BV",
                   Set_info (Attribute_s_expr "smt-lib-version"
                             (S_expr_constant (Spec_constant_string "2.0")))]


-- | writeSMTCircuit takes a Lava circuit, reifies it, and writes the SMTLib format to the given file name.
writeSMTCircuit circ outFile = do
  rc <- reifyCircuit circ
  let script = smtCircuit rc
  writeFile outFile (show script)

  return () -- rc

-- | sortCircuit does a topological sort of the circuit, which insures that all
-- driver occur before the driven.
sortCirc rc = rc { theCircuit = circ }
  where (gr,info,vlookup) = graphFromEdges [(n,id, drivers n) | (id,n) <- theCircuit rc]
        sorted = topSort (transposeG gr)
        circ = [(k,n) | (n,k,_) <- map info sorted]
        drivers (Entity _ _ is _) = [i | (_,_,Port _ i) <- is]


-- * Translation from Lava to SMTLib

-- mkDecls :: Circuit -> [Command]
mkDecls circ = concatMap (mkInput "v") (theSrcs circ) ++
               concatMap (defineEntity "v") (theCircuit circ) ++
               map (mkOutput "v") (theSinks circ)


mkInput prefix (_,ClkTy) = []
mkInput prefix (_,ClkDomTy) = []

mkInput prefix (OVar idx n,ty) = [Declare_fun n [nat] (smtType ty)]

mkOutput prefix (OVar idx n, ty, driver) =
  Define_fun n [Sorted_var "step" nat] (smtType ty) (curStep (smtDriver prefix ty driver))


defineEntity _ (_,Entity (Prim "Env") _ _ _) = [] -- Filter out 'Envs'
defineEntity prefix (nodeid, (Entity (Prim "register") [(port,ty)] [("def",defTy,defDriver), ("i0",iTy,idriver), env] [])) =
  [Define_fun (entName prefix nodeid port) [Sorted_var "step" nat] (smtType ty)
                (ifThenElse (var "step" .== 0) (smtDriver prefix defTy defDriver) (prevStep (smtDriver prefix iTy idriver)))]


defineEntity prefix (nodeid,ent@(Entity nm outs ins _)) =
  [Define_fun (entName prefix nodeid port) [Sorted_var "step" nat] (smtType ty) (smtEnt prefix nodeid ent)
   | (port,ty) <- outs]



-- Convert an entity into a name
entName prefix nodeid "o0" =  prefix ++ show nodeid
entName prefix nodeid out =  prefix ++ show nodeid ++"_" ++ out

-- Convert a driver into a term
smtDriver prefix _ (Port name d) = var $ entName prefix d name
smtDriver prefix _ (Pad (OVar idx n)) = var n
smtDriver prefix _ (ClkDom dom) = var dom
smtDriver prefix B l@(Lit (RepValue [WireVal True])) = var "true"
smtDriver _  B l@(Lit (RepValue [WireVal False])) = var "false"
smtDriver _ _ (Lit (RepValue vals)) = Term_spec_constant $ Spec_constant_binary (bools vals)
  where bools [] = []
        bools ((WireVal v):vs) = v:(bools vs)
        bools (WireUnknown:_) =
          error "smtDriver: Can't generate a lit with unknown values"


smtDriver prefix _ driver = error $ "smtDriver: " ++ show driver


smtEnt prefix nodeid (Entity nm [(o,os)] [("i0", ity0, d0), ("i1", ity1, d1)] _)
  | Just op <- lookupOp nm [ity0,ity1,os] binOps =
               (smtDriver prefix ity0 d0) `op` (smtDriver prefix ity1 d1)

smtEnt prefix nodeid (Entity nm [(o,os)] [("i0", ity0, d0)] _)
  | Just op <- lookupOp nm [ity0,os] unOps = op (smtDriver prefix ity0 d0)

smtEnt prefix nodeid (Entity (Label l) [(o,oty)] [(_, ity, d0)] _) =
   curStep (smtDriver prefix ity d0)

smtEnt _ _ e = error $  "smtEnt: unhandled case" ++ show e

showId (Name a b) = "name " ++ a ++ b
showId (Prim s) = "prim " ++ s
showId (External _) = "external"
showId (ClockId _) = "clockid"


binOps = [(Name "Lava" "and2", boolBin,bop "and"),
          (Name "Lava" "or2", boolBin, bop "or"),
          (Name "Lava" "+", signedBin, bop "bvsadd"),
          (Name "Lava" "+", unsignedBin, bop "bvuadd"),
          (Name "Lava" ".>=.", signedComp, bop "bvuge")
         ]
  where bop i x y =
          Term_qual_identifier_
            (Qual_identifier (Identifier i))
              [curStep x, curStep y]

unOps = [(Name "Lava" "not", boolUnary, uop "not")]
  where uop i x =
          Term_qual_identifier_ (Qual_identifier (Identifier "not"))
                                  [curStep x]

lookupOp :: Id -> [Type] -> [(Id, [Type] -> Bool, a)] -> Maybe a
lookupOp n ty table = maybe Nothing op (find (\(m,p,_) -> m == n && p ty) table)
  where op (_,_,op) = Just op


boolUnary [B,B] = True
boolUnary _ = False

boolBin [B,B,B] = True
boolBin _ = False

signedBin [(S x),(S y),(S z)] = z == y && y == z
signedBin _ = False

unsignedBin [(U x),(U y),(U z)] = z == y && y == z
unsignedBin _ = False

signedComp [(S x),(S y),B] = x == y
signedComp _ = False
unsignedComp [(U x),(U y),B] = x == y
unsignedComp _ = False



-- | Get the driver at the current step
curStep (Term_qual_identifier q) = (Term_qual_identifier_ q [var "step"])
curStep t@(Term_spec_constant _) = t
curStep i = error $ "curstep" ++ show i

-- | Get the driver from the previous step
prevStep  (Term_qual_identifier q) = Term_qual_identifier_ q [Term_qual_identifier_ (Qual_identifier (Identifier "-")) [var "step", 1]]




-- | Map Lava types to SMTLib sorts
smtType B = Sort_bool
-- Not sure why I can't put an Int there, but the SMTLIB grammar doesn't provide for that.
smtType (S s) =
  (Sort_identifiers (Identifier "BitVec")
   [Sort_identifier (Identifier (show s))])
smtType ClkDomTy = (Sort_identifier (Identifier "ClockDomain"))
smtType ty = error $ "smtType: " ++ show ty
nat = Sort_identifier (Identifier "Int")



-- Test circuits
c1' a b = (c, output "aprop" (and2 c (bitNot c)))
  where c = c1 a b
c1 :: Seq Bool -> Seq Bool -> Seq Bool
c1 = and2


c3 :: Seq Bool -> (Seq Bool, Seq Bool)
c3 i  = (output "value" reg,output "property" prop)
  where reg = register false i
        prop = and2 reg (bitNot reg)


c4 :: Seq S10 -> (Seq S10, Seq Bool)
c4 i  = (output "value" reg,output "property" prop)
  where reg = register 0 i
        prop = (reg .>=. 0 )



-- SMTLib utilities are below


instance Eq Term

a .== b = Term_qual_identifier_ (Qual_identifier (Identifier "=")) [a,b]
var = Term_qual_identifier . Qual_identifier . Identifier

ap = Term_qual_identifier_

ifThenElse p t e = Term_qual_identifier_ (Qual_identifier (Identifier "ite")) [p,t,e]


instance Num Term where
  fromInteger = Term_spec_constant . Spec_constant_numeral
  (+) = error "(+) is undefined for Term"
  (*) = error "(*) is undefined for Term"
  abs = error "abs is undefined for Term"
  signum = error "signum is undefined for Term"



