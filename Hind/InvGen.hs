{-# LANGUAGE RankNTypes, ExistentialQuantification,
PatternGuards,TypeFamilies,FlexibleInstances, StandaloneDeriving,
ScopedTypeVariables, TransformListComp, ParallelListComp, NoMonomorphismRestriction #-}
module Hind.InvGen where

import Hind.Constants
import Hind.Parser(HindFile(..))
import Hind.Interaction
import Hind.PathCompression
import Hind.Chan
import Hind.ConnectionPool
import Hind.Utils

import Language.SMTLIB

import qualified Data.Set as S
import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Concurrent(forkIO,newEmptyMVar,ThreadId)
import Control.Concurrent.MVar

import Data.List(intercalate,find, sort,sortBy, groupBy,nub,intersect,(\\))
import Data.Maybe(fromJust,fromMaybe)
import System.Log.Logger


import qualified Data.Map as M
import qualified Data.Set as S

-- data POVal = NoInv

type Model = [(Identifier,Term)]

class InvGen a where
  -- | Construct a candidate from a system description
  fromSystem :: HindFile -> a
  fromSystem sys
     = let states = fromMaybe [] $ lookup (typeName (undefined :: a)) (hindStates sys)
           locals = fromMaybe [] $ lookup (typeName (undefined :: a)) (hindLocals sys)
       in fromStates (states ++ locals)


  -- | Construct a candidate given a list of states
  fromStates :: [Identifier] -> a

  -- | Return the name of this type as an SMT identifier
  typeName :: a -> Sort

  -- | Return the equivalence relation
  equal :: a -> String

  -- | Return the ordering relation
  ord :: a -> String

  -- | Return a list of all of the state variables
  vars :: a -> [Identifier]
  vars x = concat $ classes x

  -- | Return the partition
  classes :: a -> [[Identifier]]

  -- | Return the ordered chains. These aren't actually chains,
  -- they're just ordered pairs. FIXME: rename this.
  chains :: a -> [(Identifier,Identifier)]

  -- Given a model, refine the candidate.
  refine :: a -> Model -> a
  refine x _ = x

  -- Tracking/Changing whether a candidate has been refined
  resetRefined :: a -> a
  isRefined :: a -> Bool


-- | Print out a candidate
showState c = show ([cls | cls <- classes c, length cls > 1]) ++ "\n" ++
              unlines (map  connect (chains c))
  where connect (a,b) = show a ++  ord c ++ show b

-- | Generate a term representing the candidate. It will have the
-- form (and (= (a time) (b time)) (= (a time) (c time))
--  (< (a time) (c time)) for the state [[a,b],[c]]
toTerm st time = and $
       concatMap eqclass (classes st) ++ map ords (chains st)
    where
      eq = binop (equal st)
      lt = binop (ord st)
      and [] = true
      and [a] = a
      and props = Term_qual_identifier_ (Qual_identifier (Identifier "and")) props

      var x = Term_qual_identifier_ (Qual_identifier x) [time]
      binop op a b  = Term_qual_identifier_ (Qual_identifier (Identifier op))
                 [a,b]
      eqclass [] = []
      eqclass [c] = []
      eqclass (c:cs) = [eq (var c) (var c') | c' <- cs]
      -- Create the implication graph for the set of states
      ords (a,b) = lt (var a) (var b)
      true = Term_qual_identifier (Qual_identifier (Identifier "true"))


-- Create a term, but change the subterm uninterpreted functions into
-- their corresponding definitions
toTermMap st termMap time = and $
       map cleanup $ concatMap eqclass (classes st) ++ map ords (chains st)
    where
      eq = binop (equal st)
      lt = binop (ord st)
      and [] = true
      and [a] = a
      and props = Term_qual_identifier_ (Qual_identifier (Identifier "and")) props

      var x = Term_qual_identifier_ (Qual_identifier x) [time]
      binop op a b  = Term_qual_identifier_ (Qual_identifier (Identifier op))
                 [a,b]
      eqclass [] = []
      eqclass [c] = []
      eqclass (c:cs) = [eq (var' c) (var' c') | c' <- cs]
      -- Create the implication graph for the set of states
      ords (a,b) = lt (var' a) (var' b)
      true = Term_qual_identifier (Qual_identifier (Identifier "true"))
      var' v = case find (isTerm v) termMap of
        Just (_,_,tm) -> tm
        Nothing -> var v
      isTerm v (_,n,_) = v == n


mkDef st termMap prevIdx =
  Define_fun (invName (idx+1))
    [Sorted_var "_M" intType] boolType augmented
  where body = toTermMap st termMap (Term_qual_identifier (Qual_identifier (Identifier "_M")))
        augmented
          | Just i <- prevIdx =
            binop "and" (Term_qual_identifier (Qual_identifier (Identifier (invName i))))
                         body
          | otherwise = body
        invName i = "___inv_"++show i
        idx = maybe 0 (+1) prevIdx

-- Dumb hack to make this easier to read.
prettierInvariant (Term_qual_identifier_ (Qual_identifier (Identifier "and")) args) =
  unlines $ map (showLustre 0 . asLustre) args



-- data BoolInvGen =
--   BoolInvGen [([Identifier])] [(Identifier,Identifier)] -- Equ. classes, chains.

data BoolInvGen = BoolInvGen [[Identifier]] PO Bool deriving (Eq)
instance Show BoolInvGen where
  show = showState

instance InvGen BoolInvGen where
  fromStates states = BoolInvGen [states] (initialSigma (S.fromList states)) False

  typeName _ = Sort_bool
  equal _ = "="
  ord _ = "implies"

  classes (BoolInvGen state _ _) = state
  -- chains (BoolInvGen state cs) = [] -- cs
  chains (BoolInvGen states po _) =
    [(from,to) | (from,tos) <- M.toList red,
                 to <- S.toList tos]

    where red = suc po'
          po' = M.mapMaybeWithKey f po
          f node edges
            | S.member node reps =
               Just $ S.filter (\next -> S.member next reps) edges
            | otherwise = Nothing
          reps = S.fromList $ map head states


  refine candidate@(BoolInvGen states po _) model = BoolInvGen states' po' True
    where model' = map getBool model :: [(Identifier,Bool)]
           -- [(n,v) | (n,Term_spec_constant (Spec_constant_numeral v)) <- model]
          states' = filter (not . null) $ concatMap nextNodes states
          po' = nextSigma po model'
          nextNodes eqclass =
            let raw = [(v,val) | v <- eqclass,
                       (v',val) <- model', v == v'
                      ]
                sorted = sortBy (\a b -> compare (snd a) (snd b)) raw
                grouped = map (map fst) $ groupBy (\a b -> snd a == snd b) sorted
            in grouped

          getBool (n,Term_spec_constant c) = error$ show  (n,c)
          getBool (n,Term_qual_identifier (Qual_identifier (Identifier i)))
            | i == "false" = (n,False)
            | i == "true" = (n,True)
            | otherwise = throw $ ProverException ("Can't get boolean value of " ++ i) []


  resetRefined (BoolInvGen a b _) = BoolInvGen a b False
  isRefined (BoolInvGen _ _ r) = r

data IntInvGen = IntInvGen [[Identifier]] PO Bool
instance Eq IntInvGen where
  a == b = (S.fromList (map S.fromList (classes a)) ==
           S.fromList (map S.fromList (classes b))) &&
           S.fromList (chains a) == S.fromList (chains b)

instance Show IntInvGen where
  show = showState


instance InvGen IntInvGen where
  fromStates states = IntInvGen [states] (initialSigma (S.fromList states)) False
  typeName _ = Sort_identifier (Identifier "Int")

  equal _ = "="
  ord _ = "<="
  classes (IntInvGen states _ _) = states
  chains (IntInvGen states po _) =
    [(from,to) | (from,tos) <- M.toList red,
                 to <- S.toList tos]

    where red = suc po'
          po' = M.mapMaybeWithKey f po
          f node edges
            | S.member node reps =
               Just $ S.filter (\next -> S.member next reps) edges
            | otherwise = Nothing
          reps = S.fromList $ map head states

  refine candidate@(IntInvGen states po _ ) model = IntInvGen states' po' True
    where model' =
           [(n,v) | (n,Term_spec_constant (Spec_constant_numeral v)) <- model]
          states' = filter (not . null) $ concatMap nextNodes states
          po' = nextSigma po model'
          nextNodes eqclass =
            let raw = [(v,val) | v <- eqclass,
                       (v',val) <- model', v == v'
                      ]
                sorted = sortBy (\a b -> compare (snd a) (snd b)) raw
                grouped = map (map fst) $ groupBy (\a b -> snd a == snd b) sorted
            in grouped

  resetRefined (IntInvGen a b _) = IntInvGen a b False
  isRefined (IntInvGen _ _ r) = r


-- Partial order insertion for traces.
-- We represent a partial order as a graph, from a node to _successor_
-- nodes. Note this representation gives uses irreflexive, transitive
-- closure of the partial order.
--
type PO = M.Map Identifier (S.Set Identifier)

-- | FIXME: Dont' use list comprehensions, use map/fold directly on
-- sets and maps.
initialSigma s = M.fromList [(k,S.delete k s) | k <- S.toList s]
nextSigma sig vals = M.mapWithKey f sig
  where f k v = S.filter (cmp k) v
        cmp a b = let Just av = lookup a vals
                      Just bv = lookup b vals
                  in av <= bv

-- i,j,k are Testing
i = initialSigma (S.fromList ["a","b","c","d"])
j = nextSigma i [("a",0),("b",1),("c",2),("d",3)]
k = nextSigma j [("a",0),("b",2),("c",1),("d",3)]

-- Calculate the transitive reduction of a PO structure. It's
-- critical that the graph be acyclic.
suc sigma = M.map f sigma
  where f v = v S.\\ getAll v
        getAll vals = S.unions $ S.toList $
                      S.map (\k -> M.findWithDefault S.empty k sigma) vals



-- invGenProcess :: InvGen a => a -> ConnectionPool -> HindFile -> Chan Term ->
--                   (ProverException -> IO ()) -> IO (ThreadId, IO ())
invGenProcess candidateType pool pathcompress hindFile invChan onError =
  withProverException pool "Hind.invGen" onError $ \p -> do
   infoM "Hind.invGen" "Started invariant generation"

   -- sendCommand p (Set_option (Produce_unsat_cores True))
   defineSystem hindFile p

   -- Subterm handling
   let (definitions,names) = gatherTerms hindFile
       relevant = [n | (ty,n,_) <- names, ty == typeName candidateType]
   mapM_ (sendCommand p) definitions

   let initialState = fromStates relevant  `asTypeOf` candidateType

   let transBase x = trans hindFile (int 0  `minusTerm` int x)
       transStep = trans hindFile . stepTime
       assert = assertTerm p
       subterms time =
         Term_qual_identifier_ (Qual_identifier (Identifier "___subterms___"))
                                [time]

   -- Iteratively check a candidate, and refine using a
   -- counterexample. We exit when we get a property
   -- that holds for step k and k+1 without refinement.
   let baseRefine candidate k = do
         mapM_ assert [transBase k' | k' <- [0..k]]
         -- assert (baseTimeIs k)
         -- Assert the subterm equalities.
         mapM_ assert [subterms (int 0 `minusTerm` int k') | k' <- [0..k]]
         baseRefine' False candidate k

       baseRefine' refined candidate k = do
         push 1 p -- Candidate Push
         let cterm = toTerm candidate (baseTime k)
         debugM "Hind.invGen.refineloop.base" ("Checking candidate (base " ++ show k ++ ")")
         debugM "Hind.invGen.refineloop.base" (showState candidate)

         assert $ notTerm (baseTimeIs k `impliesTerm` cterm)
         ok <- isUnsat p

         if ok
           then do
             debugM "Hind.invGen.refineloop.base" "Candidate passed."
             pop 1 p -- Candidate Pop
             return (candidate,k)
           else do
             model <- getValuation p (vars candidate) (baseTime k)
             pop 1 p -- Candidate Pop
             debugM "Hind.invGen.refineloop.base" "Refined Candidate"
             debugM "Hind.invGen.refineloop.base" $
               "Got counterexample:\n\t" ++ show (formatModel  model)
             let model' = refine candidate model
             baseRefine' True model' k

       stepRefine candidate k = do
         -- Assert the transition relation
         mapM_ assert [transStep i | i <- [0..k]]
         -- Assert the subterm equalities
         mapM_ assert [subterms (stepTime k') | k' <- [0..k]]
         -- Assert path compression
         when pathcompress $
           mapM_ (sendCommand p) [stateCharacteristic k' | k' <- [0..k]]


         stepRefine' candidate k

       stepRefine' candidate k = do
         push 1 p -- candidate push
         let cterm i = toTerm candidate (stepTime i)
         debugM "Hind.invGen.refineloop.step" "Checking candidate (step)"
         debugM "Hind.invGen.refineloop.step" (showState candidate)

         -- Assert the candidate induction hypotheses
         mapM_ assert [cterm i | i <- [1..k]]
         -- Assert the negation of the candidate
         assert (notTerm (cterm 0))
         ok <- isUnsat p
         if ok
           then do
             debugM "Hind.invGen.refineloop" "Found invariant:"
             debugM "Hind.invGen.refineloop" (showState candidate)
             pop 1 p -- candidate pop
             -- writeChan invChan cterm
             return candidate
           else do
             model <- getValuation p (vars candidate) (stepTime 0)
             pop 1 p
             debugM "Hind.invGen.refineloop.step" "Refined Candidate"
             stepRefine' (refine candidate model) k

       outerloop state k prev = do
         debugM "Hind.invGen.refineloop" $ "Checking for invariant at k " ++ show k
         push 1 p -- Context for base transition assertions
         (baseCandidate,baseK) <- baseRefine state k
         pop 1  p -- Close context  for base transition assertions

         debugM "Hind.invGen.refineloop.base" $ "Base process found candidate  " ++
           show (toTerm baseCandidate (baseTime baseK))

         push 1 p -- Context for step transition assertions
         invariant <- stepRefine (resetRefined baseCandidate) baseK
         pop 1 p

         let same = maybe False (== invariant) prev
         if same
           then debugM "Hind.invGen" "Same invariant"
           else do
           infoM "Hind.invGen" $ "Found invariant (" ++ show baseK ++ ")"
           debugM "Hind.invGen" $ show invariant
           -- debugM "Hind.invGen" $ show $ mkDef invariant names (Just k)
           writeChan invChan (toTermMap invariant names)



         if isRefined invariant
           then do
             outerloop (resetRefined baseCandidate) (baseK + 1) (Just invariant)
           else do
             -- If we didn't refine the step candidate, then we should
             -- just quit, because we've proven the baseCandidate
             -- invariant.
             noticeM "Hind.invGen.refineloop" $
                "Done with " ++ show (typeName invariant) ++  " refinement."
   outerloop initialState 0 Nothing

-- | This works for getting a valuation *from Z3*. The response is
-- parsed as a get-proof response, for whatever reason. This is a
-- colossal pain in the ass.
getValuation p vars time = do
  vals <- sendCommand p (Get_value [Term_qual_identifier_ (Qual_identifier v) [time] | v <- vars])
  -- infoM "Hind.invGen" ("Got Model:" ++ show vals)
  return (getVals vals)

getVals :: Command_response -> [(Identifier,Term)]
getVals (Gv_response vals) = [(n,val) | (Term_qual_identifier_ (Qual_identifier  n) _, val) <- vals]
getVals (Gp_response (S_exprs exprs)) = map val exprs
  where val (S_exprs [S_exprs [S_expr_symbol n,time],val]) = (Identifier n,sExprVal val)
        sExprVal (S_expr_constant c) = Term_spec_constant c
        sExprVal (S_expr_symbol s) = Term_qual_identifier (Qual_identifier (Identifier s))
        sExprVal (S_exprs [S_expr_symbol "-", S_expr_constant (Spec_constant_numeral x)]) =
            Term_spec_constant (Spec_constant_numeral (-x))
        sExprVal s = error $ "sExprVal not defined for " ++ show s

-- | Nicer formatting of a counterexample.
formatModel model = zip (map (snd . head) grouped) (map (map fst) grouped)
  where sorted = sortBy (\x y -> compare (snd x)  (snd y))  model
        grouped = groupBy (\x y -> snd x ==  snd y) sorted


type InvFun = Term->Term
data Invariant = NoInvariant (Chan InvFun)
               | Inv Int InvFun (Chan InvFun)

getInvariant (NoInvariant c) = do
  empty <- isEmptyChan c
  if empty
    then return (False,NoInvariant c)
    else do
    fun <- readChan c
    return (True, Inv 0 fun c)
getInvariant inv@(Inv i def c) = do
  empty <- isEmptyChan c
  if empty
    then return (False,inv)
    else do
    fun <- readChan c
    return (True, Inv (i+1) fun c)



defineInvariant p (NoInvariant _) = return ()
defineInvariant p (Inv i fun _) = do
  -- Create the define-fun
  sendCommand p def
  return ()

  where def = Define_fun (invName i)
               [Sorted_var "_M" intType] boolType augmented
        body = fun m
        augmented
          | i > 0 =
            binop "and"
              (Term_qual_identifier_ (Qual_identifier (Identifier (invName (i-1)))) [m])
              body
          | otherwise = body
        m = Term_qual_identifier (Qual_identifier (Identifier "_M"))
invName i = "___inv_"++show i

assertInvariant p (NoInvariant _) time = return ()
assertInvariant p (Inv i _ _) time = do
  sendCommand p
    (Assert (Term_qual_identifier_ (Qual_identifier (Identifier (invName i))) [time]))
  return ()


deriving instance Eq Term
deriving instance Eq Spec_constant
deriving instance Eq Attribute
deriving instance Eq Qual_identifier
deriving instance Eq Var_binding
deriving instance Eq Sorted_var
deriving instance Eq S_expr
deriving instance Ord Term
deriving instance Ord Spec_constant
deriving instance Ord Attribute
deriving instance Ord Qual_identifier
deriving instance Ord Var_binding
deriving instance Ord Sorted_var
deriving instance Ord S_expr


-- This is code for generating a bunch of definitions for all of the
-- subterms of a system, so that we have more elements to work with
-- when generating the candidate invariants.
gatherTerms sys = (decls  ++ [define],names)
  where Script cmds = hindScript sys
        states = hindStates sys
        locals = hindLocals sys
        terms = [(ty,n,findTerm n cmds) |
                 (ty,ns) <- states ++ locals,
                 n <- ns]
        subterms = nub $ [(ty,sub) | (ty,_,Just tm) <- terms,
                          (ty,sub) <- flatten ty tm]
        subterm i = "_s" ++ show i
        decls = [Declare_fun (subterm i)
                 [intType] ty | (ty,_) <- subterms | i <- [0..]]
        define = Define_fun "___subterms___"
                 [Sorted_var "_M" intType] boolType
                 (Term_qual_identifier_ (Qual_identifier (Identifier "and"))
                  [equalTerm (Term_qual_identifier_
                              (Qual_identifier (Identifier (subterm i)))
                              [Term_qual_identifier (Qual_identifier (Identifier "_M"))]) tm
                  |(_,tm) <- subterms
                  | i <- [0..]])
        names = [(ty,Identifier $ subterm i,sub) | (ty,sub) <- subterms | i <- [0..]]

findTerm (Identifier name) = fmap g . find f
  where f (Define_fun _ [_] sort
          (Term_qual_identifier_ (Qual_identifier (Identifier "="))
           [Term_qual_identifier_ (Qual_identifier (Identifier var))
            [Term_qual_identifier (Qual_identifier (Identifier "_M"))],
            term])) = var == name
        f _ = False
        g (Define_fun _ [_] sort
          (Term_qual_identifier_ (Qual_identifier (Identifier "="))
           [Term_qual_identifier_ (Qual_identifier (Identifier var))
            [Term_qual_identifier (Qual_identifier (Identifier "_M"))],
            term])) = term

-- subTerms (Define_fun _ [_] sort
--           (Term_qual_identifier_ (Qual_identifier (Identifier "="))
--            [Term_qual_identifier_ (Qual_identifier (Identifier var))
--             [Term_qual_identifier (Qual_identifier (Identifier "_M"))],
--             term])) = [(var,nub $ flatten term)]
-- subTerms _ = []

boolType = Sort_bool
intType = Sort_identifier (Identifier "Int")
flatten ty tm@(Term_qual_identifier_ (Qual_identifier (Identifier "ite"))
            [pred,t,e]) = (ty,tm):(boolType,pred):(flatten ty t ++ flatten ty e)

flatten ty tm@(Term_qual_identifier_ (Qual_identifier (Identifier ">="))
            [x,y]) = (boolType,tm):(flatten intType x ++ flatten intType y)
flatten ty tm@(Term_qual_identifier_ (Qual_identifier (Identifier "<="))
            [x,y]) = (boolType,tm):(flatten intType x ++ flatten intType y)
flatten ty tm@(Term_qual_identifier_ (Qual_identifier (Identifier ">"))
            [x,y]) = (boolType,tm):(flatten intType x ++ flatten intType y)
flatten ty tm@(Term_qual_identifier_ (Qual_identifier (Identifier "<"))
            [x,y]) = (boolType,tm):(flatten intType x ++ flatten intType y)
flatten ty tm@(Term_qual_identifier_ (Qual_identifier (Identifier "and"))
            [x,y]) = (boolType,tm):(flatten boolType x ++ flatten boolType y)
flatten ty tm@(Term_qual_identifier_ (Qual_identifier (Identifier "or"))
            [x,y]) = (boolType,tm):(flatten boolType x ++ flatten boolType y)

flatten ty tm@(Term_qual_identifier_ (Qual_identifier (Identifier "+"))
            [x,y]) = (ty,tm):(flatten ty x ++ flatten ty y)
flatten ty tm@(Term_qual_identifier_ (Qual_identifier (Identifier "-"))
            [x,y]) = (ty,tm):(flatten ty x ++ flatten ty y)
flatten ty tm = [(ty,tm)]


mkDefine j term =
  Define_fun ("def_inv_term_" ++ show j)
  [Sorted_var "_M" (Sort_identifier (Identifier "Int"))] Sort_bool
  (Term_qual_identifier_ (Qual_identifier (Identifier "="))
   [Term_qual_identifier_ (Qual_identifier (Identifier ("inv_term_" ++ show j)))
    [Term_qual_identifier (Qual_identifier (Identifier "_M"))],
    term])

--isTrue (Term_qual_identifier (Qual_identifier (Identifier "true"))) = True

-- Make the output more readable...
cleanup (Term_qual_identifier_ (Qual_identifier (Identifier "=")) [a,b]) =
            case (cleanup a,cleanup b) of
              (Term_qual_identifier (Qual_identifier (Identifier "true")),
               b') -> b'
              (a',Term_qual_identifier (Qual_identifier (Identifier "true"))) -> a'
              (a',b') -> (Term_qual_identifier_ (Qual_identifier (Identifier "=")) [a',b'])

cleanup (Term_qual_identifier_ (Qual_identifier (Identifier "and")) (a:bs)) =
            case (cleanup a,map cleanup bs) of
               (Term_qual_identifier_ (Qual_identifier (Identifier "and")) args,bs') ->
                cleanup (Term_qual_identifier_ (Qual_identifier (Identifier "and"))
                         (args ++ bs'))
               (a',bs') -> (Term_qual_identifier_ (Qual_identifier (Identifier "and"))
                            (a':bs'))

cleanup (Term_qual_identifier_ (Qual_identifier (Identifier "or")) (a:bs)) =
            case (cleanup a,map cleanup bs) of
               (Term_qual_identifier_ (Qual_identifier (Identifier "or")) args,bs') ->
                cleanup (Term_qual_identifier_ (Qual_identifier (Identifier "or"))
                         (args ++ bs'))
               (a',bs') -> (Term_qual_identifier_ (Qual_identifier (Identifier "or"))
                           (a':bs'))

cleanup (Term_qual_identifier_ op args) = Term_qual_identifier_ op (map cleanup args)

cleanup t = t


-- These two rules give a lustre-like syntax.
asLustre (Term_qual_identifier_ (Qual_identifier id)
         [Term_qual_identifier (Qual_identifier (Identifier "_M"))]) =
  Term_qual_identifier (Qual_identifier id)
asLustre (Term_qual_identifier_ (Qual_identifier id)
         [Term_qual_identifier_ (Qual_identifier (Identifier "-"))
          [Term_qual_identifier (Qual_identifier (Identifier "_M")),
           Term_spec_constant (Spec_constant_numeral 1)]]) =
  Term_qual_identifier_ (Qual_identifier (Identifier "pre"))
    [Term_qual_identifier (Qual_identifier id)]

asLustre (Term_qual_identifier_ (Qual_identifier (Identifier "ite"))
         [Term_qual_identifier_ (Qual_identifier (Identifier "="))
          [Term_qual_identifier (Qual_identifier (Identifier "_M")),
           Term_qual_identifier (Qual_identifier (Identifier "_base"))],
          t,e]) = Term_qual_identifier_ (Qual_identifier (Identifier "->"))
                  [asLustre t,asLustre e]

asLustre (Term_qual_identifier_ (Qual_identifier id) args) =
  (Term_qual_identifier_ (Qual_identifier id) (map asLustre args))

asLustre t = t


showLustre prec t@(Term_qual_identifier_ (Qual_identifier (Identifier "and")) args) =
  parens prec (getPrec "and") $
    intercalate " and " $ map (showLustre (getPrec "and")) args

showLustre prec t@(Term_qual_identifier_ (Qual_identifier (Identifier "or")) args) =
  parens prec (getPrec "or") $ intercalate " or " $ map (showLustre prec) args

showLustre prec t@(Term_qual_identifier_ (Qual_identifier (Identifier "->")) args) =
  parens prec (getPrec "->") $ intercalate " -> " $ map (showLustre prec) args


showLustre prec t@(Term_qual_identifier_ (Qual_identifier (Identifier op)) [a,b])
  | op `elem` ["implies", "=","+",">=","<=",">","<","->"] =
    parens prec (getPrec op) $
      showLustre (getPrec op) a ++ " " ++ op ++ " " ++ showLustre (getPrec op) b
  | otherwise = show t

showLustre prec t = show t

precs = [("implies",5),
         ("-",5),("+",5),
         ("=",4),(">=",4),("<=",4),(">",4),("<",4),
         ("and",4), ("or",3), ("->",3)
        ]

getPrec op = fromJust $ lookup op precs

parens parent child term
  | child > parent = term
  | otherwise = "(" ++ term ++ ")"
