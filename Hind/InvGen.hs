{-# LANGUAGE RankNTypes, ExistentialQuantification, PatternGuards,TypeFamilies,FlexibleInstances,
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

import Data.List(sort,sortBy, groupBy,nub,intersect,(\\))
import Data.Maybe(fromJust,fromMaybe)
import System.Log.Logger


import qualified Data.Map as M
import qualified Data.Set as S

data POVal = NoInv




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

-- | Print out a candidate
showState c = show (classes c) ++ "\n" ++
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


data BoolInvGen =
  BoolInvGen [([Identifier])] [(Identifier,Identifier)] -- Equ. classes, chains.

instance InvGen BoolInvGen where
  fromStates states = BoolInvGen [states] []
  typeName _ = Sort_bool
  equal _ = "="
  ord _ = "implies"

  classes (BoolInvGen state _) = state
  chains (BoolInvGen state cs) = [] -- cs

  refine (BoolInvGen state cs) model =
     BoolInvGen [eq | eq <- concat state', not (null eq)]
      cs'
    where

          state' = map snd newNodes
          cs' = nub $ concatMap nextEdge newNodes

          nextNode cls@(rep:_) =
               let ntrue = [v | (v,t) <- model, v `elem` cls, isTrue t]
                   nfalse = [v | (v,t) <- model, v `elem` cls, not (isTrue t)]
               in (rep,[nfalse,ntrue])
          newNodes = map nextNode state

          nextEdge (r,[f:_,t:ts]) = (f,t):[(t,dest p) | (r,p) <- cs]
          nextEdge (r,[[],t:_]) = [(t,dest p) | (r,p) <- cs]
          nextEdge (r,[f:_,[]]) = [(f,dest p) | (r,p) <- cs]
          dest p = case lookup p newNodes of
                     Nothing -> p -- This should be an error
                     Just [a:_,_] -> a
                     Just [[],a:_] -> a

          isTrue (Term_qual_identifier (Qual_identifier (Identifier "true"))) = True
          isTrue _ = False



-- Partial order insertion for traces.
-- We represent a partial order by a list of pairs (a,b). We want to
-- build a new partial order that takes into account a new step of the
-- trace.

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

--suc :: Sigma -> Sigma
suc sigma = M.map f sigma
  where f v = v S.\\ getAll v
        getAll vals = S.unions $ S.toList $
                      S.map (\k -> M.findWithDefault S.empty k sigma) vals



data IntInvGen = IntInvGen [[Identifier]] PO deriving Show
instance InvGen IntInvGen where

  fromStates states = IntInvGen [states] (initialSigma (S.fromList states))
  typeName _ = Sort_identifier (Identifier "Int")



  equal _ = "="
  ord _ = "<="
  classes (IntInvGen states _) = states
  chains (IntInvGen states po) =
    [(from,to) | (from,tos) <- M.toList red,
                 to <- S.toList tos]

    where red = suc po'
          po' = M.mapMaybeWithKey f po
          f node edges
            | S.member node reps =
               Just $ S.filter (\next -> S.member next reps) edges
            | otherwise = Nothing
          reps = S.fromList $ map head states

  refine candidate@(IntInvGen states po) model = IntInvGen states' po'
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

-- Testing
-- po (IntInvGen _ p) = p
-- a = [(Identifier x) |
--      x <- ["a","b","c","d","e"]]
-- v0 = zip a [Term_spec_constant (Spec_constant_numeral n) | n <- [0,0,1,1,1]]
-- v1 = zip a [Term_spec_constant (Spec_constant_numeral n) | n <- [0,1,2,3,3]]
-- v2 = zip a [Term_spec_constant (Spec_constant_numeral n) | n <- [0,2,1,3,3]]

-- t = IntInvGen [a] (initialSigma (S.fromList a))

-- test = refine (refine (refine t v0) v1) v2



-- invGenProcess :: InvGen a => a -> ConnectionPool -> HindFile -> Chan Term ->
--                   (ProverException -> IO ()) -> IO (ThreadId, IO ())
invGenProcess candidateType pool hindFile invChan onError =
  withProverException pool "Hind.invGen" onError $ \p -> do
   infoM "Hind.invGen" "Started invariant generation"
   defineSystem hindFile p

   let initialState = fromSystem hindFile `asTypeOf` candidateType

   let trans' = trans hindFile
       assert = assertTerm p

   -- Iteratively check a candidate, and refine using a
   -- counterexample. We exit when we get a property
   -- that holds for step k and k+1 without refinement.
   let baseRefine candidate k = do
         assert (trans' (baseTime k))
         assert (baseTimeIs k)
         baseRefine' False candidate k

       baseRefine' refined candidate k = do

         push 1 p -- Candidate Push
         let cterm = toTerm candidate (baseTime k)
         infoM "Hind.invGen" (showState candidate)
         infoM "Hind.invGen" ("Checking candidate (base " ++ show k ++ ")\n\t" ++ show cterm)

         assert $ notTerm (baseTimeIs k `impliesTerm` cterm)
         ok <- isUnsat p

         if ok
           then do
             infoM "Hind.invGen" "Candidate passed."
             pop 1 p -- Candidate Pop
             if refined
               then baseRefine candidate (k+1)
               else return (candidate,k)
           else do
             model <- getValuation p (vars candidate) (baseTime k)
             pop 1 p -- Candidate Pop
             infoM "Hind.invGen" $ "Got counterexample:\n\t" ++ show model
             let model' = refine candidate model
             baseRefine' True model' k

       stepRefine candidate k = do

         -- Assert the transition relation
         mapM_ assert [trans' (stepTime i) | i <- [0..k+1]]
         -- Assert the candidate for prev.
         mapM_ assert [toTerm candidate (stepTime i) | i <- [1..k+1]]
         stepRefine' candidate

       stepRefine' candidate = do
         push 1 p
         let cterm = toTerm candidate (stepTime 0)
         infoM "Hind.invGen" (showState candidate)
         infoM "Hind.invGen" ("Checking candidate (step)\n\t" ++ show cterm)
         assert (notTerm cterm)
         ok <- isUnsat p
         if ok
           then do
             infoM "Hind.invGen" ("Found invariant:\n\t" ++ show cterm)
             pop 1 p
             -- writeChan invChan cterm
             return candidate
           else do
             model <- getValuation p (vars candidate) (stepTime 0)
             pop 1 p
             stepRefine' (refine candidate model)


   push 1 p -- Context for base transition assertions
   (baseCandidate,baseK) <- baseRefine initialState 0
   pop 1  p -- Close context  for base transition assertions

   infoM "Hind.invGen" $ "Base process found candidate  " ++ show (toTerm baseCandidate (baseTime baseK))
   push 1 p -- Context for step transition assertions
   stepCandidate <- stepRefine baseCandidate baseK
   pop 1 p -- Close context for step transition assertions
   return ()

-- | This works for getting a valuation *from Z3*. The response is
-- parsed as a get-proof response, for whatever reason. This is a
-- colossal pain in the ass.
getValuation p vars time = do
  vals <- sendCommand p (Get_value [Term_qual_identifier_ (Qual_identifier v) [time] | v <- vars])
  infoM "Hind.invGen" ("Got Model:" ++ show vals)
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

getAndProcessInv :: a -> b -> c -> d -> e -> IO POVal
getAndProcessInv _ _ _ _ _ = return NoInv
assertBaseInvState :: a -> b -> IO ()
assertBaseInvState _ _ = return ()
assertBaseInv _ = return ()
assertStepInvState :: a -> b -> IO ()
assertStepInvState _ _ = return ()
assertStepInv :: a -> b -> IO ()
assertStepInv _ _ = return ()


{-
-- Invariant Generation
-- invGenProcess proverCmd model property initPO invChan = forkIO $ do
invGenProcess' pool hindFile invChan onError = do
  candidatesChan <- newChan
  basePassed <- newChan
  candidateDone <- newEmptyMVar

  -- The step process writes to the inv chan, but it reads from a duplicated
  -- version.
  baseProcInv <- dupChan invChan
  stepProcInv <- dupChan invChan

  baseProc <-
    invGenBaseProcess pool hindFile candidatesChan
                      basePassed candidateDone baseProcInv onError

  stepProc <-
    invGenStepProcess pool hindFile basePassed stepProcInv candidateDone onError
  writeList2Chan candidatesChan candidates
  return (baseProc,stepProc)
  where candidates =
          [genPO sort states i
           -- FIXME: No reason to reverse this, it was just so that int
           -- candidates were checked before bool.
           | (sort,states) <-  reverse $ hindStates hindFile,sort `elem` validSorts
           | i <- [0..] ]
        validSorts = [Sort_identifier (Identifier "Int"), Sort_identifier (Identifier "Bool")]


-- | The refinement process for the base case of invariant generation based on a partial order.
invGenBaseProcess ::
  ConnectionPool -> -- ^ Prover connection pool
  HindFile -> -- ^ Input File
  Chan POVal -> -- ^ Source for candidates
  Chan (Integer, POVal) ->  -- ^ Sink to step case
  MVar POVal ->  -- ^ Feedback from step case
  Chan POVal -> -- ^ A source for invariants
  (ProverException -> IO ()) ->  -- ^ What to do on prover errors
  IO (ThreadId, IO ())
invGenBaseProcess pool hindFile source sink isDone invChan onError =
  {-# SCC "invGenBaseProcess" #-}
  withProverException pool "Hind.invGen.Base" onError $ \p -> do

    -- Initialize the prover with the transition system
    mapM_ (sendCommand p) transitionSystem

    -- | 'loop' is the outer loop, increasing 'k'
    let loop po invId k = do


          (po',k') <- do
            -- Check to see if there a previous candidate has been verified.
            res <- tryTakeMVar isDone
            case res of
              Just po'
                | revMajor po == revMajor po'
                   -> do
                       infoM "Hind.invGen.Base" $
                               "Got isDone of " ++ show po' ++ show po
                       po' <- readChan source
                       return (po',0)
                | otherwise -> do
                       infoM "Hind.invGen.Base" $
                               "Got isDone of " ++ show po' ++ show po
                       return (po,k)
              Nothing -> return (po,k)

          -- Assert the current invariant, or a new one if it is available.
          invId' <- getAndProcessInv p invChan invId
                    (assertBaseInv p k') (assertBaseInv p k')

          mapM_ (sendCommand p)
                  [(Assert
                    (Term_qual_identifier_ (Qual_identifier trans)
                     [Term_spec_constant (Spec_constant_numeral i)]))
                          | i <- [0..k']]
          refinement po' invId'  k'

        -- | 'refinement' searches for an invariant.
        -- refinement :: PO po => po -> Integer -> IO ()
        refinement po invId k = do
          invId' <- getAndProcessInv p invChan invId
                    (\_ -> return ()) (assertBaseInv p k)


          let candidateFormula :: Term
              candidateFormula = formula po (k_time k)
          push 1 p
          infoM "Hind.invGen.Base" $
                  "Checking candidate:" ++ show candidateFormula ++
                  "(" ++ show k ++ ")"
          -- negate the candidate
          sendCommand p (Assert (negateTerm candidateFormula))
          valid <- isUnsat p
          if valid
               then do
                 pop 1 p
                 -- Assert the invariant for k
                 infoM "Hind.invGen.Base" $
                    "Verified candidate:" ++ show candidateFormula ++
                     "(" ++ show k ++ ")"

                 sendCommand p (Assert candidateFormula)
                 -- Pass the candidate order to the step process
                 writeChan sink (k,po)
                 loop po invId' (k+1)

               else do
                 infoM "Hind.invGen.Base" $
                         "Candidate not valid:" ++ show candidateFormula ++
                         "(" ++ show k ++ ")"

                 -- Query the countermodel
                 counterModel <- valuation p po (k_time k)
                 infoM "Hind.invGen.Base" $
                        "Got Countermodel: " ++ show counterModel
                 pop 1 p
                 case refine counterModel po of
                   Nothing -> do
                     po' <- readChan source
                     loop po invId' 0
                   Just po' -> refinement po' invId' k
    -- start running the process
    po <- readChan source
    loop po NoInv 0
  where (Script transitionSystem) = hindScript hindFile
        trans = hindTransition hindFile

-- | The refinement process for the step case of invariant generation based on a
-- partial order. The 'sink' is both the invariant output (for invariants that
-- this process has verified) and input (for invariants that some other process
-- has generated)
invGenStepProcess ::
  ConnectionPool -> HindFile ->
  Chan (Integer,POVal) -> Chan POVal -> MVar POVal ->
  (ProverException -> IO ()) ->  -- ^ What to do on prover errors
  IO (ThreadId, IO ())
invGenStepProcess pool hindFile source sink isDone onError  =
  {-# SCC "invGenStepProcess" #-}
  withProverException pool "Hind.invStep" onError $ \p -> do
    -- Initialize the prover with the transition system
    mapM_ (sendCommand p) transitionSystem

    -- time i = (n - i)
    let time i = Term_qual_identifier_ (Qual_identifier (Identifier "-"))
                   [Term_qual_identifier (Qual_identifier (Identifier indVar)),
                    Term_spec_constant (Spec_constant_numeral i)]
    let loop :: Maybe POVal -> InvId -> IO ()
        loop cur invId = do
          push 1 p
          -- Get a k-base-valid candidate
          (k,po) <- getNext source cur
          -- set up the transition system
          mapM_ (sendCommand p)
                -- trans (n-i)
                [Assert (Term_qual_identifier_ (Qual_identifier trans) [time i])
                 | i <- [0..k+1]]

          -- Send path compression
          mapM_ (sendCommand p) $ distinctStates (k+1)
          -- Fetch/Assert inferred invariants
          invId' <- getAndProcessInv p sink invId
                    (assertStepInv p k)
                    (assertStepInv p k)
          refinement po invId' k

        -- start the refinement process
        refinement po invId k = do
          invId' <- getAndProcessInv p sink invId
                    (\_ -> return ()) -- Don't assert invariant that isn't new.
                    (assertStepInv p k)

          push 1 p
          -- Assert the induction hypothesis for previous k+1 steps
          mapM_ (sendCommand p)
                [Assert (formula po (time i))
                 | i <- [1..k+1]]
          -- Assert the negated candidate
          let candidateFormula = (formula po (time 0))
          infoM "Hind.invGen.Step" $
                  "Checking candidate:" ++ show candidateFormula ++
                  "(" ++ show k ++ ")"

          sendCommand p (Assert (negateTerm candidateFormula))

          valid <- isUnsat p
          if valid
             then do
               infoM "Hind.invGen.Step" $
                  "Verified candidate" ++ show candidateFormula ++
                  "(" ++ show k ++ ")"


               let n_term = (Term_qual_identifier (Qual_identifier (Identifier "n")))
                   inv_formula =
                     Term_forall [Sorted_var "n" (Sort_identifier (Identifier "integer"))]
                                 (formula po n_term)
               noticeM "Hind.invGen.Step" $
                  "Discovered invariant" ++ show inv_formula ++
                  "(" ++ show k ++ ")"
               pop 2 p
               writeChan sink po
               putMVar isDone po
               loop (Just po) invId'
             else do
               infoM "Hind.invGen.Step" $
                  "Candidate not valid:" ++ show candidateFormula ++
                  "(" ++ show k ++ ")"
               counterModel <- valuation p po (time 0)
               infoM "Hind.invGen.Step" $
                        "Got Countermodel: " ++ show counterModel

               pop 1 p
               case refine counterModel po of
                 Nothing -> loop Nothing invId'
                 Just po' -> do
                   infoM "Hind.invGen.Step" $
                         "Refined " ++ show po ++ " to " ++ show po'
                   refinement po' invId' k

    loop Nothing NoInv

  where (Script transitionSystem) = hindScript hindFile
        trans = hindTransition hindFile
        -- GetChan will drop candidates sent by the base process that
        -- we've already verified as valid.
        getNext chan Nothing = readChan chan
        getNext chan (Just p) = do

          n@(_,p') <- readChan chan
          if revMajor p == revMajor p'
             then do debugM "invGenStep" "Skipping"
                     getNext chan (Just p)
             else return n

-- | Convert the integer 'k' to a Term
k_time k = Term_spec_constant (Spec_constant_numeral k)

-- | Get the valuation of a model from the solver.
valuation p po time = do
      Ga_response vals <- sendCommand p (Get_value terms)
      return (zip varNames vals)
  where varNames = vars po
        terms =
          [Term_qual_identifier_ (Qual_identifier sv) [time]
             | sv <- varNames]

-- FIXME: The 'PO' class and associated instances and code should be moved to a
-- different module. Moreover, it should be split into a class for partial
-- orders, and one that just has handles refinement, formula generation, and
-- versioning.

-- Invariant generation uses a partial order for candidate set generation
class Show a => PO a where
  -- | Construct a partial order from an equivalence over state variables.
  -- Each list element represents an equivalence class, and the classes are ordered
  -- according to the partial order <= relation.
  -- Takes a major/minor revision number
  toPO :: Int -> Int -> Gr Identifier -> a

  -- | Convert a partial order to an equivalence relation over state variables.
  -- Each list element represents an equivalence class, and the classes are ordered
  -- according to the partial order <= relation.
  fromPO :: a -> Gr Identifier

  -- | Get all of the state variables in the partial order.
  vars :: a -> [Identifier]
  vars po = nub $ concatMap snd eq
   where (eq,_) = fromPO po

  -- | Refine a partial order using the given countermodel.
  refine :: [(Identifier,Term)] -> a -> Maybe a
  refine model prev = toPO maj (min+1) <$> next
     where maj = revMajor prev
           min = revMinor prev
           next = grRefine (fromPO prev) model

  -- | Generate a formula (for the given time) for this partial order.
  formula :: a -> Term -> Term
  formula po time = grFormula  (fromPO po) (lt po) time

  -- | The "<=" relation
  lt :: a -> Identifier

  -- | revision identifiers
  revMajor :: a -> Int
  revMinor :: a -> Int


-- | POVal is an existential wrapper around a PO
data POVal = forall a. PO a => POVal a
instance Show POVal where
  show (POVal p) = show p

-- | Create a POVal wrapping a PO of the type of the first argument.
makePO :: forall a. PO a => a -> Int -> Int -> [Identifier] -> POVal
makePO _ maj min ps = POVal (toPO maj min ([(0,ps)],S.empty) :: a)

-- | Create a POVal given a Sort and major revision number.
genPO :: Sort -> [Identifier] -> Int -> POVal
genPO (Sort_identifier (Identifier "Int")) svs maj =
  makePO (undefined :: IntPO) maj 0 svs
genPO (Sort_identifier (Identifier "Bool")) svs maj =
  makePO (undefined :: BoolPO) maj 0 svs
genPO Sort_bool svs maj = makePO (undefined :: BoolPO) maj 0  svs


instance PO POVal where
  toPO _ = error "Use makePO, passing a witness of the type you wish to pack"
  fromPO (POVal p) = fromPO p
  vars (POVal p) = vars p
  refine valuation (POVal p) = POVal <$> (refine valuation p)
  formula (POVal p) = formula p
  lt (POVal p) = lt p
  revMajor (POVal p) = revMajor p
  revMinor (POVal p) = revMinor p

-- | The partial order for integers.  The inner list corresponds to a
-- equivalence class, the outer list orders the equivalence classes using <=.
data IntPO = IntPO Int Int (Gr Identifier) deriving Show
instance PO IntPO where
  toPO maj min ss = IntPO maj min ss
  fromPO (IntPO _ _ p) = p
  lt _ = (Identifier "<=")
  revMajor (IntPO maj _ _) = maj
  revMinor (IntPO _ min _) = min

data BoolPO = BoolPO Int Int (Gr Identifier) deriving Show
instance PO BoolPO where
  toPO maj min ss  = BoolPO maj min ss
  fromPO (BoolPO _ _ p) = p
  lt _ = (Identifier "implies")
  revMajor (BoolPO maj _ _) = maj
  revMinor (BoolPO _ min _) = min

-- | Utility functions
-- poFormula works for a po that is an ordered partition
poFormula rel partition time =
    Term_qual_identifier_ (Qual_identifier (Identifier "and"))
                            (equivalences ++ ineq (map head partition))
    where -- Generate "c(k) = c'(k) for each c in cs
      equiv (c:cs) =
          [Term_qual_identifier_ (Qual_identifier (Identifier "="))
           [Term_qual_identifier_
            (Qual_identifier c)
            [time],
            Term_qual_identifier_
            (Qual_identifier c')
            [time]]
             | c' <- cs]

      equivalences = concatMap equiv partition
      ineq [] = []
      ineq [t] = []
      ineq (r:s:ts) =
          (Term_qual_identifier_ (Qual_identifier rel)
                                  [Term_qual_identifier_
                                   (Qual_identifier r)
                                   [time],
                                   Term_qual_identifier_
                                   (Qual_identifier s)
                                   [time]]):ineq (s:ts)

-- | Refine a conjecture.
poRefine prev model
  | prev == next = Nothing
  | otherwise = Just next
  where next =  [q | (n,v) <- model
           , then group by v -- Sorting is implicit.
           , p <- prev
           , q@(_:_) <- [n `intersect` p] -- Make sure there's at least one element
           ]



negateTerm term =
  (Term_qual_identifier_ (Qual_identifier (Identifier "not")) [term])


instance Eq Term where
   (Term_qual_identifier (Qual_identifier (Identifier t1))) ==
    (Term_qual_identifier (Qual_identifier (Identifier t2))) = t1 == t2

   (Term_spec_constant (Spec_constant_numeral t1)) == (Term_spec_constant (Spec_constant_numeral t2)) = t1 == t2


instance Ord Term where
   (Term_qual_identifier (Qual_identifier (Identifier "true"))) `compare`
    (Term_qual_identifier (Qual_identifier (Identifier "false"))) = GT

   (Term_qual_identifier (Qual_identifier (Identifier "false"))) `compare`
    (Term_qual_identifier (Qual_identifier (Identifier "true"))) = LT

   (Term_qual_identifier (Qual_identifier (Identifier "true"))) `compare`
    (Term_qual_identifier (Qual_identifier (Identifier "true"))) = EQ

   (Term_qual_identifier (Qual_identifier (Identifier "false"))) `compare`
    (Term_qual_identifier (Qual_identifier (Identifier "false"))) = EQ

   (Term_spec_constant (Spec_constant_numeral t1)) `compare`
    (Term_spec_constant (Spec_constant_numeral t2)) = t1 `compare` t2


   compare t1 t2 = error $ show t1 ++ show t2


type Gr a = ([(Int,[a])], S.Set (Int,Int))
a :: Gr Identifier
a = ([(0,(map toId "abc"))],S.empty)
m1 = [(toId 'a',0), (toId 'b',1),(toId 'c',1)]
m2 = [(toId 'a',1), (toId 'b',0),(toId 'c',0)]

toId :: Char -> Identifier
toId c = Identifier [c]


grRefine :: forall a v. (Ord v, Ord a, Eq a) => Gr a -> [(a,v)] -> Maybe (Gr a)
grRefine prev@(oldBlocks,edges) model
  | grEmpty next || same prev next  = Nothing
  | otherwise = Just next
  where temp =  [((oldId,newId),q) | (n,v) <- model
           , then group by v -- Sorting is implicit.
           , (oldId,p) <- oldBlocks
           , q@(_:_) <- [n `intersect` p] -- Make sure there's at least one element
           | newId <- [0..]
           ]
        blocks = [(id,block) |((_,id),block) <- temp]
        next :: Gr a
        next = (blocks, S.fromList $ updateEdges ++ newEdges)

        updateEdges = [(newA,newB) | ((oldA,newA),_) <- temp
                      ,  ((oldB,newB),_) <- temp
                      , (from,to) <- S.toList edges
                      , oldA == from, oldB == to
                      ]
        newEdges = [(newA,newB) | ((_,newA),_) <- temp
                                | ((_,newB),_) <- safeTail temp]
        safeTail [] = []
        safeTail (a:as) = as
        same (aBlocks,aEdges) (bBlocks,bEdges) =
          S.fromList (map fst aBlocks) == S.fromList (map fst bBlocks) &&
          aEdges == bEdges




grFormula :: Gr Identifier -> Identifier -> Term -> Term
grFormula (partition,edges) rel time =
    Term_qual_identifier_ (Qual_identifier (Identifier "and"))
                            (equivalences ++ ordered)
    where -- Generate "c(k) = c'(k) for each c in cs
      equiv (_,(c:cs)) =
          [Term_qual_identifier_ (Qual_identifier (Identifier "="))
           [Term_qual_identifier_
            (Qual_identifier c)
            [time],
            Term_qual_identifier_
            (Qual_identifier c')
            [time]]
             | c' <- cs]

      equivalences = concatMap equiv partition
      ordered = concatMap inEq (S.toList edges)
      inEq (r,s)
           | (s,r) `S.member` edges = []
           | otherwise =
             case (lookup r partition, lookup s partition) of
               (Just (rid:_), Just (sid:_)) ->
                 [(Term_qual_identifier_ (Qual_identifier rel)
                                  [Term_qual_identifier_
                                   (Qual_identifier rid)
                                   [time],
                                   Term_qual_identifier_
                                   (Qual_identifier sid)
                                   [time]])]

-- | A Graph is empty if it only has singleton blocks and no valid implications.
grEmpty :: Gr a -> Bool
grEmpty (partition,edges) =
  (null [l | l@(_,(_:_:_)) <- partition]) &&
  (null [e | e@(l,r) <- S.toList edges, not (S.member (r,l) edges)])

-- | Handling invariant stuff.
data InvId = NoInv | Inv Int deriving Show

incInvId NoInv = Inv 0
incInvId (Inv x) = Inv (x+1)

invName NoInv = "noinv"
invName (Inv i) = "_inv_" ++ show i

addInvFormula NoInv term = term
addInvFormula i term =
  Term_qual_identifier_ (Qual_identifier (Identifier "and"))
    [Term_qual_identifier_ (Qual_identifier (Identifier (invName i)))
     [Term_qual_identifier (Qual_identifier (Identifier "step"))],
     term]


-- | Try to read a new invariant. In the case that there is one available,
-- generate a new definition and return the name of the new invariant.
-- TODO: This should really continue to read and build new invariants as long
-- as more are available.
getInvariant prover invChan curId = do
  empty <- isEmptyChan invChan
  if empty
     then return Nothing
     else do
       inv <- readChan invChan
       -- Generate a new definition
       let nextInvId = incInvId curId
       let invFun = Define_fun (invName nextInvId)
                     [Sorted_var "step" (Sort_identifier (Identifier "Int"))] Sort_bool
                     (addInvFormula curId
                     (formula inv (Term_qual_identifier (Qual_identifier (Identifier "step")))))

       sendCommand prover invFun
       return (Just nextInvId)

-- | For a given invariant 'inv', assert (inv 0), (inv 1) ... (inv k)
assertBaseInvState p k NoInv = return ()
assertBaseInvState p k invId = do
  sendCommand p
    (Assert (Term_qual_identifier_ (Qual_identifier (Identifier (invName invId)))
             [Term_spec_constant (Spec_constant_numeral k)]))
  return ()

-- | For a given invariant 'inv', assert
-- (inv (- n 0)), (inv (- n 1)) ... (inv (- n k))
assertStepInvState p k NoInv = return ()
assertStepInvState p k invId = do
    sendCommand p tm
    return ()
  where tm =
         Assert (Term_qual_identifier_ (Qual_identifier (Identifier (invName invId)))
                 [Term_qual_identifier_ (Qual_identifier (Identifier "-"))
                  [Term_qual_identifier (Qual_identifier (Identifier indVar)),
                   Term_spec_constant (Spec_constant_numeral k)]])




-- | For a given invariant 'inv', assert (inv k)
assertBaseInv p k invId = do
  sequence_ [assertBaseInvState p i invId | i <- [0..k]]

-- | For a given invariant 'inv', assert (inv (- n k))
assertStepInv _ k NoInv = return ()
assertStepInv p k invId =
  sequence_ [assertStepInvState p i invId | i <- [0..k]]



-- | Try to fetch a new invariant. If a new one is available, apply 'onNew' to
-- it; otherwise, apply 'onOld' to the old invariant. Return either the old
-- invariant or else the newly-fetched invariant.
getAndProcessInv p invChan invId onOld onNew = do
  nextInv <- getInvariant p invChan invId

  case nextInv of
    Nothing -> do
      onOld invId
      return invId
    Just newInv -> do
      infoM (name p) $  "Asserting new invariant" ++ show newInv
      onNew newInv
      return newInv
-}