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

instance InvGen BoolInvGen where
  -- fromStates states = BoolInvGen [states] []
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
           debugM "Hind.invGen" $ show $ mkDef invariant names (Just k)
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

-- Junk from earlier implementation
-- getAndProcessInv :: a -> b -> c -> d -> e -> IO POVal
-- getAndProcessInv _ _ _ _ _ = return NoInv
-- assertBaseInvState :: a -> b -> IO ()
-- assertBaseInvState _ _ = return ()
-- assertBaseInv _ = return ()
-- assertStepInvState :: a -> b -> IO ()
-- assertStepInvState _ _ = return ()
-- assertStepInv :: a -> b -> IO ()
-- assertStepInv _ _ = return ()
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
