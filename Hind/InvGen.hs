{-# LANGUAGE RankNTypes, ExistentialQuantification, ScopedTypeVariables, TransformListComp, ParallelListComp #-}
module Hind.InvGen where

import Hind.Constants
import Hind.Parser(HindFile(..))
import Hind.Interaction
import Hind.PathCompression
import Hind.Chan
import Hind.ConnectionPool

import Language.SMTLIB

import qualified Data.Set as S
import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Concurrent(forkIO,newEmptyMVar,ThreadId)
import Control.Concurrent.MVar

import Data.List(sortBy, groupBy,nub,intersect)
import System.Log.Logger


-- Invariant Generation
-- invGenProcess proverCmd model property initPO invChan = forkIO $ do
invGenProcess pool hindFile invChan onError = do
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


