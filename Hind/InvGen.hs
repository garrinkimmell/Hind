{-# LANGUAGE RankNTypes, ExistentialQuantification, ScopedTypeVariables, TransformListComp, ParallelListComp #-}
module Hind.InvGen where

import Hind.Parser(HindFile(..))
import Hind.Interaction
import Language.SMTLIB

import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Concurrent
import Data.List(sortBy, groupBy,nub,intersect)
import System.Log.Logger


-- Invariant Generation
-- invGenProcess proverCmd model property initPO invChan = forkIO $ do
invGenProcess proverCmd hindFile invChan = do
  candidatesChan <- newChan
  basePassed <- newChan
  candidateDone <- newEmptyMVar
  baseProc <-
    invGenBaseProcess proverCmd hindFile candidatesChan basePassed candidateDone
  stepProc <-
    invGenStepProcess proverCmd hindFile basePassed invChan candidateDone
  writeList2Chan candidatesChan candidates
  return (baseProc,stepProc)
  where candidates =
          [genPO sort states i
           | (sort,states) <-  reverse $ hindStates hindFile
           | i <- [0..]]


-- | The refinement process for the base case of invariant generation based on a partial order.
invGenBaseProcess ::
  String -> -- ^ Prover command
  HindFile -> -- ^ Input File
  Chan POVal -> -- ^ Source for candidates
  Chan (Integer, POVal) ->  -- ^ Sink to step case
  MVar POVal ->  -- ^ Feedback from step case
  IO ThreadId
invGenBaseProcess proverCmd hindFile source sink isDone = forkIO  $
  {-# SCC "invGenBaseProcess" #-}
  bracket (makeProverNamed proverCmd "invGenBase") closeProver $ \p -> do

    -- Initialize the prover with the transition system
    mapM_ (sendCommand p) transitionSystem

    -- | 'loop' is the outer loop, increasing 'k'
    let loop po k = do
          next <- do
            -- Check to see if there a previous candidate has been verified.
            res <- tryTakeMVar isDone

            case res of
              Just po'
                | revMajor po == revMajor po'
                   -> do
                       infoM "Hind.invGenBase" $ "Got isDone of " ++ show po' ++ show po
                       po' <- readChan source
                       return $ Just (po',0)
                | otherwise -> do
                       infoM "Hind.invGenBase" $ "Got isDone of " ++ show po' ++ show po
                       return $ Just (po,k)
              Nothing -> return $ Just (po,k)
          case next of
            Nothing -> return ()
            Just (po',k) -> do
               sendCommand p (Assert
                  (Term_qual_identifier_ (Qual_identifier trans)
                   [Term_spec_constant (Spec_constant_numeral k)]))
               refinement po' k

        -- | 'refinement' searches for an invariant.
        -- refinement :: PO po => po -> Integer -> IO ()
        refinement po k = do
          let candidateFormula :: Term
              candidateFormula = formula po (k_time k)
          push 1 p
          infoM "Hind.invGenBase" $
                  "Checking candidate:" ++ show candidateFormula ++
                  "(" ++ show k ++ ")"
          -- negate the candidate
          sendCommand p (Assert (negateTerm candidateFormula))
          valid <- isUnsat p
          if valid
               then do
                 pop 1 p
                 -- Assert the invariant for k
                 noticeM "Hind.invGenBase" $
                    "Verified candidate:" ++ show candidateFormula ++
                     "(" ++ show k ++ ")"

                 sendCommand p (Assert candidateFormula)
                 -- Pass the candidate order to the step process
                 writeChan sink (k,po)
                 loop po (k+1)

               else do
                 infoM "Hind.invGenBase" $
                         "Candidate not valid:" ++ show candidateFormula ++
                         "(" ++ show k ++ ")"

                 -- Query the countermodel
                 counterModel <- valuation p po (k_time k)
                 infoM "Hind.invGenBase" $
                        "Got Countermodel: " ++ show counterModel
                 pop 1 p
                 case refine counterModel po of
                   Nothing -> do
                     po' <- readChan source
                     loop po 0
                   Just po' -> refinement po' k
    -- start running the process
    po <- readChan source
    loop po 0
  where (Script transitionSystem) = hindScript hindFile
        trans = hindTransition hindFile

-- | The refinement process for the step case of invariant generation based on a partial order.
invGenStepProcess ::
  String -> HindFile ->
  Chan (Integer,POVal) -> Chan POVal -> MVar POVal -> IO ThreadId
invGenStepProcess proverCmd hindFile source sink isDone  = forkIO $
  {-# SCC "invGenStepProcess" #-}
  bracket (makeProverNamed proverCmd "invStep") closeProver $ \p -> do
    -- Initialize the prover with the transition system
    mapM_ (sendCommand p) transitionSystem

    -- time i = (n - i)
    let time i = Term_qual_identifier_ (Qual_identifier (Identifier "-"))
                   [Term_qual_identifier (Qual_identifier (Identifier "n")),
                    Term_spec_constant (Spec_constant_numeral i)]
    let loop cur = do
          push 1 p
          -- Get a k-base-valid candidate
          (k,po) <- getNext source cur
          -- set up the transition system
          mapM_ (sendCommand p)
                -- trans (n-i)
                [Assert (Term_qual_identifier_ (Qual_identifier trans) [time i])
                 | i <- [0..k+1]]

          refinement po k

        -- start the refinement process
        refinement po k = do
          push 1 p
          -- Assert the induction hypothesis for previous k+1 steps
          mapM_ (sendCommand p)
                [Assert (formula po (time i))
                 | i <- [1..k+1]]
          -- Assert the negated candidate
          let candidateFormula = (formula po (time 0))
          infoM "Hind.invGenStep" $
                  "Checking candidate:" ++ show candidateFormula ++
                  "(" ++ show k ++ ")"

          sendCommand p (Assert (negateTerm candidateFormula))

          valid <- isUnsat p
          if valid
             then do
               noticeM "Hind.invGenStep" $
                  "Verified candidate" ++ show candidateFormula ++
                  "(" ++ show k ++ ")"


               let n_term = (Term_qual_identifier (Qual_identifier (Identifier "n")))
                   inv_formula =
                     Term_forall [Sorted_var "n" (Sort_identifier (Identifier "integer"))]
                                 (formula po n_term)
               noticeM "Hind.invGenStep" $
                  "Verified candidate" ++ show inv_formula ++
                  "(" ++ show k ++ ")"
               pop 2 p
               writeChan sink po
               putMVar isDone po
               loop (Just po)
             else do
               infoM "Hind.invGenStep" $
                  "Candidate not valid:" ++ show candidateFormula ++
                  "(" ++ show k ++ ")"
               counterModel <- valuation p po (time 0)
               infoM "Hind.invGenStep" $
                        "Got Countermodel: " ++ show counterModel

               pop 1 p
               case refine counterModel po of
                 Nothing -> loop Nothing
                 Just po' -> do
                   infoM "Hind.invGenStep" $
                         "Refined " ++ show po ++ " to " ++ show po'
                   refinement po' k

    loop Nothing
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


-- Invariant generation uses a partial order for candidate set generation
class Show a => PO a where
  -- | Construct a partial order from an equivalence over state variables.
  -- Each list element represents an equivalence class, and the classes are ordered
  -- according to the partial order <= relation.
  -- Takes a major/minor revision number
  toPO :: Int -> Int -> [[Identifier]] -> a

  -- | Convert a partial order to an equivalence relation over state variables.
  -- Each list element represents an equivalence class, and the classes are ordered
  -- according to the partial order <= relation.
  fromPO :: a -> [[Identifier]]

  -- | Get all of the state variables in the partial order.
  vars :: a -> [Identifier]
  vars = nub . concat . fromPO

  -- | Refine a partial order using the given countermodel.
  refine :: [(Identifier,Term)] -> a -> Maybe a
  refine model prev = toPO maj (min+1) <$> next
     where maj = revMajor prev
           min = revMinor prev
           next = poRefine (fromPO prev) model

  -- | Generate a formula (for the given time) for this partial order.
  formula :: a -> Term -> Term
  formula po time = poFormula (lt po) (fromPO po) time

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
makePO :: forall a. PO a => a -> Int -> Int -> [[Identifier]] -> POVal
makePO _ maj min ps = POVal (toPO maj min ps :: a)

-- | Create a POVal given a Sort and major revision number.
genPO :: Sort -> [Identifier] -> Int -> POVal
genPO (Sort_identifier (Identifier "Int")) svs maj =
  makePO (undefined :: IntPO) maj 0 [svs]
genPO (Sort_identifier (Identifier "Bool")) svs maj =
  makePO (undefined :: BoolPO) maj 0 [svs]
genPO Sort_bool svs maj = makePO (undefined :: BoolPO) maj 0  [svs]


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
data IntPO = IntPO Int Int [[Identifier]] deriving Show
instance PO IntPO where
  toPO maj min ss = IntPO maj min ss
  fromPO (IntPO _ _ p) = p
  lt _ = (Identifier "<=")
  revMajor (IntPO maj _ _) = maj
  revMinor (IntPO _ min _) = min

data BoolPO = BoolPO Int Int [[Identifier]] deriving Show
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



