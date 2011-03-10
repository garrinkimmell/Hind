{-# LANGUAGE RankNTypes, ExistentialQuantification, ScopedTypeVariables, TransformListComp #-}
module Hind.InvGen where

import Hind.Parser(HindFile(..))
import Hind.Interaction
import Language.SMTLIB

import Control.Exception
import Control.Monad
import Control.Concurrent
import Data.List(sortBy, groupBy,nub,intersect)



-- Invariant Generation
-- invGenProcess proverCmd model property initPO invChan = forkIO $ do
invGenProcess proverCmd hindFile invChan = do
  basePassed <- newChan
  candidateDone <- newEmptyMVar
  baseProc <- invGenBaseProcess proverCmd hindFile basePassed candidateDone
  stepProc <- invGenStepProcess proverCmd hindFile basePassed invChan candidateDone
  return (baseProc,stepProc)

-- | The refinement process for the base case of invariant generation based on a partial order.
-- invGenBaseProcess :: PO po => String -> [Command] -> po -> Chan (Integer,po) -> IO ThreadId
invGenBaseProcess :: String -> HindFile -> Chan (Integer, POVal) -> MVar Int -> IO ThreadId
invGenBaseProcess proverCmd hindFile sink isDone = forkIO  $
  {-# SCC "invGenBaseProcess" #-}
  bracket (makeProverNamed proverCmd "invGenBase") closeProver $ \p -> do

    -- Initialize the prover with the transition system
    mapM_ (sendCommand p) transitionSystem

    -- | 'loop' is the outer loop, increasing 'k'
    let loop po k = do
          done <- tryTakeMVar isDone
          -- Currently we're just using this like a boolean flag, later we'll pass a candidate id
          case done of
            Just _ -> return ()
            Nothing -> do
               sendCommand p (Assert
                  (Term_qual_identifier_ (Qual_identifier trans)
                   [Term_spec_constant (Spec_constant_numeral k)]))
               refinement po k

        -- | 'refinement' searches for an invariant.
        -- refinement :: PO po => po -> Integer -> IO ()
        refinement po k = do
          let candidateFormula :: Term
              candidateFormula = formula po (k_time k)
          push 1 p
          -- negate the candidate
          sendCommand p (Assert (negateTerm candidateFormula))
          valid <- isUnsat p
          if valid
               then do
                 pop 1 p
                 -- Assert the invariant for k
                 sendCommand p (Assert candidateFormula)
                 -- Pass the candidate order to the step process
                 writeChan sink (k,po)
                 loop po (k+1)

               else do
                 -- Query the countermodel
                 counterModel <- valuation p po (k_time k)
                 let next = refine (counterModel) po
                 pop 1 p
                 -- unless (next == po) $ refinement next k
                 refinement next k
    -- start running the process
    loop initPO 0
  where (Script transitionSystem) = hindScript hindFile
        initPO = makePO (undefined :: IntPO) [hindStates hindFile]
        trans = hindTransition hindFile

-- | The refinement process for the step case of invariant generation based on a partial order.
invGenStepProcess ::
  String -> HindFile -> Chan (Integer,POVal) -> Chan POVal -> MVar Int -> IO ThreadId
invGenStepProcess proverCmd hindFile source sink isDone  = forkIO $

  {-# SCC "invGenStepProcess" #-}
  bracket (makeProverNamed proverCmd "invStep") closeProver $ \p -> do
    -- Initialize the prover with the transition system
    mapM_ (sendCommand p) transitionSystem

    -- time i = (n - i)
    let time i = Term_qual_identifier_ (Qual_identifier (Identifier "-"))
                   [Term_qual_identifier (Qual_identifier (Identifier "n")),
                    Term_spec_constant (Spec_constant_numeral i)]
    let loop = do
          push 1 p
          -- Get a k-base-valid candidate
          (k,po) <- readChan source
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
          sendCommand p (Assert (negateTerm (formula po (time 0))))
          valid <- isUnsat p
          if valid
             then do
               putStrLn $ "Found a valid invariant (" ++ show k ++ ")"

               let n_term = (Term_qual_identifier (Qual_identifier (Identifier "n")))
                   inv_formula =
                     Term_forall [Sorted_var "n" (Sort_identifier (Identifier "integer"))]
                                 (formula po n_term)
               print inv_formula
               pop 2 p
               writeChan sink po
               -- putMVar isDone 0
               loop
             else do
               putStrLn "Invariant Candidate not valid"
               counterModel <- valuation p po (time 0)
               let next = refine counterModel po
               pop 1 p
               refinement next k

    loop
  where (Script transitionSystem) = hindScript hindFile
        trans = hindTransition hindFile

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
class PO a where
  -- | Construct a partial order from an equivalence over state variables.
  -- Each list element represents an equivalence class, and the classes are ordered
  -- according to the partial order <= relation.
  toPO :: [[Identifier]] -> a

  -- | Convert a partial order to an equivalence relation over state variables.
  -- Each list element represents an equivalence class, and the classes are ordered
  -- according to the partial order <= relation.
  fromPO :: a -> [[Identifier]]

  -- | Get all of the state variables in the partial order.
  vars :: a -> [Identifier]

  -- | Refine a partial order using the given countermodel.
  refine :: [(Identifier,Term)] -> a -> a

  -- | Generate a formula (for the given time) for this partial order.
  formula :: a -> Term -> Term


-- | POVal is an existential wrapper around a PO
data POVal = forall a. PO a => POVal a

-- | Create a POVal wrapping a PO of the type of the first argument.
makePO :: forall a. PO a => a -> [[Identifier]] -> POVal
makePO _ ps = POVal (toPO ps :: a)


instance PO POVal where
  toPO _ = error "Use makePO, passing a witness of the type you wish to pack"
  fromPO (POVal p) = fromPO p
  vars (POVal p) = vars p
  refine valuation (POVal p) = POVal (refine valuation p)
  formula (POVal p) = formula p

-- |The partial order for integers
-- The inner list corresponds to a equivalence class, the outer list orders the equivalence classes using <=.
newtype IntPO = IntPO [[Identifier]]
instance PO IntPO where
  toPO = IntPO
  fromPO (IntPO p) = p

  vars (IntPO p) = nub $ concat p

  refine model (IntPO prev) = IntPO
                  [q | (n,v) <- model
                  , then group by v -- Sorting is implicit.
                  , p <- prev -- singleton classes are useless
                  , q@(_:_) <- [n `intersect` p] -- Make sure there's at least two elements
                  ]


  formula (IntPO p) time =
    Term_qual_identifier_ (Qual_identifier (Identifier "and"))
                            (equivalences ++ ineq (map head p))
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

      equivalences = concatMap equiv p
      ineq [] = []
      ineq [t] = []
      ineq (r:s:ts) =
          (Term_qual_identifier_ (Qual_identifier (Identifier "<="))
                                  [Term_qual_identifier_
                                   (Qual_identifier r)
                                   [time],
                                   Term_qual_identifier_
                                   (Qual_identifier s)
                                   [time]]):ineq (s:ts)

negateTerm term =
  (Term_qual_identifier_ (Qual_identifier (Identifier "not")) [term])


instance Eq Term where
   (Term_qual_identifier (Qual_identifier (Identifier t1))) ==
    (Term_qual_identifier (Qual_identifier (Identifier t2))) = t1 == t2

   (Term_spec_constant (Spec_constant_numeral t1)) == (Term_spec_constant (Spec_constant_numeral t2)) = t1 == t2


instance Ord Term where
   (Term_qual_identifier (Qual_identifier (Identifier "true"))) `compare`
    (Term_qual_identifier (Qual_identifier (Identifier "false"))) = LT

   (Term_qual_identifier (Qual_identifier (Identifier "false"))) `compare`
    (Term_qual_identifier (Qual_identifier (Identifier "true"))) = GT

   (Term_qual_identifier (Qual_identifier (Identifier "true"))) `compare`
    (Term_qual_identifier (Qual_identifier (Identifier "true"))) = EQ

   (Term_qual_identifier (Qual_identifier (Identifier "false"))) `compare`
    (Term_qual_identifier (Qual_identifier (Identifier "false"))) = EQ

   (Term_spec_constant (Spec_constant_numeral t1)) `compare`
    (Term_spec_constant (Spec_constant_numeral t2)) = t1 `compare` t2


   compare t1 t2 = error $ show t1 ++ show t2



instance Eq Identifier where
  (Identifier s) == (Identifier s') = s == s'
  (Identifier_ s ns) == (Identifier_ s' ns') = s == s' && ns == ns'
  _ == _ = False



t = [('a',3),('b',1),('c',1),('d',2),('e',3)]
t' = [('a',3),('b',9),('c',1),('d',2), ('e', 3)]

s = ["abcde"]

u prev model  =
  [q | (n,v) <- model
  , then group by v -- The sort is implicit?
  , p <- prev -- singleton classes are useless
  , q@(_:_) <- [n `intersect` p] -- Make sure there's at least one element
  ]