module Hind.PathCompression
  (distinctStates, stateCharacteristic, addPathCompression) where

import Hind.Parser
import Hind.Constants
import Hind.Utils
import Language.SMTLIB


-- | addPathCompression modifies a transisition system so that it includes path compression support.
addPathCompression :: HindFile -> HindFile
addPathCompression hf = hf { hindScript = Script (scr ++ pathCompressionSig hf) }
  where Script scr = hindScript hf


-- | Assert that states n-k .. n are distinct
distinctStates k =
  [stateCharacteristic i| i <- [0..k-1]]

stateCharacteristic k =
  (Assert (Term_qual_identifier_ (Qual_identifier (Identifier "__path_compression_def"))
           [Term_qual_identifier_ (Qual_identifier (Identifier "-"))
            [Term_qual_identifier (Qual_identifier (Identifier indVar)),
             Term_spec_constant (Spec_constant_numeral k)]]))



pathCompressionSig :: HindFile -> [Command]
pathCompressionSig hf = decls ++ defines
  where decls =
          [Declare_fun "__path_compression"
           (concat [replicate (length args) s |  (s,args) <- hindStates hf])
           (Sort_identifier (Identifier "Int")) ]
        defines =
          -- (= idx (path_compression (s0 idx) ... (s1 idx)))
          [Define_fun "__path_compression_def"
           [Sorted_var idxName (Sort_identifier (Identifier "Int"))] Sort_bool
           (Term_qual_identifier_ (Qual_identifier (Identifier "="))
            [idx,
             Term_qual_identifier_ (Qual_identifier (Identifier ("__path_compression")))
             [(Term_qual_identifier_ (Qual_identifier v) [idx]) | (_,vars) <- hindStates hf, v <- vars]

            ])]

        idx = Term_qual_identifier (Qual_identifier (Identifier idxName))
        idxName = "___idx"

-- | Generate the signature for path compression.
-- pathCompressionSig :: HindFile -> [Command]
pathCompressionSig hf = decls  ++ defines ++ top
  where decls =
          [Declare_fun (pcname sort )
                        (replicate (length ids) sort) (Sort_identifier (Identifier "Int"))
           | (sort,ids) <- hindStates hf]
        defines =
          [Define_fun (pcname sort ++ "_n")
                        [(Sorted_var idxName (Sort_identifier (Identifier "Int")))]
                          Sort_bool
                         (Term_qual_identifier_ (Qual_identifier (Identifier "="))
                          [(Term_qual_identifier_ (Qual_identifier (Identifier (pcname sort)))
                            [Term_qual_identifier_ (Qual_identifier i)
                               [idx]
                                 | i <- ids]),
                           idx])

           | (sort,ids) <- hindStates hf]
        top = [Define_fun ("___path_compression")
               [Sorted_var "___idx" (Sort_identifier (Identifier "Int"))] Sort_bool
               (Term_qual_identifier_ (Qual_identifier (Identifier "and"))
                [Term_qual_identifier_ (Qual_identifier (Identifier (pcname sort ++ "_n"))) [idx]
                | (sort,_) <- hindStates hf])]



        pcname sort = "___path_compression_" ++ pcSort sort

        pcSort (Sort_bitvec n) = "bitvec_" ++ show n
        pcSort s = show s

        idx = Term_qual_identifier (Qual_identifier (Identifier idxName))
        idxName = "___idx"
