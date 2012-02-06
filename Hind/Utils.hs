module Hind.Utils where

import Language.SMTLIB
import Hind.Parser
import Hind.Interaction
import Hind.Constants



assertTerm p t  = sendCommand p (Assert t)
-- Define a transition system, from a file
defineSystem hf p = mapM (sendCommand p) system
  where Script system = hindScript hf



notTerm t = Term_qual_identifier_ (Qual_identifier (Identifier "not")) [t]

-- Generate the term for the property for a given step
prop hf time = Term_qual_identifier_ (Qual_identifier property) [time]
  where [property] = hindProperties hf


-- Generate the term for the transition for a given step
trans hf time = Term_qual_identifier_ (Qual_identifier transition) [time]
  where transition = hindTransition hf

-- Generate the time index (e.g. (+ _base 3) or (- _n 4))
relTime op rel i = Term_qual_identifier_ (Qual_identifier (Identifier op))
                    [Term_qual_identifier (Qual_identifier (Identifier rel)),
                     Term_spec_constant (Spec_constant_numeral i)]

stepTime = relTime "-" indVar
baseTime = relTime "-" baseVar



binop op a b = Term_qual_identifier_ (Qual_identifier (Identifier op))  [a,b]
impliesTerm = binop "=>"
equalTerm = binop "="
minusTerm = binop "-"

int x = Term_spec_constant (Spec_constant_numeral x)

base = Term_qual_identifier (Qual_identifier (Identifier baseVar))

baseTimeIs x = equalTerm base (int x)