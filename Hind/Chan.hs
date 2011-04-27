-- | A small wrapper around channels, to get around the 'isEmptyChan' issue.
module Hind.Chan(
   Chan, readChan, writeChan,newChan,isEmptyChan,writeList2Chan, dupChan
  ) where

-- import Control.Concurrent.Chan


import qualified Control.Concurrent.STM.TChan as C
import Control.Concurrent.STM
import Control.Applicative


type Chan = C.TChan


newChan = atomically $ C.newTChan
readChan c = atomically  $ C.readTChan c
writeChan c v = atomically $ C.writeTChan c v
isEmptyChan c = atomically $  C.isEmptyTChan c
dupChan c = atomically $ C.dupTChan c
writeList2Chan c l = mapM_ (writeChan c) l
tryReadChan c = atomically $ do
  t <- C.isEmptyTChan c
  if t
     then return Nothing
     else Just <$> C.readTChan c


