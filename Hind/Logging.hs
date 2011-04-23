module Hind.Logging (
  setupLogger,
  module System.Log.Logger
                    ) where


import Hind.Options(logLevel)
import System.Log.Logger
import System.Log.Handler(setFormatter,close)
import System.Log.Handler.Simple
import System.Log.Formatter
import System.IO
import Text.Read
import Control.Monad(unless)

setupLogger fname options = do
      -- Set up the logger
      oh <- do lh <- streamHandler stdout DEBUG
               return $ setFormatter lh $
                        (simpleLogFormatter "[$loggername: $prio] $msg")

      h <- do lh <- fileHandler fname DEBUG
              return $  setFormatter lh $
                       (simpleLogFormatter "[$loggername : $prio] $msg")

      updateGlobalLogger rootLoggerName (setHandlers ([] :: [GenericHandler ()]))


      updateGlobalLogger rootLoggerName (addHandler h)
      updateGlobalLogger rootLoggerName (addHandler oh)
      -- By default, all NOTICEs will be logged
      updateGlobalLogger rootLoggerName (setLevel NOTICE)
      mapM_ updateLogger $ splitLogLevel (logLevel options)


updateLogger (LogComponent name p) = updateGlobalLogger name (setLevel p)

data LogLevel = LogComponent String Priority  deriving (Show)

instance Read LogLevel where
  readPrec = do name <- readName
                Punc "=" <- lexP
                level <- step readPrec
                return (LogComponent name level)
    where readName = do
              Ident ident <- lexP
              rest <- (do Symbol "." <- lexP
                          nm <- readName
                          return ('.':nm)
                      +++ return "")
              return (ident ++ rest)


  readListPrec = do
    i <- step readPrec
    is <- (do Punc "," <- lexP
              readListPrec
           +++
           (return []))
    return (i:is)


-- Process a loglevel argument string to a list of log levels
splitLogLevel :: String -> [LogLevel]
splitLogLevel = read

