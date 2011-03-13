module Hind.Logging (
  setupLogger,
  module System.Log.Logger

                    ) where



import System.Log.Logger
import System.Log.Handler(setFormatter,close)
import System.Log.Handler.Simple
import System.Log.Formatter
import System.IO

setupLogger fname level = do
      -- Set up the logger
      oh <- do lh <- streamHandler stdout NOTICE
               return $ setFormatter lh $
                        (simpleLogFormatter "[$loggername : $prio] $msg")

      h <- do lh <- fileHandler (fname ++ ".log") (read level)
              return $  setFormatter lh $
                       (simpleLogFormatter "[$loggername : $prio] $msg")
                       -- (simpleLogFormatter "[$time : $loggername : $prio] $msg")

      updateGlobalLogger rootLoggerName (setHandlers ([] :: [GenericHandler ()]))

      updateGlobalLogger rootLoggerName (addHandler oh)
      updateGlobalLogger "Hind" (addHandler h)
      updateGlobalLogger "Hind" (setLevel (read level))
