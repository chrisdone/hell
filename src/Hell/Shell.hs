{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE CPP #-}

-- | The Hell shell.

module Hell.Shell
  (module Hell.Types
  ,module Data.Default
  ,startHell)
  where

import           Hell.Types

import           Control.Applicative
import           Control.Exception
import           Control.Monad.Reader
import           Control.Monad.Trans
import           Data.Default
import           Data.Dynamic
import           Data.IORef
import           Data.List
import           Data.Maybe
import           Data.Monoid
import qualified Data.Text as T
import           System.Console.Haskeline
import           System.Console.Haskeline.History
import           System.Directory
import           System.FilePath
import           System.Posix.User

import           DynFlags
import           Exception (ExceptionMonad)
import           GHC hiding (History)
import           GHC.Paths hiding (ghc)
import           Name
import           Outputable (Outputable(..),showSDoc)

-- | Go to hell.
startHell :: Config -> IO ()
startHell unreadyConfig =
  do home <- io getHomeDirectory
     let config =
           unreadyConfig { configHistory = reifyHome home (configHistory unreadyConfig) }
     runGhc
       (Just libdir)
       (do dflags <- getSessionDynFlags
           void (setSessionDynFlags
                   (setFlags [Opt_ImplicitPrelude]
                             dflags))
           setImports (configImports config)
           historyRef <- io (readHistory (configHistory config) >>= newIORef)
           username <- io getEffectiveUserName
           candidates <- fmap (map (occNameString . nameOccName))
                              getNamesInScope
           runReaderT (runHell repl)
                      (HellState config historyRef username home candidates))

-- | Read-eval-print loop.
repl :: Hell ()
repl =
  do state <- ask
     config <- asks stateConfig
     welcome <- asks (configWelcome . stateConfig)
     unless (null welcome) (haskeline (outputStrLn welcome))
     loop config state

-- | Do the get-line-and-looping.
loop :: Config -> HellState -> Hell ()
loop config state =
  fix (\again ->
         do (mline,history) <- getLineAndHistory config state
            case mline of
              Nothing -> again
              Just line ->
                do historyRef <- asks stateHistory
                   io (writeIORef historyRef history)
                   result <- ghc (runProducer line)
                   io (writeHistory (configHistory config) history)
                   again)

-- | Get a new line and return it with a new history.
getLineAndHistory :: Config -> HellState -> Hell (Maybe String, History)
getLineAndHistory config state =
  do pwd <- io getCurrentDirectory
     prompt <- prompter (stateUsername state) (stripHome home pwd)
     haskeline (do line <- getInputLine prompt
                   history <- getHistory
                   return (line,history))
  where prompter = configPrompt config
        home = stateHome state

-- | Transform ~/foo to /home/chris/foo.
reifyHome :: FilePath -> String -> FilePath
reifyHome home fp
  | isPrefixOf "~/" fp = home </> drop 2 fp
  | otherwise = fp

-- | Strip and replace /home/chris/blah with ~/blah.
stripHome :: FilePath -> FilePath -> FilePath
stripHome home path
  | isPrefixOf home path = "~/" ++ dropWhile (=='/') (drop (length home) path)
  | otherwise            = path

-- | Import the given modules.
setImports :: [String] -> Ghc ()
setImports =
  mapM (fmap IIDecl . parseImportDecl) >=> setContext

-- | Compile the given expression and evaluate it.
runProducer :: String -> Ghc ()
runProducer stmt =
  do result <- gcatch (fmap Right (dynCompileExpr expr))
                      (\(e::SomeException) -> return (Left e))
     case result of
       Left err ->
         runComplete stmt
       Right compiled ->
         gcatch (io (fromDyn compiled (putStrLn "Bad compile.")))
                (\(e::SomeException) -> liftIO (putStrLn (show e)))
  where expr = "runResourceT (sourceList [] $= " ++ stmt ++ " $$ sinkHandle stdout) :: IO ()"

-- | Compile the given expression and evaluate it.
runComplete :: String -> Ghc ()
runComplete stmt =
  do result <- gcatch (fmap Right (dynCompileExpr expr))
                      (\(e::SomeException) -> return (Left e))
     case result of
       Left err ->
         printType stmt
       Right compiled ->
         gcatch (io (fromDyn compiled (putStrLn "Bad compile.")))
                (\(e::SomeException) -> liftIO (putStrLn (show e)))
  where expr = "runResourceT (sourceList [] $= " ++ stmt ++ ") :: IO ()"

-- | Print the type of the expression.
printType :: String -> Ghc ()
printType stmt =
  do result <- gtry (exprType stmt)
     case result of
       Left err ->
         io (putStrLn (show err))
       Right ty ->
         do d <- getDynFlags
            io (putStrLn (showppr d ty))

-- | Short-hand utility.
io :: MonadIO m => IO a -> m a
io = Control.Monad.Trans.liftIO

-- | Run a Haskeline action in Hell.
haskeline :: InputT IO a -> Hell a
haskeline m =
  do historyRef <- asks stateHistory
     history <- io (readIORef historyRef)
     state <- ask
     io (runInputT (settings state)
                   (do putHistory history
                       m))
  where settings state =
          setComplete (completeFilesAndFunctions (stateFunctions state))
                      defaultSettings

-- | Complete file names or functions in scope.
completeFilesAndFunctions :: [String] -> (String,String) -> IO (String,[Completion])
completeFilesAndFunctions funcs (leftReversed,right) = do
  (fileCandidate,fileResults) <- completeFilename (leftReversed,right)
  return (fileCandidate <|> funcCandidate,map speech fileResults <> funcResults)
  where speech (Completion (normalize -> rep) d fin) = Completion newrep d fin
          where newrep = (if isPrefixOf "\"" rep then rep else "\"" <> rep) <> "\""
        funcResults = mapMaybe (completeFunc (reverse leftReversed)) funcs
        funcCandidate = ""
        normalize = T.unpack . T.replace "\\ " " " . T.pack

-- | Complete a function name.
completeFunc :: String -> String -> Maybe Completion
completeFunc left func =
  if isPrefixOf left func
     then Just (Completion func func True)
     else Nothing

-- | Run a GHC action in Hell.
ghc :: Ghc a -> Hell a
ghc m = Hell (ReaderT (const m))

-- | Set the given flags.
setFlags :: [ExtensionFlag] -> DynFlags -> DynFlags
setFlags xs dflags = foldl xopt_set dflags xs

-- | Something like Show but for things which annoyingly do not have
-- Show but Outputable instead.
showppr :: Outputable a => DynFlags -> a -> String
showppr d = showSDoc d . ppr

-- | Try the thing or return the exception.
gtry :: (Functor m, ExceptionMonad m) => m a -> m (Either SomeException a)
gtry m =
  gcatch (fmap Right m)
         (\(e::SomeException) ->
            return (Left e))
