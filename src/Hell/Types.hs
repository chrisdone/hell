{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}

module Hell.Types where

import Control.Applicative
import Control.Monad.Reader

import Data.Default
import Data.IORef
import GhcMonad

import System.Console.Haskeline.History

-- | Shell config.
data Config = Config
  { configImports :: ![String] -- ^ Starting imports.
  , configWelcome :: String -- ^ A welcome string.
  , configHistory :: FilePath
  , configPrompt  :: String -> FilePath -> Hell String -- ^ An action to generate the prompt.
  }

-- | State of the shell.
data HellState = HellState
  { stateConfig    :: !Config
  , stateHistory   :: !(IORef History)
  , stateUsername  :: !String
  , stateHome      :: !FilePath
  , stateFunctions :: ![String]
  }

-- | Hell monad, containing user information and things like that.
newtype Hell a =
  Hell {runHell :: ReaderT HellState Ghc a}
  deriving (Functor,Applicative,Monad,MonadIO,MonadReader HellState)

instance Default Config where
  def =
    Config {configImports =
              ["import Prelude"
              ,"import Data.List"
              ,"import Data.Ord"
              ,"import Data.Conduit.Shell"
              ,"import System.Directory"
              ,"import Data.Conduit"
              ,"import qualified Data.Conduit.List as CL"
              ,"import Data.Bifunctor"
              ,"import qualified Data.Conduit.Binary as CB"
              ,"import qualified Data.ByteString.Char8 as S8"
              ,"import Control.Monad"
              ,"import Data.Function"
              ,"import Hell"]
           ,configWelcome = "Welcome to Hell!"
           ,configPrompt =
              \username pwd ->
                return (username ++ ":" ++ pwd ++ "$ ")
           ,configHistory = "~/.hell-history"}

-- | Hopefully this shouldn't be a problem because while this is a
-- library it has a very narrow use-case.

#if __GLASGOW_HASKELL__ == 706
instance MonadIO Ghc where
  liftIO = GhcMonad.liftIO
#endif
