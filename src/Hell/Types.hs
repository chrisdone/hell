module Hell.Types where

import Data.Default
import GhcMonad

-- | Shell config.
data Config = Config
  { configImports :: ![String]
  , configWelcome :: String
  , configPrompt  :: String -> FilePath -> Ghc String
  }

instance Default Config where
  def = Config
    { configImports =
        map ("import "++)
            ["Prelude"
             ,"GHC.Types"
             ,"System.IO"
             ,"Data.List"
             ,"Control.Monad"
             ,"Control.Monad.Fix"
             ,"System.Directory"
             ,"System.Process"
             ,"System.Environment"
             ,"Hell.Prelude"]
    , configWelcome = "Welcome to Hell!"
    , configPrompt = \username pwd -> return (username ++ ":" ++ pwd ++ "$ ")
    }
