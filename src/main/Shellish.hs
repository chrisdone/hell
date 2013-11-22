-- | A sample Hell configuration for the Shellish package.
--
-- Remember to: cabal install shellish

module Main where

import Hell

-- | Main entry point.
main :: IO ()
main = startHell def { configRun = Just (\username pwd -> return "shellish")
                     , configImports = "import Shellish" :
                                       filter (/= "import Hell.Prelude")
                                              (configImports def)
                     }
