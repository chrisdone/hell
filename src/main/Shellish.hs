-- | A sample Hell configuration for the Shellish package.
--
-- Remember to: cabal install shelly

module Main where

import Hell

-- | Main entry point.
main :: IO ()
main = startHell def { configRun = Just (\username pwd -> return "shelly")
                     , configImports = "import Shelly" :
                                       filter (/= "import Hell.Prelude")
                                              (configImports def)
                     }
