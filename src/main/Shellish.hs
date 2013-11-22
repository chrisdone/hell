-- | A sample Hell configuration for the Shellish package.
--
-- Remember to: cabal install shellish

module Main where

import Hell

-- | Main entry point.
main :: IO ()
main = startHell def { configRun = Just "(\\m -> do p <- getCurrentDirectory; (v,p) <- shellish (do cd p; v <- m; p <- pwd; return (v,p)); setCurrentDirectory p;return v)"
                     , configImports = "import Shellish" :
                                       filter (/= "import Hell.Prelude")
                                              (configImports def)
                     }
