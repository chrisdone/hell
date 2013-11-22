-- | A sample Hell configuration for the Shelly package.
--
-- Remember to: cabal install shelly

module Main where

import Hell

-- | Main entry point.
main :: IO ()
main = startHell def { configRun = Just "(\\m -> do p <- getCurrentDirectory;\
                                        \(v,p) <- shellyNoDir (do cd (fromText (T.pack p));\
                                        \v <- m;\
                                        \p <- pwd;\
                                        \return (v,p));\
                                        \setCurrentDirectory (T.unpack (toTextIgnore p));\
                                        \return v)"
                     , configImports = "import Shelly" :  "import qualified Data.Text as T" :
                                       filter (/= "import Hell.Prelude")
                                              (configImports def)
                     }
