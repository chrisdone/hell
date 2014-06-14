{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

-- | Exports a symbol for all binaries in PATH.

module Hell.Bin where

import Hell.TH

generateBinaries
