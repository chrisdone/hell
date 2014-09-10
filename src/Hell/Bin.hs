{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

-- | Exports a symbol for all binaries in PATH.

module Hell.Bin where

import Hell.TH

generateBinaries
