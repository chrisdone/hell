-- | Handy module for writing scripts.

module Hell
  (module Hell)
  where

import Hell.Bin as Hell

import Control.Monad.Fix as Hell
import Control.Monad.IO.Class as Hell
import Control.Monad.Trans.Resource as Hell
import Data.Conduit as Hell
import Data.Conduit.List as Hell (sourceList)
import Data.Conduit.Binary as Hell hiding (mapM_)
import Data.Conduit.Process as Hell
import Prelude as Hell hiding (mapM,mapM_,lines,takeWhile,take,drop,dropWhile,head)
import System.Directory as Hell
import System.Environment as Hell
import System.IO as Hell
import System.Process as Hell
