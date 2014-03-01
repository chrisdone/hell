-- | A set of utilities that are named similarly and behave similarly
-- to the UNIX way of doing shells.

module Hell.Unix where

import Control.Monad.IO.Class
import System.Directory

-- | Change the current directory.
cd :: MonadIO m => FilePath -> m ()
cd = liftIO . setCurrentDirectory
