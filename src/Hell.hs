-- | Some additional utilities for the shell.

module Hell where

import System.Directory

-- | Simpler to type alias for 'setCurrentDirectory'. It's one of the
-- few commands that are provided by the shell rather than a real
-- process.
cd :: FilePath -> IO ()
cd = setCurrentDirectory
