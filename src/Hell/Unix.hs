{-# LANGUAGE FlexibleInstances #-}
-- | A set of utilities that are named similarly and behave similarly
-- to the UNIX way of doing shells.

module Hell.Unix where

import System.Directory
import Data.List

-- | List directory contents.
class Ls a where
  ls :: a

-- | Get directory contents.
instance Ls (FilePath -> IO [FilePath]) where
  ls x = fmap sort (getDirectoryContents x)

-- | Get current directory contents.
instance Ls (IO [FilePath]) where
  ls = getCurrentDirectory >>= ls

-- | List the given directory.
instance Ls (FilePath -> IO String) where
  ls x = ls x >>= mapM_ putStrLn >> return ""

-- | List the current directory.
instance Ls (IO String) where
  ls = do pwd <- getCurrentDirectory
          ls pwd

-- | Set current directory.
class Cd a where
  cd :: a

-- | Switch to given directory.
instance Cd (FilePath -> IO String) where
  cd x = setCurrentDirectory x >> return ""

-- | Switch to home directory.
instance Cd (IO String) where
  cd = getHomeDirectory >>= putStrLn >> return ""

-- | Print the present working directory.
pwd :: IO ()
pwd = getCurrentDirectory >>= putStrLn
