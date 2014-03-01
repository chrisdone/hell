{-# LANGUAGE FlexibleInstances #-}
-- | A set of utilities that are named similarly and behave similarly
-- to the UNIX way of doing shells.

module Hell.Unix where

import Control.Monad
import Data.List
import System.Directory

-- | R parameter.
data R = R

-- | List directory contents.
class Ls a where
  ls :: a

-- | Print recursive directory contents.
instance Ls (R -> IO String) where
  ls R =
    getCurrentDirectory >>= ls R

-- | Print the given directory recursively.
instance Ls (R -> FilePath -> IO String) where
  ls R x =
    do xs <- ls x
       forM_ (filter (not . all (=='.')) xs)
             (\x ->
                do putStrLn x
                   isDir <- doesDirectoryExist x
                   when isDir
                        (do "" <- ls R x
                            return ()))
       return ""

-- | Get directory contents.
instance Ls (FilePath -> IO [FilePath]) where
  ls x =
    fmap sort (getDirectoryContents x)

-- | Get current directory contents.
instance Ls (IO [FilePath]) where
  ls =
    getCurrentDirectory >>= ls

-- | List the given directory.
instance Ls (FilePath -> IO String) where
  ls x =
    ls x >>= mapM_ putStrLn >> return ""

-- | List the current directory.
instance Ls (IO String) where
  ls =
    do pwd <- getCurrentDirectory
       ls pwd

-- | Set current directory.
class Cd a where
  cd :: a

-- | Switch to given directory.
instance Cd (FilePath -> IO String) where
  cd x =
    setCurrentDirectory x >> return ""

-- | Switch to home directory.
instance Cd (IO String) where
  cd =
    getHomeDirectory >>= setCurrentDirectory >> return ""

-- | Print the present working directory.
pwd :: IO ()
pwd = getCurrentDirectory >>= putStrLn

-- | Remove given file.
class Rm a where
  rm :: a

instance Rm (FilePath -> IO String) where
  rm x =
    removeFile x >> return ""

instance Rm (R -> FilePath -> IO String) where
  rm R x
    = removeDirectoryRecursive x >> return ""

-- | Remove given file.
rmdir :: FilePath -> IO ()
rmdir = removeDirectory
